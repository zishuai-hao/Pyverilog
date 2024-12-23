import copy

from pyverilog.dataflow.dataflow import DataFlow, DFConcat, DFPointer, DFPartselect, DFOperator, DFBranch, DFTerminal, \
    DFUndefined, DFHighImpedance, DFConstant, DFEvalValue
from pyverilog.dataflow.optimizer import VerilogOptimizer
from pyverilog.dataflow.visit import Labels, FrameTable
import re
import sys
from loguru import logger
from pyverilog.utils import verror
from pyverilog.utils.scope import ScopeChain, scopetype_list_unprint, ScopeLabel

format = "{time:YYYY-MM-DD at HH:mm:ss} | {level} | {message} | {name}:{function}:{line}"
logger.remove()
logger.add(sys.stdout, level='DEBUG', format=format)
logger.add('output.log', level='DEBUG', format=format)


def compare_dict_values(dict1, dict2):
    differing_keys = {}

    for key in dict1.keys() & dict2.keys():  # 只遍历两个字典都有的键
        if dict1[key] != dict2[key]:  # 如果值不相等
            differing_keys[key] = (dict1[key], dict2[key])  # 存储不同的键及其值

    return differing_keys


class ModuleStatus:
    def __init__(self, instance_scope, frames, dataflow, optimizer, is_leaf=False):
        self.instance_scope = instance_scope
        self.frames: FrameTable = frames
        self.dataflow: DataFlow = dataflow
        self.optimizer: VerilogOptimizer = optimizer
        # 这里要考虑当前的 current 以及后面会不会修改这些
        self.frames_cache = {}
        self.always_cache = {}
        self.nb_assign_cache = {}
        self.block_assign_cache = {}
        self.labels_addition = {}
        self.labels_cache = {}  # 缓存进入模块的label，便于后面计算
        self.is_leaf = True

    @staticmethod
    def of(scope, frames, labels, dataflow, optimizer):
        df = DataFlow()
        df.terms = copy.deepcopy(dataflow.terms)
        df.binddict = copy.copy(dataflow.binddict)
        df.functions = copy.deepcopy(dataflow.functions)
        df.function_ports = copy.deepcopy(dataflow.function_ports)
        df.tasks = copy.deepcopy(dataflow.tasks)
        df.task_ports = copy.deepcopy(dataflow.task_ports)
        df.temporal_value = copy.deepcopy(dataflow.temporal_value)
        return ModuleStatus(
            scope,
            copy.deepcopy(frames),
            copy.deepcopy(labels),
            df,
            copy.deepcopy(optimizer))

    def compare(self, __value):
        return (
                self.labels.labels == __value.labels.labels and
                self.dataflow.terms == __value.dataflow.terms and
                self.dataflow.binddict == __value.dataflow.binddict and
                self.optimizer.terms == __value.optimizer.terms and
                self.optimizer.constlist == __value.optimizer.terms.constlist
        )

    def compare_exists_keys(self, other):
        frames_dict = compare_dict_values(self.frames.dict, other.frames.dict)
        logger.info(f"frames.dict:{len(frames_dict.items())}")

        logger.info(f"dataflow.terms:{compare_dict_values(self.dataflow.terms, other.dataflow.terms)}")
        logger.info(f"dataflow.binddict:{compare_dict_values(self.dataflow.binddict, other.dataflow.binddict)}")
        optimizer_terms = compare_dict_values(self.optimizer.terms, other.optimizer.terms)
        logger.info(f"optimizer.terms:{len(optimizer_terms.items())}")
        optimizer_constlist = compare_dict_values(self.optimizer.constlist, other.optimizer.constlist)
        logger.info(f"optimizer.constlist:{len(optimizer_constlist.items())}")


class ModuleCache:
    def __init__(self):
        self.module_info_dict: dict[str: ModuleStatus] = {}
        self.current: ModuleStatus = None

    def getCurrent(self):
        return self.current

    def addModuleInfo(self, module_name, module_status):
        if not self.hasModuleInfo(module_name):
            for item in self.module_info_dict.items():
                (key, value) = item
                pre_name = value.instance_scope.__repr__()
                cur_name = module_status.instance_scope.__repr__()
                if cur_name.startswith(pre_name):
                    value.is_leaf = False
            self.module_info_dict[module_name] = module_status
            self.current = self.module_info_dict[module_name]
            return True
        return False

    def hasModuleInfo(self, module_name):
        return module_name in self.module_info_dict

    def check_leaf(self, module_name):
        if self.hasModuleInfo(module_name):
            return self.getModuleInfo(module_name).is_leaf
        return False
    def getModuleInfo(self, module_name) -> ModuleStatus:
        return self.module_info_dict[module_name]

    def setTerm(self, name, term):
        self.current.dataflow.addTerm(name, term)

    def setConst(self, name, value):
        if (value == None):
            self.current.optimizer.resetConstant(name)
            return
        self.current.optimizer.setConstant(name, value)

    def setConstTerm(self, name, value):
        self.current.optimizer.setTerm(name, value)

    def addBind(self, name, bind):
        self.current.dataflow.addBind(name, bind)

    def addFrame(self, scope, frame):
        self.current.frames_cache[scope] = frame

    def addAlawaysInfo(self, scope, always_info):
        self.current.always_cache[scope] = always_info

    def addNonblockingAssign(self, name, non_blocking_assign, scope):
        # self.current.nb_assign_cache[name] = non_blocking_assign
        if scope in self.current.nb_assign_cache:
            self.current.nb_assign_cache[scope][name] = non_blocking_assign
        else:
            self.current.nb_assign_cache[scope] = {name: non_blocking_assign}

    def addBlockingAssign(self, name, blocking_assign, scope):
        if scope in self.current.block_assign_cache:
            self.current.block_assign_cache[scope][name] = blocking_assign
        else:
            self.current.block_assign_cache[scope] = {name: blocking_assign}

    def __contains__(self, item):
        return self.hasModuleInfo(item)


def update_trailing_number(scopename, labels, labels_cache):
    patten = "([a-zA-Z_]*)(\d*)"

    def replacement(match):
        variable = match.group(1)
        if variable in labels.labels:
            num = match.group(2)
            # 计算公式：模块标签的相对序号差值=标签本身的序号-初始序号，在加上当前的序号就可以计算出最终序号
            return variable + str(
                int(num) - (labels_cache[variable].cnt if variable in labels_cache else 0) + labels.labels[
                    variable].cnt)
        return match.group(0)

    return re.sub(patten, replacement, scopename)


def update_scope(scope, old_scope, current_scope, labels, labels_cache):
    """
        处理标签尾部的序号
    :param scope: 需要处理的scope
    :param old_scope: 以前实例的 scope
    :param current_scope: 当前实例的 scope
    :param labels: 当前标签尾部的序号
    :return:
    """
    # 1. 更新模块的scope
    scope = scope.replace(old_scope, current_scope)

    # # 2. 更新 label 的序号
    # sub_length = len(current_scope)
    # flag = False
    # result = []
    # i = 0
    # scope_chain = scope.scopechain
    # while i < len(scope_chain):
    #     if flag:
    #         scope = scope_chain[i]
    #         # 跳过不需要处理的类型
    #         if scope.scopetype not in scopetype_list_unprint:
    #             i += 1
    #             result.append(scope)  # 保留当前元素
    #             continue
    #         scopename = scope.scopename
    #         # if scopename.endswith("_ELSE"):
    #         #     scopename = scopename.replace("_ELSE", "")
    #         #     scopename = update_trailing_number(scopename, labels, labels_cache) + "_ELSE"
    #         #
    #         # else:
    #         #     scopename = update_trailing_number(scopename, labels, labels_cache)
    #         result.append(ScopeLabel(scopename, scope.scopetype, scope.scopeloop))  # 保留当前元素
    #         i += 1
    #         continue
    #     # 检查是否找到子数组
    #     if scope[i:i + sub_length] == current_scope:
    #         result.extend(current_scope)  # 替换为另一个数组
    #         i += sub_length  # 跳过子数组的长度
    #         flag = True
    #     else:
    #         result.append(scope_chain[i])  # 保留当前元素
    #         i += 1

    # return ScopeChain(result)

    return scope

def process_tree(tree, visited, step=1, delay=False, msb=None, lsb=None, ptr=None, instance_scope=None, current_scope=None, labels=None, labels_cache=None):
    if tree is None:
        return None

    if isinstance(tree, DFUndefined):
        return tree

    if isinstance(tree, DFHighImpedance):
        return tree

    if isinstance(tree, DFConstant):
        return tree

    if isinstance(tree, DFEvalValue):
        return tree

    if isinstance(tree, DFTerminal):
        tree.name = update_scope(tree.name, instance_scope, current_scope, labels, labels_cache)
        return tree

    if isinstance(tree, DFBranch):
        condnode = process_tree(tree.condnode, visited, step, delay, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache)
        truenode = process_tree(tree.truenode, visited, step, delay, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache)
        falsenode = process_tree(tree.falsenode, visited, step, delay, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache)
        return DFBranch(condnode, truenode, falsenode)

    if isinstance(tree, DFOperator):
        nextnodes = []
        for n in tree.nextnodes:
            nextnodes.append(process_tree(n, visited, step, delay, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache))
        return DFOperator(tuple(nextnodes), tree.operator)

    if isinstance(tree, DFPartselect):
        msb = process_tree(tree.msb, visited, step, delay, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache)
        lsb = process_tree(tree.lsb, visited, step, delay, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache)
        var = process_tree(tree.var, visited, step, delay, msb=msb, lsb=lsb, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache)
        # if isinstance(var, DFPartselect):
        #     child_lsb = self.getTerm(str(tree.var)).lsb.eval()
        #     return DFPartselect(var.var, DFIntConst(str(msb.eval() + var.lsb.eval() - child_lsb)),
        #                         DFIntConst(str(lsb.eval() + var.lsb.eval() - child_lsb)))
        return DFPartselect(var, msb, lsb)

    if isinstance(tree, DFPointer):
        ptr = process_tree(tree.ptr, visited, step, delay, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache)
        var = process_tree(tree.var, visited, step, delay, ptr=ptr, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache)
        # if isinstance(tree.var, DFTerminal):
        #     if (self.getTermDims(tree.var.name) is not None and
        #             not (isinstance(var, DFTerminal) and var.name == tree.var.name)):
        #         return var
        return DFPointer(var, ptr)

    if isinstance(tree, DFConcat):
        nextnodes = []
        for n in tree.nextnodes:
            nextnodes.append(process_tree(n, visited, step, delay, instance_scope=instance_scope, current_scope=current_scope, labels=labels, labels_cache=labels_cache))
        return DFConcat(tuple(nextnodes))

    raise verror.DefinitionError(
        'Undefined Node Type: %s : %s' % (str(type(tree)), str(tree)))
