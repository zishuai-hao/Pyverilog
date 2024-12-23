# -------------------------------------------------------------------------------
# bindvisitor.py
#
# Binding visitor
#
# Copyright (C) 2013, Shinya Takamaeda-Yamazaki
# License: Apache 2.0
# Contributor: ryosuke fukatani
# -------------------------------------------------------------------------------

from __future__ import absolute_import
from __future__ import print_function

import concurrent.futures
import time
from functools import wraps

import pyverilog.dataflow.reorder as reorder
import pyverilog.dataflow.replace as replace
from pyverilog.dataflow.cache import *
from pyverilog.dataflow.dataflow import *
from pyverilog.dataflow.visit import *

format = "{time:YYYY-MM-DD at HH:mm:ss} | {level} | {message} | {name}:{function}:{line}"
logger.remove()
logger.add(sys.stdout, level='DEBUG', format=format)
logger.add('output.log', level='DEBUG', format=format)


def get_time_ms(message: None):
    def get_time(f):
        @wraps(f)
        def inner(*arg, **kwarg):
            s_time = time.time()
            res = f(*arg, **kwarg)
            e_time = time.time()
            logger.debug(f'{message}耗时：{e_time - s_time}秒')
            return res

        return inner

    return get_time


executor = concurrent.futures.ThreadPoolExecutor(max_workers=10)


class BindVisitor(NodeVisitor):
    def __init__(self, moduleinfotable, top, frames: FrameTable, noreorder=False, use_cache=False):
        self.moduleinfotable = moduleinfotable
        self.top = top
        self.frames = frames
        self.labels = Labels()
        self.dataflow = DataFlow()
        self.optimizer = VerilogOptimizer({}, {})

        self.noreorder = noreorder

        # set the top frame of top module
        self.frames.setCurrent(ScopeChain())
        self.stackInstanceFrame(top, top)

        self.copyAllFrameInfo()  # 这一步主要是将所有信号和常量加入数据流符号表

        current = self.frames.getCurrent()
        self.copyFrameInfo(current)  # 没有常量啥也没干

        self.renamecnt = 0
        self.default_nettype = 'wire'
        self.DFTree_cache = dict()
        self.module_cache = ModuleCache()

        self.always_feature_map = []
        self.use_cache = use_cache

    def getDataflows(self):
        return self.dataflow

    def getFrameTable(self):
        return self.frames

    def start_visit(self):
        return self.visit(self.moduleinfotable.getDefinition(self.top))

    def fast_module_visit(self, module_node):
        """
            需要将该模块所引用到的信号名，scope都追加上去
            处理数据流，主要包括instance信号的关联，  这个关联是由当前层传递到下级模块
            当前问题，处理完嵌套模块后，父模块没有信息
        """
        # 存储处理后的alwaysinfo
        current_scope = self.frames.getCurrent()
        # rcurrent_scope = current_scope[-1]
        module_status = self.module_cache.getModuleInfo(module_node.name)
        instance_scope = module_status.instance_scope
        # 存储处理后的alwaysinfo
        after_process_alaways_info_dict = {}

        def process_bind(bind):
            bind = copy.copy(bind)
            bind.dest = update_scope(bind.dest, instance_scope, current_scope, self.labels, module_status.labels_cache)
            if bind.alwaysinfo:
                bind.alwaysinfo = after_process_alaways_info_dict[bind.alwaysinfo.alwaysScope]
            # value.ptr = copy.deepcopy(value.ptr) # TODO 不理解这个 ptr
            bind.tree = process_tree(copy.deepcopy(bind.tree), visited=set(),
                                     instance_scope=instance_scope, current_scope=current_scope, labels=self.labels,
                                     labels_cache=module_status.labels_cache)

            # bind.tree = copy.deepcopy(value.tree)
            return bind

        # rinstance_scope = module_status.instance_scope[-1]
        # 1. 处理frames:sframe always, nb assign, blockassign
        for item in module_status.frames_cache.items():
            raise NotImplementedError
        for item in self.frames.dict.items():
            (scope, _) = item
            if scope.find(instance_scope):
                new_scope = scope.replace(instance_scope, current_scope)
                if (new_scope not in self.frames.dict):
                    continue
                self.frames.dict[new_scope].probability = self.frames.dict[scope].probability



        # always_info
        for item in module_status.always_cache.items():
            (key, value) = item
            value = copy.copy(value)
            key = update_scope(key, instance_scope, current_scope, self.labels, module_status.labels_cache)

            if value.clock_name != None:
                old_clock_name = value.clock_name
                value.clock_name = update_scope(value.clock_name, instance_scope, current_scope,
                                                self.labels, module_status.labels_cache)
                self.always_feature_map.append(f'{value.clock_name}')
            if (value.reset_name != None):
                old_reset_name = value.reset_name
                value.reset_name = update_scope(value.reset_name, instance_scope, current_scope,
                                                self.labels, module_status.labels_cache)

                self.always_feature_map.append(f'{value.reset_name}')
            self.always_feature_map.append(f'{value.clock_name}')
            if len(value.senslist) > 0:
                for sens in value.senslist:
                    if isinstance(sens.sig, Pointer):
                        sens_name = f"{current_scope.__repr__()} .{sens.sig.var}[{sens.sig.ptr}]"
                    else:
                        sens_name = f"{current_scope.__repr__()} .{sens.sig.name}"
                    self.always_feature_map.append(sens_name)
            self.frames.dict[key].alawaysinfo = value
            after_process_alaways_info_dict[value.alwaysScope] = value

        for item in module_status.nb_assign_cache.items():
            (key, assigns) = item
            assigns = copy.copy(assigns)
            key = update_scope(key, instance_scope, current_scope, self.labels, module_status.labels_cache)
            for assign in assigns.items():
                (scope, value) = assign
                scope = update_scope(scope, instance_scope, current_scope, self.labels, module_status.labels_cache)
                value = process_bind(value)
                self.frames.dict[key].addNonblockingAssign(scope, value)

        for item in module_status.block_assign_cache.items():
            (key, assigns) = item
            assigns = copy.copy(assigns)
            key = update_scope(key, instance_scope, current_scope, self.labels, module_status.labels_cache)
            for assign in assigns.items():
                (scope, value) = assign
                scope = update_scope(scope, instance_scope, current_scope, self.labels, module_status.labels_cache)
                value = process_bind(value)
                self.frames.dict[key].setBlockingAssign(scope, value)

        # 2. 处理dataflow bind 使用自带的函数，可以自动merge
        for item in module_status.dataflow.binddict.items():
            (key, binds) = item
            key = update_scope(key, instance_scope, current_scope, self.labels, module_status.labels_cache)
            for bind in binds:
                self.dataflow.addBind(key, process_bind(bind))
        for item in module_status.dataflow.terms.items():
            (name, term) = item
            name = update_scope(name, instance_scope, current_scope, self.labels, module_status.labels_cache)
            term = copy.copy(term)
            term.name = update_scope(term.name, instance_scope, current_scope, self.labels, module_status.labels_cache)
            self.dataflow.addTerm(name, term)
        # 3. 处理optimizer
        for item in module_status.optimizer.constlist.items():
            raise NotImplementedError
            (name, const) = item
            self.optimizer.setConstant(
                update_scope(name, instance_scope, current_scope, self.labels, module_status.labels_cache),
                None)
        for item in module_status.optimizer.terms.items():
            (name, term) = item
            name = update_scope(name, instance_scope, current_scope, self.labels, module_status.labels_cache)
            term = copy.copy(term)
            term.name = update_scope(term.name, instance_scope, current_scope, self.labels, module_status.labels_cache)
            self.optimizer.setTerm(name, term)

    def visit_ModuleDef(self, node):
        # if self.use_cache and self.module_cache.hasModuleInfo(node.name) and self.module_cache.check_leaf(node.name) :
        if self.use_cache and self.module_cache.hasModuleInfo(node.name):
            return self.fast_module_visit(node)
        is_leaf = True
        for item in node.items:
            if isinstance(item, (InstanceList, Instance)):
                is_leaf = False
        self.module_cache.addModuleInfo(node.name, ModuleStatus(self.frames.getCurrent(), FrameTable(), DataFlow(),
                                                                VerilogOptimizer({}, {}), is_leaf=is_leaf))
        logger.info(f"遍历模块 {node.name}")
        # cached = ModuleStatus.of(None,self.frames,  self.labels, self.dataflow, self.optimizer)
        # cached_labels = copy.deepcopy(self.labels.labels)

        self.default_nettype = node.default_nettype
        self.generic_visit(node)

        logger.info(f"遍历模块结束 {node.name}")
        # now = ModuleStatus.of(None,self.frames, self.labels, self.dataflow, self.optimizer)
        # cached.compare_exists_keys(now)

        # # 处理完该模块后，读取模块的
        # labels_addition = Labels()
        # for item in self.labels.labels.items():
        #     (key, value) = copy.deepcopy(item)
        #     if key in cached_labels:
        #         value.cnt = value.cnt - cached_labels[key].cnt
        #     labels_addition.labels[key] = value
        # self.module_cache.current.labels_addition = labels_addition
        # self.module_cache.current.labels_cache = cached_labels

    def visit_Input(self, node):
        self.addTerm(node)

    def visit_Output(self, node):
        self.addTerm(node)

    def visit_Inout(self, node):
        self.addTerm(node)

    def visit_Reg(self, node):
        self.addTerm(node)

    def visit_Wire(self, node):
        self.addTerm(node)

    def visit_Tri(self, node):
        self.addTerm(node)

    def visit_Integer(self, node):
        self.addTerm(node)

    def visit_Parameter(self, node):
        self.addTerm(node)
        current = self.frames.getCurrent()
        name = current + ScopeLabel(node.name, 'signal')
        if not self.hasConstant(name):
            value = self.optimize(self.getTree(node.value, current))
            self.setConstant(name, value)

        if len(self.dataflow.getBindlist(name)) == 0:
            self.addBind(node.name, node.value, bindtype='parameter')

    def visit_Supply(self, node):
        self.addTerm(node)
        current = self.frames.getCurrent()
        name = current + ScopeLabel(node.name, 'signal')
        self.addBind(node.name, node.value, bindtype='parameter')

    def visit_Localparam(self, node):
        self.addTerm(node)
        current = self.frames.getCurrent()
        name = current + ScopeLabel(node.name, 'signal')
        if not self.hasConstant(name):
            value = self.optimize(self.getTree(node.value, current))
            self.setConstant(name, value)

        self.addBind(node.name, node.value, bindtype='localparam')

    def visit_Genvar(self, node):
        self.addTerm(node)
        current = self.frames.getCurrent()
        name = self.frames.getCurrent() + ScopeLabel(node.name, 'signal')
        value = DFEvalValue(0)
        self.setConstant(name, value)

    def visit_Function(self, node):
        self.frames.setFunctionDef()
        self.generic_visit(node)
        self.frames.unsetFunctionDef()

    def visit_Task(self, node):
        self.frames.setTaskDef()
        self.generic_visit(node)
        self.frames.unsetTaskDef()

    def visit_InstanceList(self, node):
        for i in node.instances:
            self.visit(i)

    def visit_Instance(self, node):
        if node.array:
            return self._visit_Instance_array(node)
        nodename = node.name
        return self._visit_Instance_body(node, nodename)

    def _visit_Instance_array(self, node):
        if node.name == '':
            raise verror.FormatError("Module %s requires an instance name" % node.module)

        current = self.frames.getCurrent()
        msb = self.optimize(self.getTree(node.array.msb, current)).value
        lsb = self.optimize(self.getTree(node.array.lsb, current)).value
        num_of_pins = msb + 1 - lsb

        for i in range(lsb, msb + 1):
            nodename = node.name + '_' + str(i)
            self._visit_Instance_body(node, nodename, arrayindex=i)

    @get_time_ms(message="instance")
    def _visit_Instance_body(self, node, nodename, arrayindex=None):
        if node.module in primitives:
            return self._visit_Instance_primitive(node, arrayindex)

        if nodename == '':
            raise verror.FormatError("Module %s requires an instance name" % node.module)
        # 重置 labels
        self.labels = Labels()

        current = self.stackInstanceFrame(nodename, node.module)

        scope = self.frames.getCurrent()

        paramnames = self.moduleinfotable.getParamNames(node.module)
        for paramnames_i, param in enumerate(node.parameterlist):
            self.addInstanceParameterBind(param, paramnames[paramnames_i])
            value = self.optimize(self.getTree(param.argname, current))
            paramname = paramnames[paramnames_i] if param.paramname is None else param.paramname
            if paramname not in paramnames:
                raise verror.FormatError("No such parameter: %s in %s" %
                                         (paramname, nodename))
            name = scope + ScopeLabel(paramname, 'signal')
            self.setConstant(name, value)
            definition = Parameter(paramname, str(value.value))
            term = self.makeConstantTerm(name, definition, current)
            self.setConstantTerm(name, term)

        ioports = self.moduleinfotable.getIOPorts(node.module)
        for ioport_i, port in enumerate(node.portlist):
            if port.portname is not None and not (port.portname in ioports):
                raise verror.FormatError("No such port: %s in %s" %
                                         (port.argname.name, nodename))
            self.addInstancePortBind(port, ioports[ioport_i], arrayindex)  # 将实例的输入端口绑定到数据流图中

        new_current = self.frames.getCurrent()
        self.copyFrameInfo(new_current)

        self.visit(self.moduleinfotable.getDefinition(node.module))
        self.frames.setCurrent(current)

    def _visit_Instance_primitive(self, node, arrayindex=None):
        # 没有执行到这里
        primitive_type = primitives[node.module]
        left = node.portlist[0].argname
        if arrayindex is not None:
            left = Pointer(left, IntConst(str(arrayindex)))
        right = None
        if primitive_type == None:
            right = (Pointer(node.portlist[1].argname, IntConst('0')) if arrayindex is None else
                     Pointer(node.portlist[1].argname, IntConst(str(arrayindex))))
        elif primitive_type == Unot:
            right = (Ulnot(Pointer(node.portlist[1].argname, IntConst('0'))) if arrayindex is None else
                     Ulnot(Pointer(node.portlist[1].argname, IntConst(str(arrayindex)))))
        else:
            concat_list = ([Pointer(p.argname, IntConst('0')) for p in node.portlist[1:]] if arrayindex is None else
                           [Pointer(p.argname, IntConst(str(arrayindex))) for p in node.portlist[1:]])
            right = primitive_type(Concat(concat_list))
        self.addBind(left, right, bindtype='assign')

    def visit_Initial(self, node):
        pass
        # label = self.labels.get( self.frames.getLabelKey('initial') )
        # current = self.stackNextFrame(label, 'initial',
        #                              generate=self.frames.isGenerate(),
        #                              initial=True)
        # self.generic_visit(node)
        # self.frames.setCurrent(current)

    def visit_Always(self, node):
        label = self.labels.get(self.frames.getLabelKey('always'))
        current = self.stackNextFrame(label, 'always',
                                      generate=self.frames.isGenerate(),
                                      always=True, probability=self.frames.getProbability())

        (clock_name, clock_edge, clock_bit,
         reset_name, reset_edge, reset_bit,
         senslist) = self._createAlwaysinfo(node, current)
        self.always_feature_map.append(clock_name.__repr__())
        if reset_name:
            self.always_feature_map.append(reset_name.__repr__())
        if len(senslist) > 0:
            for sens in senslist:
                if isinstance(sens.sig, Pointer):
                    sens_name = f"{current.__repr__()} .{sens.sig.var}[{sens.sig.ptr}]"
                else:
                    sens_name = f"{current.__repr__()} .{sens.sig.name}"
                self.always_feature_map.append(sens_name)
        self.frames.setAlwaysInfo(clock_name, clock_edge, clock_bit,
                                  reset_name, reset_edge, reset_bit, senslist, current)
        # TODO cache alaswaysInfo
        self.module_cache.addAlawaysInfo(self.frames.getCurrent(), self.frames.getAlwaysInfo())

        self.generic_visit(node)
        self.frames.setCurrent(current)

    def _get_signal_name(self, n):
        if isinstance(n, Identifier):
            return n.name
        if isinstance(n, Pointer):
            return self._get_signal_name(n.var)
        if isinstance(n, Partselect):
            return self._get_signal_name(n.var)
        return None

    def _createAlwaysinfo(self, node, scope):
        sens = None
        senslist = []
        clock_edge = None
        clock_name = None
        clock_bit = None
        reset_edge = None
        reset_name = None
        reset_bit = None

        for l in node.sens_list.list:
            if l.sig is None:
                continue

            if isinstance(l.sig, pyverilog.vparser.ast.Pointer):
                signame = self._get_signal_name(l.sig.var)
                bit = int(l.sig.ptr.value)
            else:
                signame = self._get_signal_name(l.sig)
                bit = 0

            if signaltype.isClock(signame):
                clock_name = self.searchTerminal(signame, scope)
                clock_edge = l.type
                clock_bit = bit
            elif signaltype.isReset(signame):
                reset_name = self.searchTerminal(signame, scope)
                reset_edge = l.type
                reset_bit = bit
            else:
                senslist.append(l)
        # TODO  为了保持设计的清晰和可预测性，通常建议将时钟边沿触发的逻辑和复位边沿触发的逻辑分开处理
        # if clock_edge is not None and len(senslist) > 0:
        #     raise verror.FormatError('Illegal sensitivity list')
        # if reset_edge is not None and len(senslist) > 0:
        #     raise verror.FormatError('Illegal sensitivity list')

        return (clock_name, clock_edge, clock_bit, reset_name, reset_edge, reset_bit, senslist)

    def visit_IfStatement(self, node):
        if self.frames.isFunctiondef() and not self.frames.isFunctioncall():
            return
        if self.frames.isTaskdef() and not self.frames.isTaskcall():
            return

        if (self.frames.isGenerate() and
                not self.frames.isAlways() and not self.frames.isInitial() and
                not self.frames.isFunctioncall() and not self.frames.isTaskcall() and
                not self.frames.isFunctiondef() and not self.frames.isTaskdef()):
            # generate-if statement
            current = self.frames.getCurrent()
            tree = self.getTree(node.cond, current)
            rslt = self.optimize(tree)
            if not isinstance(rslt, DFEvalValue):
                raise verror.FormatError("Can not resolve generate-if condition")

            if rslt.value > 0:
                label = self._if_true(node)
                if node.true_statement is not None:
                    self.copyBlockingAssigns(current + ScopeLabel(label, 'if'), current)
            else:
                label = self.labels.get(self.frames.getLabelKey('if'))
                self._if_false(node, label)
                if node.false_statement is not None:
                    self.copyBlockingAssigns(
                        current + ScopeLabel(self._toELSE(label), 'if'), current)
            return
        current = self.frames.getCurrent()
        probability = self.computerProbability(node.cond, current)
        label = self._if_true(node, probability)
        self._if_false(node, label, probability)

        current = self.frames.getCurrent()
        if node.true_statement is not None:
            self.copyBlockingAssigns(current + ScopeLabel(label, 'if'), current)
        if node.false_statement is not None:
            self.copyBlockingAssigns(current + ScopeLabel(self._toELSE(label), 'if'), current)

    def _toELSE(self, label):
        return label + '_ELSE'

    def _if_true(self, node, probability):
        if node.true_statement is None:
            return None
        label = self.labels.get(self.frames.getLabelKey('if'))
        current = self.stackNextFrame(label, 'if',
                                      frametype='ifthen',
                                      condition=node.cond,
                                      functioncall=self.frames.isFunctioncall(),
                                      taskcall=self.frames.isTaskcall(),
                                      generate=self.frames.isGenerate(),
                                      always=self.frames.isAlways(),
                                      initial=self.frames.isInitial(),
                                      probability=probability * self.frames.getProbability())

        self.copyPreviousNonblockingAssign(current + ScopeLabel(label, 'if'))

        if node.true_statement is not None:
            self.visit(node.true_statement)
        self.frames.setCurrent(current)
        return label

    def _if_false(self, node, label, probability):
        if node.false_statement is None:
            return
        label = self._toELSE(label)
        current = self.stackNextFrame(label, 'if',
                                      frametype='ifelse',
                                      condition=node.cond,
                                      functioncall=self.frames.isFunctioncall(),
                                      taskcall=self.frames.isTaskcall(),
                                      generate=self.frames.isGenerate(),
                                      always=self.frames.isAlways(),
                                      initial=self.frames.isInitial(),
                                      probability=(1 - probability) * self.frames.getProbability())

        self.copyPreviousNonblockingAssign(current + ScopeLabel(label, 'if'))

        if node.false_statement is not None:
            self.visit(node.false_statement)
        self.frames.setCurrent(current)
        return label

    def computerProbability(self, cond_node, scope) -> Fraction:
        if isinstance(cond_node, str):
            name = self.searchTerminal(cond_node, scope)
            term = self.dataflow.getTerm(name)
            msb, lsb = term.msb, term.lsb
            result = Fraction(1, pow(2, msb - lsb + 1))
            print(f"{cond_node}条件下的概率：{result}")
            return result

        if isinstance(cond_node, Identifier):
            if cond_node.scope is not None:
                raise NotImplemented
                name = self.searchScopeTerminal(cond_node.scope, cond_node.name, scope)
                if name is None:
                    raise verror.DefinitionError('No such signal: %s' % cond_node.name)
                return DFTerminal(name)
            name = self.searchTerminal(cond_node.name, scope)
            if name is None:
                raise verror.DefinitionError('No such signal: %s' % cond_node.name)
            term = self.dataflow.getTerm(name)
            msb, lsb = term.msb, term.lsb
            result = Fraction(1, pow(2, int(msb.value) - int(lsb.value) + 1))
            print(f"{cond_node}概率：{result}")
            return result

        # if isinstance(cond_node, Cond):
        #     true_df = self.makeDFTree(cond_node.true_value, scope)
        #     false_df = self.makeDFTree(cond_node.false_value, scope)
        #     cond_df = self.makeDFTree(cond_node.cond, scope)
        #     if isinstance(cond_df, DFBranch):
        #         return reorder.insertCond(cond_df, true_df, false_df)
        #     return DFBranch(cond_df, true_df, false_df)

        if isinstance(cond_node, Eq):
            return self.computerProbability(cond_node.left, scope)

        if isinstance(cond_node, Lor):
            return self.computerProbability(cond_node.left, scope) + self.computerProbability(cond_node.right, scope)

        if isinstance(cond_node, Ulnot):
            return self.computerProbability(cond_node.right, scope)

        if isinstance(cond_node, Unot):
            return self.computerProbability(cond_node.right, scope)

        if isinstance(cond_node, Pointer):
            var_df = self.makeDFTree(cond_node.var, scope)
            ptr_df = self.makeDFTree(cond_node.ptr, scope)
            # self.dataflow.getTerm(var_df.name)
            if isinstance(ptr_df, DFIntConst):
                return Fraction(1, pow(2, int(ptr_df.value) - int(ptr_df.value) + 1))

            raise NotImplemented

        # if isinstance(cond_node, Operator):  # EQ
        #     left_df = self.makeDFTree(cond_node.left, scope)
        #     right_df = self.makeDFTree(cond_node.right, scope)
        #     if isinstance(left_df, DFBranch) or isinstance(right_df, DFBranch):
        #         return reorder.insertOp(left_df, right_df, cond_node.__class__.__name__)
        #     return DFOperator((left_df, right_df,), cond_node.__class__.__name__)

        # if isinstance(cond_node, IntConst):
        #     return DFIntConst(cond_node.value)

        # region # 暂时不处理

        #
        # if isinstance(cond_node, FloatConst):
        #     return DFFloatConst(cond_node.value)
        #
        # if isinstance(cond_node, StringConst):
        #     return DFStringConst(cond_node.value)
        #

        #
        # if isinstance(cond_node, UnaryOperator):
        #     right_df = self.makeDFTree(cond_node.right, scope)
        #     if isinstance(right_df, DFBranch):
        #         return reorder.insertUnaryOp(right_df, cond_node.__class__.__name__)
        #     return DFOperator((right_df,), cond_node.__class__.__name__)
        #

        #
        # if isinstance(cond_node, Partselect):
        #     var_df = self.makeDFTree(cond_node.var, scope)
        #     msb_df = self.makeDFTree(cond_node.msb, scope)
        #     lsb_df = self.makeDFTree(cond_node.lsb, scope)
        #
        #     if isinstance(var_df, DFBranch):
        #         return reorder.insertPartselect(var_df, msb_df, lsb_df)
        #     return DFPartselect(var_df, msb_df, lsb_df)
        #

        # if isinstance(cond_node, Concat):
        #     nextcond_nodes = []
        #     for n in cond_node.list:
        #         nextcond_nodes.append(self.makeDFTree(n, scope))
        #     for n in nextcond_nodes:
        #         if isinstance(n, DFBranch):
        #             return reorder.insertConcat(tuple(nextcond_nodes))
        #     return DFConcat(tuple(nextcond_nodes))
        #
        # if isinstance(cond_node, Repeat):
        #     nextcond_nodes = []
        #     times = self.optimize(self.getTree(cond_node.times, scope)).value
        #     value = self.makeDFTree(cond_node.value, scope)
        #     for i in range(int(times)):
        #         nextcond_nodes.append(copy.deepcopy(value))
        #     return DFConcat(tuple(nextcond_nodes))
        #
        # if isinstance(cond_node, FunctionCall):
        #     func = self.searchFunction(cond_node.name.name, scope)
        #     if func is None:
        #         raise verror.DefinitionError('No such function: %s' % cond_node.name.name)
        #     label = self.labels.get(self.frames.getLabelKey('functioncall'))
        #
        #     save_current = self.frames.getCurrent()
        #     self.frames.setCurrent(scope)
        #
        #     current = self.frames.addFrame(
        #         ScopeLabel(label, 'functioncall'),
        #         functioncall=True, generate=self.frames.isGenerate(),
        #         always=self.frames.isAlways())
        #
        #     varname = self.frames.getCurrent() + ScopeLabel(func.name, 'signal')
        #
        #     self.addTerm(Wire(func.name, func.retwidth))
        #
        #     funcports = self.searchFunctionPorts(cond_node.name.name, scope)
        #     funcargs = cond_node.args
        #
        #     if len(funcports) != len(funcargs):
        #         raise verror.FormatError("%s takes exactly %d arguments. (%d given)" %
        #                                  (func.name.name, len(funcports), len(funcargs)))
        #     for port in funcports:
        #         self.addTerm(Wire(port.name, port.width))
        #
        #     lscope = self.frames.getCurrent()
        #     rscope = scope
        #     func_i = 0
        #     for port in funcports:
        #         arg = funcargs[func_i]
        #         dst = self.getDestinations(port.name, lscope)
        #         self.addDataflow(dst, arg, lscope, rscope)
        #         func_i += 1
        #
        #     self.visit(func)
        #
        #     self.frames.setCurrent(current)
        #     self.frames.setCurrent(save_current)
        #
        #     return DFTerminal(varname)
        #
        # if isinstance(cond_node, TaskCall):
        #     task = self.searchTask(cond_node.name.name, scope)
        #     label = self.labels.get(self.frames.getLabelKey('taskcall'))
        #
        #     current = self.frames.addFrame(
        #         ScopeLabel(label, 'taskcall'),
        #         taskcall=True, generate=self.frames.isGenerate(),
        #         always=self.frames.isAlways())
        #
        #     varname = self.frames.getCurrent() + ScopeLabel(task.name, 'signal')
        #
        #     taskports = self.searchTaskPorts(cond_node.name.name, scope)
        #     taskargs = cond_node.args
        #
        #     if len(taskports) != len(taskargs):
        #         raise verror.FormatError("%s takes exactly %d arguments. (%d given)" %
        #                                  (task.name.name, len(taskports), len(taskargs)))
        #     for port in taskports:
        #         self.addTerm(Wire(port.name, port.width))
        #
        #     lscope = self.frames.getCurrent()
        #     rscope = scope
        #     task_i = 0
        #     for port in taskports:
        #         arg = taskargs[task_i]
        #         dst = self.getDestinations(port.name, lscope)
        #         self.addDataflow(dst, arg, lscope, rscope)
        #         task_i += 1
        #
        #     self.visit(taskargs)
        #     self.frames.setCurrent(current)
        #     return DFTerminal(varname)
        #
        # if isinstance(cond_node, SystemCall):
        #     if cond_node.syscall == 'unsigned':
        #         return self.makeDFTree(cond_node.args[0], scope)
        #     if cond_node.syscall == 'signed':
        #         return self.makeDFTree(cond_node.args[0], scope)
        #     return DFIntConst('0')
        # endregion

        raise verror.FormatError("unsupported AST cond_node type: %s %s" %
                                 (str(type(cond_node)), str(cond_node)))

    def visit_CaseStatement(self, node):
        if self.frames.isFunctiondef() and not self.frames.isFunctioncall():
            return
        if self.frames.isTaskdef() and not self.frames.isTaskcall():
            return
        start_frame = self.frames.getCurrent()
        caseframes = []
        self._case(node.comp, node.caselist, caseframes, self.frames.getProbability(), self.frames.getProbability())
        self.frames.setCurrent(start_frame)
        for f in caseframes:
            self.copyBlockingAssigns(f, start_frame)

    def visit_CasexStatement(self, node):
        return self.visit_CaseStatement(node)

    def _case(self, comp, caselist, myframes, case_probability, reduce_probability):
        """
        case计算
        输入：
            casselist 每次取出一个case,
            case_prob是整个case块执行的概率，
            reduce_prob是整个case在经过 N个分支后剩余的执行概率
        计算公式：
            分三种情况：
                当前分支的概率=条件触发概率(computer_prob) * case块执行的概率(case_prob)  (1)
                当前分支所对应的else分支的概率=剩余的执行概率reduce_probability -= 当前分支的概率，这里的-=表示需要更新剩余执行概率  (2)

                下一分支的概率=上面公式(1)
                下一分支对应的else分支概率=剩余的执行概率(更新后)reduce_probability - 下一分支的概率

                default下的分支概率，直接等于剩余概率
        """
        if len(caselist) == 0:
            return

        case = caselist[0]
        cond = IntConst('1')
        if case.cond is not None:
            if len(case.cond) > 1:
                cond = Eq(comp, case.cond[0])
                for c in case.cond[1:]:
                    cond = Lor(cond, Eq(comp, c))
            else:
                cond = Eq(comp, case.cond[0])
        # else: raise Exception
        label = self.labels.get(self.frames.getLabelKey('if'))
        if len(caselist) == 1 and case.cond is None:  # default情况下
            computer_prob = reduce_probability
        else:
            computer_prob = self.computerProbability(cond, self.frames.getCurrent()) * case_probability
        current = self.stackNextFrame(label, 'if',
                                      frametype='ifthen',
                                      condition=cond,
                                      functioncall=self.frames.isFunctioncall(),
                                      taskcall=self.frames.isTaskcall(),
                                      generate=self.frames.isGenerate(),
                                      always=self.frames.isAlways(),
                                      initial=self.frames.isInitial(),
                                      probability=computer_prob)

        self.copyPreviousNonblockingAssign(current + ScopeLabel(label, 'if'))

        myframes.append(self.frames.getCurrent())

        if case.statement is not None:
            self.visit(case.statement)
        self.frames.setCurrent(current)

        if len(caselist) == 1:
            return
        reduce_probability -= computer_prob  # 计算剩余
        label = self._toELSE(label)
        current = self.stackNextFrame(label, 'if',
                                      frametype='ifelse',
                                      condition=cond,
                                      functioncall=self.frames.isFunctioncall(),
                                      taskcall=self.frames.isTaskcall(),
                                      generate=self.frames.isGenerate(),
                                      always=self.frames.isAlways(),
                                      initial=self.frames.isInitial(),
                                      probability=reduce_probability)

        self.copyPreviousNonblockingAssign(current + ScopeLabel(label, 'if'))

        myframes.append(current + ScopeLabel(label, 'if'))

        self._case(comp, caselist[1:], myframes, case_probability, reduce_probability)

    def visit_ForStatement(self, node):
        if self.frames.isFunctiondef() and not self.frames.isFunctioncall():
            return
        if self.frames.isTaskdef() and not self.frames.isTaskcall():
            return

        # pre-statement
        current = self.frames.getCurrent()
        pre_right = self.getTree(node.pre.right, current)
        pre_right_value = self.optimize(pre_right)
        loop = pre_right_value.value
        self.frames.setForPre()
        self.visit(node.pre)
        self.frames.unsetForPre()
        label = self.labels.get(self.frames.getLabelKey('for'))
        # loop = 0
        start_frame = self.frames.getCurrent()

        while True:
            # cond-statement
            current = self.frames.getCurrent()
            raw_tree = self.getTree(node.cond, current)
            rslt = self.optimize(raw_tree)
            if not isinstance(rslt, DFEvalValue):
                raise verror.FormatError(("Can not process the for-statement. "
                                          "for-condition should be evaluated statically."))
            if rslt.value <= 0:
                break

            # main-statement
            current = self.stackNextFrame(label, 'for',
                                          frametype='for',
                                          functioncall=self.frames.isFunctioncall(),
                                          taskcall=self.frames.isTaskcall(),
                                          generate=self.frames.isGenerate(),
                                          always=self.frames.isAlways(),
                                          initial=self.frames.isInitial(),
                                          loop=loop, loop_iter=self.frames.getForIter())

            self.visit(node.statement)
            self.copyBlockingAssigns(self.frames.getCurrent(), start_frame)
            self.frames.setCurrent(current)

            # post-statement
            current = self.frames.getCurrent()
            post_right = self.getTree(node.post.right, current)
            post_right_value = self.optimize(post_right)
            loop = post_right_value.value
            self.frames.setForPost()
            self.visit(node.post)
            self.frames.unsetForPost()
            # loop += 1

    def visit_WhileStatement(self, node):
        if self.frames.isFunctiondef() and not self.frames.isFunctioncall():
            return
        if self.frames.isTaskdef() and not self.frames.isTaskcall():
            return
        label = self.labels.get(self.frames.getLabelKey('while'))
        loop = 0
        start_frame = self.frames.getCurrent()

        while True:
            # cond-statement
            current = self.frames.getCurrent()
            raw_tree = self.getTree(node.cond, current)
            rslt = self.optimize(raw_tree)
            if not isinstance(rslt, DFEvalValue):
                raise verror.FormatError(("Can not process the while-statement. "
                                          "while-condition should be evaluated statically."))
            if rslt.value <= 0:
                break

            # main-statement
            current = self.stackNextFrame(label, 'while',
                                          frametype='while',
                                          functioncall=self.frames.isFunctioncall(),
                                          taskcall=self.frames.isTaskcall(),
                                          generate=self.frames.isGenerate(),
                                          always=self.frames.isAlways(),
                                          initial=self.frames.isInitial(),
                                          loop=loop)

            self.visit(node.statement)
            self.copyBlockingAssigns(self.frames.getCurrent(), start_frame)
            self.frames.setCurrent(current)
            loop += 1

    def visit_GenerateStatement(self, node):
        label = self.labels.get(self.frames.getLabelKey('generate'))
        current = self.stackNextFrame(label, 'generate',
                                      generate=True)

        self.generic_visit(node)
        self.frames.setCurrent(current)

    def visit_Block(self, node):
        label = None
        if node.scope is not None:
            label = node.scope
        else:
            label = self.labels.get(self.frames.getLabelKey('block'))

        current = self.stackNextFrame(label, 'block',
                                      frametype='block',
                                      functioncall=self.frames.isFunctioncall(),
                                      taskcall=self.frames.isTaskcall(),
                                      generate=self.frames.isGenerate(),
                                      always=self.frames.isAlways(),
                                      initial=self.frames.isInitial(),
                                      probability=self.frames.getProbability())

        self.generic_visit(node)
        self.frames.setCurrent(current)
        if self.frames.isAlways():  # 将下层节点的blocking赋值语句复制到上层节点
            self.copyBlockingAssigns(current + ScopeLabel(label, 'block'), current)

    def visit_Assign(self, node):
        self.addBind(node.left, node.right, bindtype='assign')

    def visit_BlockingSubstitution(self, node):
        self.addBind(node.left, node.right, self.frames.getAlwaysStatus(), 'blocking')
        # self.addBind(node.left, node.right, self.frames.getAlwaysStatus(), 'nonblocking')

    def visit_NonblockingSubstitution(self, node):
        """处理非阻塞赋值"""
        if self.frames.isForpre() or self.frames.isForpost():
            raise verror.FormatError(("Non Blocking Substitution is not allowed"
                                      "in for-statement"))
        if self.frames.isFunctioncall():
            raise verror.FormatError("Non Blocking Substitution is not allowed in function")
        self.addBind(node.left, node.right, self.frames.getAlwaysStatus(), 'nonblocking')

    def visit_SystemCall(self, node):
        logger.info("Warning: Isolated system call is not supported: %s" % node.syscall)

    def optimize(self, node):
        return self.optimizer.optimize(node)

    def stackInstanceFrame(self, instname, modulename):
        current = self.frames.getCurrent()
        current_probability = self.frames.getProbability()
        self.frames.setCurrent(current + ScopeLabel(instname, 'module'))
        self.frames.updateProbability(current_probability)
        self.copyFrameInfo(current + ScopeLabel(instname, 'module'))
        return current

    def stackNextFrame(self, label, scopetype,
                       frametype='none',
                       alwaysinfo=None, condition=None,
                       module=False, functioncall=False, taskcall=False,
                       generate=False, always=False, initial=False, loop=None, loop_iter=None, probability=Fraction(1)):
        """
        probability: 当前分支的概率
        """
        current = self.frames.getCurrent()
        scopelabel = ScopeLabel(label, scopetype, loop)
        nextscope = current + scopelabel

        if not self.frames.hasFrame(nextscope):  # 如果没有该作用域，则加入，如果经过 signalvisit,则已经添加
            current = self.frames.addFrame(scopelabel,
                                           frametype=frametype,
                                           alwaysinfo=alwaysinfo, condition=condition,
                                           module=module, functioncall=functioncall, taskcall=taskcall,
                                           generate=generate, always=always, initial=initial,
                                           loop=loop, loop_iter=loop_iter)
            # TODO cache add frame 这里要考虑当前的 current 以及后面会不会修改这个 frame
            self.module_cache.addFrame(self.frames.getCurrent(), self.frames.dict[self.frames.getCurrent()])

        self.frames.setCurrent(nextscope)
        self.frames.updateProbability(probability)
        new_current = self.frames.getCurrent()
        self.copyFrameInfo(new_current)
        return current

    def copyFrameInfo(self, current):
        for name, definitions in self.frames.getConsts(current).items():
            if len(definitions) > 1:
                raise verror.FormatError("Multiple definitions for Constant")
            for definition in definitions:
                termtype = definition.__class__.__name__
                term = Term(name, set([termtype]))
                self.dataflow.addTerm(name, term)
                if hasattr(self, "module_cache"):
                    self.module_cache.setTerm(name, term)

        for name, definitions in self.frames.getConsts(current).items():
            if len(definitions) > 1:
                raise verror.FormatError("Multiple definitions for Constant")
            for definition in definitions:
                cterm = self.makeConstantTerm(name, definition, current)
                self.setConstantTerm(name, cterm)

        all_passed = False
        while not all_passed:
            all_passed = True
            for name, definitions in self.frames.getConsts(current).items():
                if len(definitions) > 1:
                    raise verror.FormatError("Multiple definitions for Constant")
                if self.hasConstant(name):
                    continue

                for definition in definitions:
                    if isinstance(definition, Genvar):
                        continue
                    value = self.optimize(self.getTree(definition.value, current))
                    if not isinstance(value, DFEvalValue):
                        all_passed = False
                        continue
                    self.setConstant(name, value)

    def copyAllFrameInfo(self):
        for name, definitions in self.frames.getAllConsts().items():  # 将所有的常量加入dataflow
            if len(definitions) > 1:
                raise verror.FormatError("Multiple definitions for Constant")

            for definition in definitions:
                termtype = definition.__class__.__name__
                term = Term(name, set([termtype]))
                self.dataflow.addTerm(name, term)

        for name, definitions in self.frames.getAllSignals().items():  # 将信号加入 dataflow的 terms
            for definition in definitions:
                termtype = definition.__class__.__name__
                self.dataflow.addTerm(name, Term(name, set([termtype])))

        for name, definition in self.frames.getAllFunctions().items():
            self.dataflow.addFunction(name, definition.getDefinition())
            self.dataflow.addFunctionPorts(name, definition.getIOPorts())

        for name, definition in self.frames.getAllTasks().items():
            self.dataflow.addTask(name, definition.getDefinition())
            self.dataflow.addTaskPorts(name, definition.getIOPorts())

    def copyPreviousNonblockingAssign(self, scope):
        assign = self.frames.getPreviousNonblockingAssign()
        for name, bindlist in assign.items():
            for bind in bindlist:
                self.frames.addNonblockingAssign(name, bind)
                self.module_cache.addNonblockingAssign(name, bind, self.frames.getCurrent())
                # TODO cache nonblocking assign
                msb = bind.msb
                lsb = bind.lsb
                ptr = bind.ptr
                part_msb = None
                part_lsb = None
                condlist, flowlist = self.getCondflow(scope)
                alwaysinfo = bind.alwaysinfo
                raw_tree = bind.tree
                new_bind = self.makeBind(name, msb, lsb, ptr, part_msb, part_lsb,
                                         raw_tree, condlist, flowlist,
                                         alwaysinfo=alwaysinfo)
                self.dataflow.addBind(name, new_bind)
                self.module_cache.addBind(name, new_bind)

    def copyBlockingAssigns(self, scope_copy_from, scope_copy_to):
        assign = self.frames.getBlockingAssignsScope(scope_copy_from)
        for name, bindlist in assign.items():
            for bind in bindlist:
                self.frames.setBlockingAssign(name, bind, scope_copy_to)
                self.module_cache.addBlockingAssign(name, bind, scope_copy_to)
                # TODO copy blocking assign

    def setConstant(self, name, value):
        self.optimizer.setConstant(name, value)
        if hasattr(self, "module_cache"):
            self.module_cache.setConst(name, value)  # 加入缓存

    def resetConstant(self, name):
        self.optimizer.resetConstant(name)
        if hasattr(self, "module_cache"):
            self.module_cache.setConst(name, None)  # 加入缓存

    def getConstant(self, name):
        return self.optimizer.getConstant(name)

    def hasConstant(self, name):
        return self.optimizer.hasConstant(name)

    def setConstantTerm(self, name, term):
        if hasattr(self, "module_cache"):
            self.module_cache.setConstTerm(name, term)
        self.optimizer.setTerm(name, term)

    def getTerm(self, name):
        term = self.dataflow.getTerm(name)
        return term

    def getTermWidth(self, name):
        term = self.dataflow.getTerm(name)
        return term.msb, term.lsb

    def getTermDims(self, name):
        term = self.dataflow.getTerm(name)
        return term.dims

    def getTermtype(self, name):
        term = self.dataflow.getTerm(name)
        return term.termtype

    def getBindlist(self, name):
        return self.dataflow.getBindlist(name)

    def renameVar(self, name):
        renamedvar = (name[:-1] +
                      ScopeLabel('_rn' + str(self.renamecnt) +  # rn = rename 重命名信号，用于阻塞赋值
                                 '_' + name[-1].scopename, 'signal'))
        self.renamecnt += 1
        return renamedvar

    def toScopeChain(self, blocklabel, current):
        scopelist = []
        for b in blocklabel.labellist:
            if b.loop is not None:
                loop = self.optimize(self.getTree(b.loop, current))
                if not isinstance(loop, DFEvalValue):
                    raise verror.FormatError('Loop iterator should be constant')
                scopelist.append(ScopeLabel('for', 'for', loop.value))
            scopelist.append(ScopeLabel(b.name, 'any'))
        return ScopeChain(scopelist)

    def getModuleScopeChain(self, target):
        remove_cnt = 0
        length = len(target)
        for scope in reversed(target):
            if scope.scopetype == 'module':
                return target[:length - remove_cnt]
            remove_cnt += 1
        raise verror.DefinitionError('module not found')

    def searchScopeTerminal(self, blocklabel, name, current):
        currentmodule = self.getModuleScopeChain(current)
        localchain = currentmodule[-1:] + self.toScopeChain(blocklabel, current)
        matchedchain = self.frames.searchMatchedScopeChain(currentmodule, localchain)
        varname = currentmodule[:-1] + matchedchain + ScopeLabel(name, 'signal')
        if self.dataflow.hasTerm(varname):
            return varname
        raise verror.DefinitionError('No such signal: %s' % varname)

    # def searchScopeConstantDefinition(self, blocklabel, name, current):
    #    currentmodule = self.getModuleScopeChain(current)
    #    localchain = currentmodule[-1:] + self.toScopeChain(blocklabel, current)
    #    matchedchain = self.frames.searchMatchedScopeChain(currentmodule, localchain)
    #    constdef = self.frames.getConstantDefinition(matchedchain, name)
    #    return constdef

    # def searchScopeFunction(self, blocklabel, name, current):
    #    currentmodule = self.getModuleScopeChain(current)
    #    localchain = currentmodule[-1:] + self.toScopeChain(blocklabel, current)
    #    matchedchain = self.frames.searchMatchedScopeChain(currentmodule, localchain)
    #    varname = currentmodule[:-1] + matchedchain + ScopeLabel(name, 'function')
    #    if self.dataflow.hasFunction(varname): return self.dataflow.getFunction(varname)
    #    raise verror.DefinitionError('No such function: %s' % varname)

    # def searchScopeTask(self, blocklabel, name, current):
    #    currentmodule = self.getModuleScopeChain(current)
    #    localchain = currentmodule[-1:] + self.toScopeChain(blocklabel, current)
    #    matchedchain = self.frames.searchMatchedScopeChain(currentmodule, localchain)
    #    varname = currentmodule[:-1] + matchedchain + ScopeLabel(name, 'task')
    #    if self.dataflow.hasTask(varname): return self.dataflow.getTask(varname)
    #    raise verror.DefinitionError('No such task: %s' % varname)

    # def searchScopeFunctionPorts(self, blocklabel, name, current):
    #    currentmodule = self.getModuleScopeChain(current)
    #    localchain = currentmodule[-1:] + self.toScopeChain(blocklabel, current)
    #    matchedchain = self.frames.searchMatchedScopeChain(currentmodule, localchain)
    #    varname = currentmodule[:-1] + matchedchain + ScopeLabel(name, 'function')
    #    if self.dataflow.hasFunction(varname):
    #        return self.dataflow.getFunctionPorts(varname)
    #    raise verror.DefinitionError('No such function: %s' % varname)

    # def searchScopeTaskPorts(self, blocklabel, name, current):
    #    currentmodule = self.frames.getModuleScopeChain(current)
    #    localchain = currentmodule[-1:] + self.toScopeChain(blocklabel, current)
    #    matchedchain = self.frames.searchMatchedScopeChain(currentmodule, localchain)
    #    varname = currentmodule[:-1] + matchedchain + ScopeLabel(name, 'task')
    #    if self.dataflow.hasTask(varname):
    #        return self.dataflow.getTaskPorts(varname)
    #    raise verror.DefinitionError('No such task: %s' % varname)

    def searchConstantDefinition(self, key, name):
        const = self.frames.searchConstantDefinition(key, name)
        if const is None:
            raise verror.DefinitionError('constant value not found: %s' % name)
        return const

    def searchTerminal(self, name, scope):
        if len(scope) == 0:
            return None
        varname = scope + ScopeLabel(name, 'signal')
        if self.dataflow.hasTerm(varname):
            return varname
        if self.frames.dict[scope].isModule():
            return None
        # if self.frames.dict[scope].isFunctioncall(): return None
        return self.searchTerminal(name, scope[:-1])

    def searchFunction(self, name, scope):
        if len(scope) == 0:
            return None
        varname = scope + ScopeLabel(name, 'function')
        if self.dataflow.hasFunction(varname):
            return self.dataflow.getFunction(varname)
        if self.frames.dict[scope].isModule():
            return None
        return self.searchFunction(name, scope[:-1])

    def searchTask(self, name, scope):
        if len(scope) == 0:
            return None
        varname = scope + ScopeLabel(name, 'task')
        if self.dataflow.hasTask(varname):
            return self.dataflow.getTask(varname)
        if self.frames.dict[scope].isModule():
            return None
        return self.searchTask(name, scope[:-1])

    def searchFunctionPorts(self, name, scope):
        if len(scope) == 0:
            return ()
        varname = scope + ScopeLabel(name, 'function')
        if self.dataflow.hasFunction(varname):
            return self.dataflow.getFunctionPorts(varname)
        if self.frames.dict[scope].isModule():
            return ()
        return self.searchFunctionPorts(name, scope[:-1])

    def searchTaskPorts(self, name, scope):
        if len(scope) == 0:
            return ()
        varname = scope + ScopeLabel(name, 'task')
        if self.dataflow.hasTask(varname):
            return self.dataflow.getTaskPorts(varname)
        if self.frames.dict[scope].isModule():
            return ()
        return self.searchTaskPorts(name, scope[:-1])

    def makeConstantTerm(self, name, node, scope):
        termtype = node.__class__.__name__
        termtypes = set([termtype])
        msb = DFIntConst('31', probability=self.frames.getProbability()) if node.width is None else self.makeDFTree(
            node.width.msb, scope)
        lsb = DFIntConst('0', probability=self.frames.getProbability()) if node.width is None else self.makeDFTree(
            node.width.lsb, scope)
        return Term(name, termtypes, msb, lsb)

    def addTerm(self, node, rscope=None):
        if self.frames.isFunctiondef() and not self.frames.isFunctioncall():
            return
        if self.frames.isTaskdef() and not self.frames.isTaskcall():
            return
        scope = self.frames.getCurrent() if rscope is None else rscope
        name = scope + ScopeLabel(node.name, 'signal')
        termtype = node.__class__.__name__
        if self.frames.isFunctioncall():
            termtype = 'Function'
        if self.frames.isTaskcall():
            termtype = 'Task'
        termtypes = set([termtype])

        if isinstance(node, (Parameter, Localparam)):
            msb = DFIntConst('31', probability=self.frames.getProbability()) if node.width is None else self.makeDFTree(
                node.width.msb, scope)
        else:
            msb = DFIntConst('0', probability=self.frames.getProbability()) if node.width is None else self.makeDFTree(
                node.width.msb, scope)
        lsb = DFIntConst('0', probability=self.frames.getProbability()) if node.width is None else self.makeDFTree(
            node.width.lsb, scope)

        dims = None
        if node.dimensions is not None:
            dims = []
            for length in node.dimensions.lengths:
                l = self.makeDFTree(length.msb, scope)
                r = self.makeDFTree(length.lsb, scope)
                dims.append((l, r))
            dims = tuple(dims)

        term = Term(name, termtypes, msb, lsb, dims)
        self.dataflow.addTerm(name, term)
        self.setConstantTerm(name, term)
        #  append 追加到 module的 term
        self.module_cache.setTerm(name, term)

    def addBind(self, left, right, alwaysinfo=None, bindtype=None):  # 添加binddict绑定
        if self.frames.isFunctiondef() and not self.frames.isFunctioncall():
            return
        if self.frames.isTaskdef() and not self.frames.isTaskcall():
            return
        lscope = self.frames.getCurrent()
        rscope = lscope
        dst = self.getDestinations(left, lscope)  # 15% used  # 被赋值目标（name, msb, lsb, ptr, None, None）

        if bindtype == 'blocking':
            self.addDataflow_blocking(dst, right, lscope, rscope, alwaysinfo)
        else:
            self.addDataflow(dst, right, lscope, rscope, alwaysinfo, bindtype)

    def addInstanceParameterBind(self, param, name=None):
        lscope = self.frames.getCurrent()
        rscope = lscope[:-1]
        paramname = name if param.paramname is None else param.paramname
        dst = self.getDestinations(paramname, lscope)

        self.addDataflow(dst, param.argname, lscope, rscope, None, 'parameter')

    def addInstancePortBind(self, port, instportname=None, arrayindex=None):
        lscope = self.frames.getCurrent()
        rscope = lscope[:-1]
        portname = instportname if port.portname is None else port.portname
        ldst = self.getDestinations(portname, lscope)
        if ldst[0][0] is None:
            raise verror.DefinitionError('No such port: %s' % portname)

        termtype = self.getTermtype(ldst[0][0])
        for t in termtype:
            if t == 'Input':
                if port.argname is None:
                    continue
                portarg = (port.argname if arrayindex is None else
                           Pointer(port.argname, IntConst(str(arrayindex))))
                self.addDataflow(ldst, portarg, lscope, rscope, is_instance=True)
            elif t == 'Output':
                if port.argname is None:
                    continue
                portarg = (port.argname if arrayindex is None else
                           Pointer(port.argname, IntConst(str(arrayindex))))
                rdst = self.getDestinations(portarg, rscope)
                self.addDataflow(rdst, portname, rscope, lscope, is_instance=True)
            elif t == 'Inout':  # TODO is_instance的作用
                if port.argname is None:
                    continue
                portarg = (port.argname if arrayindex is None else
                           Pointer(port.argname, IntConst(str(arrayindex))))
                self.addDataflow(ldst, portarg, lscope, rscope)
                rdst = self.getDestinations(portarg, rscope)
                self.addDataflow(rdst, portname, rscope, lscope, is_instance=True)

    def addDataflow(self, dst, right, lscope, rscope, alwaysinfo=None, bindtype=None, is_instance=False):
        condlist, flowlist = self.getCondflow(lscope)  # 获取该节点所在的控制流信息
        raw_tree = self.getTree(right, rscope)
        if isinstance(right, str):
            lineno = None
        else:
            lineno = right.lineno

        for name, msb, lsb, ptr, part_msb, part_lsb in dst:
            bind = self.makeBind(name, msb, lsb, ptr, part_msb, part_lsb,
                                 raw_tree, condlist, flowlist,
                                 num_dst=len(dst),
                                 alwaysinfo=alwaysinfo,
                                 bindtype=bindtype)

            self.dataflow.addBind(name, bind)  # 添加 binddict到 dataflow中
            if not is_instance:
                self.module_cache.addBind(name, bind)

            if alwaysinfo is not None:  # 除非实例的端口赋值，会继续执行非阻塞赋值的设置
                self.setNonblockingAssign(name, dst, raw_tree,
                                          msb, lsb, ptr,
                                          part_msb, part_lsb,
                                          alwaysinfo)

    def addDataflow_blocking(self, dst, right, lscope, rscope, alwaysinfo):
        condlist, flowlist = self.getCondflow(lscope)
        raw_tree = self.getTree(right, rscope)
        lineno = right.lineno
        self.setDataflow_rename(dst, raw_tree, condlist, flowlist, lscope, alwaysinfo)

        if len(dst) == 1:  # set genvar value to the constant table
            name = dst[0][0]
            if signaltype.isGenvar(self.getTermtype(name)):
                value = self.optimize(raw_tree)
                self.setConstant(name, value)
            else:  # for "for-statement"
                value = self.optimize(raw_tree)
                if isinstance(value, DFEvalValue):
                    self.setConstant(name, value)
                else:
                    self.resetConstant(name)

    def getCondflow(self, scope):
        condlist = self.getCondlist(scope)
        condlist = self.resolveCondlist(condlist, scope)  # 50% time used
        flowlist = self.getFlowlist(scope)
        return (condlist, flowlist)

    # @get_time_ms(message="condlist")
    def getCondlist(self, scope):
        ret = []
        s = scope
        while s is not None:
            frame = self.frames.dict[s]
            cond = frame.getCondition()  # 获取当前帧的条件节点
            if cond is not None:
                key = f'{cond} + {s}'
                if key in self.DFTree_cache:
                    ret.append(self.DFTree_cache[key])
                else:
                    ret.append(self.makeDFTree(cond, self.reduceIfScope(s)))  # 构造当前帧的条件树
                    self.DFTree_cache[key] = ret[-1]

                # logger.info(cond, s, ret[-1].nextnodes)
            if frame.isModule():  # 截止到module
                break
            s = frame.previous
        ret.reverse()
        return tuple(ret)

    def getFlowlist(self, scope):
        ret = []
        s = scope
        while s is not None:
            frame = self.frames.dict[s]
            cond = frame.getCondition()
            if cond is not None:
                ret.append(not frame.isIfelse())
            if frame.isModule():
                break
            s = frame.previous
        ret.reverse()
        return tuple(ret)

    def getTree(self, node, scope):
        expr = node.var if isinstance(node, Rvalue) else node
        tree = self.makeDFTree(expr, scope)
        tree = self.resolveBlockingAssign(tree, scope)
        if not self.noreorder:
            tree = reorder.reorder(tree)
        return tree

    def makeDFTree(self, node, scope, probability=None):
        """
        从给定的抽象语法树（AST）节点递归构建数据流树（DFT）。
        这个方法是数据流分析过程的核心，因为它遍历AST并构建一个DFT，代表系统中的数据流。

        :param node: 要处理的AST中的当前节点。
        :param scope: 正在处理节点的当前作用域。
        :param probability: 当前节点的概率，用于概率分析。
        :return: 代表给定AST节点的数据流的DFT节点。
        """
        if not probability:  # 如果没有指定当前DFTree的概率，则使用当前作用域的概率
            probability = self.frames.dict[scope].probability

        if isinstance(node, str):
            # 如果节点是一个字符串，它代表DFT中的一个终端。
            # 在当前作用域中搜索终端并返回一个DFTerminal节点。
            name = self.searchTerminal(node, scope)
            return DFTerminal(name, probability=probability)

        if isinstance(node, Identifier):
            # 如果节点是一个标识符，它可能代表一个信号或一个变量。
            # 检查标识符是否有作用域，并在作用域中搜索它。
            if node.scope is not None:
                raise NotImplemented
                name = self.searchScopeTerminal(node.scope, node.name, scope)
                if name is None:
                    raise verror.DefinitionError('No such signal: %s' % node.name)
                return DFTerminal(name, probability=probability)
            # 如果没有指定作用域，就在当前作用域中搜索标识符。
            name = self.searchTerminal(node.name, scope)
            if name is None:
                raise verror.DefinitionError('No such signal: %s' % node.name)
            return DFTerminal(name, probability=probability)

        if isinstance(node, IntConst):
            # 如果节点是一个整数常量，返回一个DFIntConst节点。
            return DFIntConst(node.value, probability=probability)

        if isinstance(node, FloatConst):
            # 如果节点是一个浮点常量，返回一个DFFloatConst节点。
            return DFFloatConst(node.value, probability=probability)

        if isinstance(node, StringConst):
            # 如果节点是一个字符串常量，返回一个DFStringConst节点。
            return DFStringConst(node.value, probability=probability)

        if isinstance(node, Cond):
            # 如果节点是一个条件语句，递归构建条件、真分支和假分支的DFT。
            true_df = self.makeDFTree(node.true_value, scope, probability)
            false_df = self.makeDFTree(node.false_value, scope, probability)
            cond_df = self.makeDFTree(node.cond, scope, probability)
            # 如果条件DFT是一个分支，就把真分支和假分支插入进去。
            if isinstance(cond_df, DFBranch):
                raise NotImplemented
                return reorder.insertCond(cond_df, true_df, false_df)
            # 否则，创建一个新的分支节点。
            return DFBranch(cond_df, true_df, false_df, probability=probability)

        if isinstance(node, UnaryOperator):
            # 如果节点是一个一元运算符，递归构建它的右操作数的DFT。
            right_df = self.makeDFTree(node.right, scope, probability)
            # 如果右操作数的DFT是一个分支，就把一元运算符插入进去。
            if isinstance(right_df, DFBranch):
                return reorder.insertUnaryOp(right_df, node.__class__.__name__)
            # 否则，创建一个新的运算符节点。
            return DFOperator((right_df,), node.__class__.__name__, probability=probability)

        if isinstance(node, Operator):
            # 如果节点是一个二元运算符，递归构建它的左操作数和右操作数的DFT。
            left_df = self.makeDFTree(node.left, scope, probability)
            right_df = self.makeDFTree(node.right, scope, probability)
            # 如果任何一个操作数的DFT是一个分支，就把二元运算符插入进去。
            if isinstance(left_df, DFBranch) or isinstance(right_df, DFBranch):
                return reorder.insertOp(left_df, right_df, node.__class__.__name__)
            # 否则，创建一个新的运算符节点。
            return DFOperator((left_df, right_df,), node.__class__.__name__, probability=probability)

        if isinstance(node, Partselect):
            # 如果节点是一个部分选择，递归构建变量、MSB和LSB的DFT。
            var_df = self.makeDFTree(node.var, scope, probability)
            msb_df = self.makeDFTree(node.msb, scope, probability)
            lsb_df = self.makeDFTree(node.lsb, scope, probability)
            # 如果变量的DFT是一个分支，就把部分选择插入进去。
            if isinstance(var_df, DFBranch):
                return reorder.insertPartselect(var_df, msb_df, lsb_df)
            # 否则，创建一个新的部分选择节点。
            return DFPartselect(var_df, msb_df, lsb_df, probability=probability)

        if isinstance(node, Pointer):
            # 如果节点是一个指针，递归构建变量和指针的DFT。
            var_df = self.makeDFTree(node.var, scope, probability)
            ptr_df = self.makeDFTree(node.ptr, scope, probability)
            # 如果变量的DFT是一个终端并且有维度，就创建一个指针节点。
            if isinstance(var_df, DFTerminal) and self.getTermDims(var_df.name) is not None:
                raise NotImplemented
                return DFPointer(var_df, ptr_df)
            # 否则，创建一个部分选择节点，把指针作为MSB和LSB。
            return DFPartselect(var_df, ptr_df, copy.deepcopy(ptr_df), probability=probability)

        if isinstance(node, Concat):
            # 如果节点是一个连接，递归构建每个操作数的DFT。
            nextnodes = []
            for n in node.list:
                nextnodes.append(self.makeDFTree(n, scope, probability))
            # 如果任何一个操作数的DFT是一个分支，就把连接插入进去。
            for n in nextnodes:
                if isinstance(n, DFBranch):
                    return reorder.insertConcat(tuple(nextnodes))
            # 否则，创建一个新的连接节点。
            return DFConcat(tuple(nextnodes), probability=probability)

        if isinstance(node, Repeat):
            # 如果节点是一个重复，递归构建次数和值的DFT。
            nextnodes = []
            times = self.optimize(self.getTree(node.times, scope)).value
            value = self.makeDFTree(node.value, scope, probability)
            # 重复值的DFT指定的次数。
            for i in range(int(times)):
                nextnodes.append(copy.deepcopy(value))
            # 创建一个连接节点，把重复的值放进去。
            return DFConcat(tuple(nextnodes), probability=probability)

        if isinstance(node, FunctionCall):
            # 如果节点是一个函数调用，搜索函数并处理它的参数。
            func = self.searchFunction(node.name.name, scope)
            if func is None:
                raise verror.DefinitionError('No such function: %s' % node.name.name)
            label = self.labels.get(self.frames.getLabelKey('functioncall'))

            save_current = self.frames.getCurrent()
            self.frames.setCurrent(scope)

            current = self.frames.addFrame(  # TODO 暂不处理 FunctionCall
                ScopeLabel(label, 'functioncall'),
                functioncall=True, generate=self.frames.isGenerate(),
                always=self.frames.isAlways())
            # TODO cache func frames
            self.module_cache.addFrame(self.frames.getCurrent(), self.frames.dict[self.frames.getCurrent()])

            varname = self.frames.getCurrent() + ScopeLabel(func.name, 'signal')

            self.addTerm(Wire(func.name, func.retwidth))

            funcports = self.searchFunctionPorts(node.name.name, scope)
            funcargs = node.args

            if len(funcports) != len(funcargs):
                raise verror.FormatError("%s takes exactly %d arguments. (%d given)" %
                                         (func.name.name, len(funcports), len(funcargs)))
            for port in funcports:
                self.addTerm(Wire(port.name, port.width))

            lscope = self.frames.getCurrent()
            rscope = scope
            func_i = 0
            for port in funcports:
                arg = funcargs[func_i]
                dst = self.getDestinations(port.name, lscope)
                self.addDataflow(dst, arg, lscope, rscope)
                func_i += 1

            self.visit(func)

            self.frames.setCurrent(current)
            self.frames.setCurrent(save_current)
            # 处理函数调用和它的参数。
            # 这是未来实现的一个占位符。
            return DFTerminal(varname)

        if isinstance(node, TaskCall):
            # 如果节点是一个任务调用，搜索任务并处理它的参数。
            task = self.searchTask(node.name.name, scope)
            label = self.labels.get(self.frames.getLabelKey('taskcall'))

            current = self.frames.addFrame(  # TODO 暂不处理 TaskCall
                ScopeLabel(label, 'taskcall'),
                taskcall=True, generate=self.frames.isGenerate(),
                always=self.frames.isAlways())
            # TODO cache task frames
            self.module_cache.addFrame(self.frames.getCurrent(), self.frames.dict[self.frames.getCurrent()])

            varname = self.frames.getCurrent() + ScopeLabel(task.name, 'signal')

            taskports = self.searchTaskPorts(node.name.name, scope)
            taskargs = node.args

            if len(taskports) != len(taskargs):
                raise verror.FormatError("%s takes exactly %d arguments. (%d given)" %
                                         (task.name.name, len(taskports), len(taskargs)))
            for port in taskports:
                self.addTerm(Wire(port.name, port.width))

            lscope = self.frames.getCurrent()
            rscope = scope
            task_i = 0
            for port in taskports:
                arg = taskargs[task_i]
                dst = self.getDestinations(port.name, lscope)
                self.addDataflow(dst, arg, lscope, rscope)
                task_i += 1

            self.visit(taskargs)
            self.frames.setCurrent(current)
            # 处理任务调用和它的参数。
            # 这是未来实现的一个占位符。
            return DFTerminal(varname)

        if isinstance(node, SystemCall):
            # 如果节点是一个系统调用，根据系统调用的类型处理它。
            if node.syscall == 'unsigned':
                return self.makeDFTree(node.args[0], scope, probability)
            if node.syscall == 'signed':
                return self.makeDFTree(node.args[0], scope, probability)
            raise NotImplemented
            return DFIntConst('0')

        # 如果节点类型不被识别，就抛出一个格式错误。
        raise verror.FormatError("unsupported AST node type: %s %s" %
                                 (str(type(node)), str(node)))

    def reduceIfScope(self, scope):
        if len(scope) == 0:
            return scope
        if scope[-1].scopetype == 'if':
            return scope[:-1]
        return self.reduceIfScope(scope[:-1])

    def resolveCondlist(self, condlist, scope):
        resolved_condlist = []
        reducedscope = self.reduceIfScope(scope)
        for i, c in enumerate(reversed(condlist)):
            resolved_condlist.append(self.resolveBlockingAssign(c, reducedscope))
            reducedscope = self.reduceIfScope(reducedscope)
        return tuple(reversed(resolved_condlist))

    def removeOverwrappedCondition(self, tree, current_bindlist, scope):
        msb, lsb = self.getTermWidth(tree.name)
        merged_tree = self.getFitTree(current_bindlist, msb, lsb)
        condlist, flowlist = self.getCondflow(scope)
        (merged_tree,
         rest_condlist,
         rest_flowlist,
         match_flowlist) = self.diffBranchTree(merged_tree, condlist, flowlist)
        return replace.replaceUndefined(merged_tree, tree.name)

    def resolveBlockingAssign(self, tree, scope):  # 95% time used
        if tree is None:
            return None

        if isinstance(tree, DFConstant):
            return tree

        if isinstance(tree, DFEvalValue):
            return tree

        if isinstance(tree, DFTerminal):
            if signaltype.isGenvar(self.getTermtype(tree.name)):
                return self.getConstant(tree.name)

            # current_bindlist = self.frames.getBlockingAssign(tree.name, scope)
            current_bindlist = []  # update 原因：感觉没有走这一路 2024 年 10 月 22 日 16:21:46
            if len(current_bindlist) == 0:
                return tree
            raise NotImplemented
            return self.removeOverwrappedCondition(tree, current_bindlist, scope)

        if isinstance(tree, DFBranch):
            truenode = self.resolveBlockingAssign(tree.truenode, scope)
            falsenode = self.resolveBlockingAssign(tree.falsenode, scope)
            condnode = self.resolveBlockingAssign(tree.condnode, scope)
            if isinstance(condnode, DFBranch):
                return reorder.insertBranch(condnode, truenode, falsenode)
            return DFBranch(condnode, truenode, falsenode, probability=tree.probability)

        if isinstance(tree, DFOperator):
            resolvednodes = []
            for n in tree.nextnodes:
                resolvednodes.append(self.resolveBlockingAssign(n, scope))
            for r in resolvednodes:
                if isinstance(r, DFBranch):
                    return reorder.insertOpList(resolvednodes, tree.operator)
            return DFOperator(tuple(resolvednodes), tree.operator, probability=tree.probability)

        if isinstance(tree, DFConcat):
            resolvednodes = []
            for n in tree.nextnodes:
                resolvednodes.append(self.resolveBlockingAssign(n, scope))
            for r in resolvednodes:
                if isinstance(r, DFBranch):
                    return reorder.insertConcat(resolvednodes)
            return DFConcat(tuple(resolvednodes), probability=tree.probability)

        if isinstance(tree, DFPartselect):
            resolved_msb = self.resolveBlockingAssign(tree.msb, scope)
            resolved_lsb = self.resolveBlockingAssign(tree.lsb, scope)
            resolved_var = self.resolveBlockingAssign(tree.var, scope)
            if isinstance(resolved_var, DFBranch):
                return reorder.insertPartselect(resolved_var,
                                                resolved_msb, resolved_lsb)
            return DFPartselect(resolved_var, resolved_msb, resolved_lsb, probability=tree.probability)

        if isinstance(tree, DFPointer):
            # raise NotImplemented
            resolved_ptr = self.resolveBlockingAssign(tree.ptr, scope)
            if (isinstance(tree.var, DFTerminal) and
                    self.getTermDims(tree.var.name) is not None):
                current_bindlist = self.frames.getBlockingAssign(tree.var.name, scope)
                if len(current_bindlist) == 0:
                    raise NotImplemented
                    return DFPointer(tree.var, resolved_ptr)
                new_tree = DFPointer(tree.var, resolved_ptr)
                for bind in current_bindlist:
                    new_tree = DFBranch(DFOperator((bind.ptr, resolved_ptr), 'Eq', probability=tree.probability),
                                        bind.tree, new_tree, probability=tree.probability)
                logger.warning(("Warning: "
                                "Overwrting Blocking Assignment with Reg Array is not supported"))
                return new_tree
            resolved_var = self.resolveBlockingAssign(tree.var, scope)
            if isinstance(resolved_var, DFBranch):
                return reorder.insertPointer(resolved_var, resolved_ptr)
            return DFPointer(resolved_var, resolved_ptr, probability=tree.probability)

        raise verror.FormatError("unsupported DFNode type: %s %s" %
                                 (str(type(tree)), str(tree)))

    def getFitTree(self, bindlist, msb, lsb):
        optimized_msb = self.optimize(msb)
        optimized_lsb = self.optimize(lsb)
        for bind in bindlist:
            if bind.msb is None and bind.lsb is None:
                return bind.tree
            if (self.optimize(bind.msb) == optimized_msb and
                    self.optimize(bind.lsb) == optimized_lsb):
                return bind.tree
        return self.getMergedTree(bindlist)

    def getMergedTree(self, bindlist):
        concatlist = []
        last_msb = -1
        last_ptr = -1

        def bindkey(x):
            lsb = 0 if x.lsb is None else x.lsb.value
            ptr = 0 if not isinstance(x.ptr, DFEvalValue) else x.ptr.value
            term = self.getTerm(x.dest)
            length = (abs(self.optimize(term.msb).value
                          - self.optimize(term.lsb).value) + 1)
            return ptr * length + lsb

        for bind in sorted(bindlist, key=bindkey):
            lsb = 0 if bind.lsb is None else bind.lsb.value
            if last_ptr != (-1 if not isinstance(bind.ptr, DFEvalValue)
            else bind.ptr.value):
                continue
            if last_msb + 1 < lsb:
                raise NotImplemented
                concatlist.append(DFUndefined(last_msb - lsb - 1))
            concatlist.append(bind.tree)
            last_msb = -1 if bind.msb is None else bind.msb.value
            last_ptr = -1 if not isinstance(bind.ptr, DFEvalValue) else bind.ptr.value
        raise NotImplemented
        return DFConcat(tuple(reversed(concatlist)))

    def getDestinations(self, left, scope):
        ret = []
        dst = self.getDsts(left, scope)
        part_offset = DFIntConst('0', probability=self.frames.getProbability())
        for name, msb, lsb, ptr in reversed(dst):
            if len(dst) == 1:
                ret.append((name, msb, lsb, ptr, None, None))
                continue

            if msb is None and lsb is None:
                msb, lsb = self.getTermWidth(name)
            diff = reorder.reorder(DFOperator((msb, lsb), 'Minus', probability=self.frames.getProbability()))
            part_lsb = part_offset
            part_msb = reorder.reorder(
                DFOperator((part_offset, diff), 'Plus', probability=self.frames.getProbability()))
            part_offset = reorder.reorder(
                DFOperator((part_msb, DFIntConst('1')), 'Plus', probability=self.frames.getProbability()))

            ret.append((name, msb, lsb, ptr, part_msb, part_lsb))

        return tuple(ret)

    def getDsts(self, left, scope):
        if isinstance(left, Lvalue):
            return self.getDsts(left.var, scope)
        if isinstance(left, LConcat) or isinstance(left, Concat):  # 修复bug
            dst = []
            for n in left.list:
                dst.extend(list(self.getDsts(n, scope)))
            return tuple(dst)
        ret = (self.getDst(left, scope),)
        return ret

    def getDst(self, left, scope):
        if isinstance(left, str):  # Parameter
            name = self.searchTerminal(left, scope)
            return (name, None, None, None)

        if isinstance(left, Identifier):
            name = self.searchTerminal(left.name, scope)
            if name is None:
                m = re.search('none', self.default_nettype)
                if m:
                    raise verror.FormatError("No such signal: %s" % left.name)
                m = re.search('wire', self.default_nettype)
                if m:
                    self.addTerm(Wire(left.name), rscope=scope)
                m = re.search('reg', self.default_nettype)
                if m:
                    self.addTerm(Reg(left.name), rscope=scope)
                name = self.searchTerminal(left.name, scope)
            if left.scope is not None:
                name = left.scope + ScopeLabel(left.name, 'signal')
            return (name, None, None, None)

        if isinstance(left, Partselect):
            if isinstance(left.var, Pointer):
                name, msb, lsb, ptr = self.getDst(left.var, scope)
                if msb is None and lsb is None:
                    msb = self.optimize(self.makeDFTree(left.msb, scope))
                    lsb = self.optimize(self.makeDFTree(left.lsb, scope))
                else:
                    raise verror.FormatError("%s is not array" % str(name))
                return (name, msb, lsb, ptr)
            name = self.searchTerminal(left.var.name, scope)
            if left.var.scope is not None:
                name = left.var.scope + ScopeLabel(left.var.name, 'signal')
            msb = self.optimize(self.makeDFTree(left.msb, scope))
            lsb = self.optimize(self.makeDFTree(left.lsb, scope))
            return (name, msb, lsb, None)

        if isinstance(left, Pointer):
            if isinstance(left.var, Pointer):
                name, msb, lsb, ptr = self.getDst(left.var, scope)
                if msb is None and lsb is None:
                    msb = self.optimize(self.makeDFTree(left.ptr, scope))
                    lsb = copy.deepcopy(msb)
                else:
                    raise verror.FormatError("%s is not array" % str(name))
                return (name, msb, lsb, ptr)
            name = self.searchTerminal(left.var.name, scope)
            if left.var.scope is not None:
                name = left.var.scope + ScopeLabel(left.var.name, 'signal')
            ptr = self.optimize(self.makeDFTree(left.ptr, scope))
            if self.getTermDims(name) is not None:
                return (name, None, None, ptr)
            return (name, ptr, copy.deepcopy(ptr), None)

        raise verror.FormatError("unsupported AST node type: %s %s" %
                                 (str(type(left)), str(left)))

    def setDataflow_rename(self, dst, raw_tree, condlist, flowlist,
                           scope, alwaysinfo=None):
        renamed_dst = self.getRenamedDst(dst)
        self.setRenamedTree(renamed_dst, raw_tree, alwaysinfo)
        self.setRenamedFlow(dst, renamed_dst, condlist, flowlist, scope, alwaysinfo)

    def setNonblockingAssign(self, name, dst, raw_tree, msb, lsb, ptr,
                             part_msb, part_lsb, alwaysinfo):
        """将非阻塞赋值的信息压栈"""
        tree = raw_tree
        if len(dst) > 1:
            tree = reorder.reorder(DFPartselect(raw_tree, part_msb, part_lsb, probability=raw_tree.probability))
        bind = Bind(tree, name, msb, lsb, ptr, alwaysinfo)
        self.frames.addNonblockingAssign(name, bind)
        # TODO cache non Blocking Assign
        self.module_cache.addNonblockingAssign(name, bind, self.frames.getCurrent())

    def getRenamedDst(self, dst):
        renamed_dst = ()
        for d in dst:
            dname = d[0]
            samename_exists = True
            while samename_exists:
                renamed_dname = self.renameVar(dname)
                samename_exists = self.dataflow.hasTerm(renamed_dname)
            term = self.dataflow.getTerm(dname)
            newterm = copy.deepcopy(term)
            newterm.name = renamed_dname
            newterm.termtype = set(['Rename'])
            self.dataflow.addTerm(renamed_dname, newterm)
            self.module_cache.setTerm(renamed_dname, newterm)
            newd = (renamed_dname,) + d[1:]
            renamed_dst += (newd,)
        return renamed_dst

    def setRenamedTree(self, renamed_dst, raw_tree, alwaysinfo):
        for name, msb, lsb, ptr, part_msb, part_lsb in renamed_dst:
            tree = raw_tree
            if len(renamed_dst) > 1:
                tree = reorder.reorder(
                    DFPartselect(tree, part_msb, part_lsb, probability=tree.probability))
            bind = Bind(tree, name, msb, lsb, ptr)
            self.dataflow.addBind(name, bind)
            self.module_cache.addBind(name, bind)

            value = self.optimize(tree)
            if isinstance(value, DFEvalValue):
                self.setConstant(name, value)
            msb, lsb = self.getTermWidth(name)
            self.setConstantTerm(name, Term(name, set(['Rename']), msb, lsb))

    def setRenamedFlow(self, dst, renamed_dst, condlist, flowlist,
                       scope, alwaysinfo=None):
        term_i = 0
        for name, msb, lsb, ptr, part_msb, part_lsb in dst:
            renamed_term = DFTerminal(renamed_dst[term_i][0], probability=self.frames.getProbability())
            renamed_bind = self.makeBind(name, msb, lsb, ptr, part_msb, part_lsb,
                                         renamed_term, condlist, flowlist,
                                         num_dst=len(dst), alwaysinfo=alwaysinfo)
            self.dataflow.addBind(name, renamed_bind)
            self.module_cache.addBind(name, renamed_bind)

            self.frames.setBlockingAssign(name, renamed_bind, scope)
            # TODO cache blocking assign
            self.module_cache.addBlockingAssign(name, renamed_bind, scope)

            term_i += 1

    def makeBind(self, name, msb, lsb, ptr, part_msb, part_lsb,
                 raw_tree, condlist, flowlist,
                 num_dst=1, alwaysinfo=None, bindtype=None):
        """

        创建给定参数的Bind对象。

        此方法通过处理给定的参数（包括名称、MSB、LSB、指针、部分MSB、部分LSB、原始树、条件列表、流列表、目的地数量、始终信息和绑定类型）
        来构造Bind对象。它检查现有绑定，根据条件和流构造树，并在必要时应用部分选择。

        参数：
        - name：绑定的名称。
        - msb：最高有效位。
        - lsb：最低有效位。
        - ptr：指针。
        - part_msb：部分选择的最高有效位。
        - part_lsb：部分选择的最低有效位。
        - raw_tree：原始树结构。
        - condlist：条件列表。
        - flowlist：流控制值列表。
        - num_dst：目的地数量（默认为1）。
        - alwaysinfo：始终块的附加信息（默认为None）。
        - bindtype：绑定类型（默认为None）。

        返回：
        - 从给定参数构造的Bind对象。
        """

        # 获取给定名称的当前绑定列表
        current_bindlist = self.getBindlist(name)
        current_tree = None
        current_msb = None
        current_lsb = None
        current_ptr = None

        # 检查是否存在现有绑定
        if len(current_bindlist) > 0:
            # 遍历当前绑定以找到匹配项
            for current_bind in current_bindlist:
                # 检查当前绑定是否与给定参数匹配
                if (current_bind.msb == msb and
                        current_bind.lsb == lsb
                        and current_bind.ptr == ptr):
                    # 如果找到匹配项，更新当前树及其属性
                    current_tree = current_bind.tree
                    current_msb = current_bind.msb
                    current_lsb = current_bind.lsb
                    current_ptr = current_bind.ptr
                    break

        # 初始化剩余树、条件列表和流列表的变量
        rest_tree = current_tree
        rest_condlist = condlist
        rest_flowlist = flowlist

        # 初始化一个空元组，用于存储匹配流列表
        match_flowlist = ()
        # 检查当前MSB、LSB和PTR是否与给定参数匹配
        if (current_msb == msb and
                current_lsb == lsb
                and current_ptr == ptr):
            # 如果找到匹配项，处理分支树以找到匹配流列表
            (rest_tree,
             rest_condlist,  # 不匹配的 条件列表
             rest_flowlist,  # 不匹配的 控制流
             match_flowlist) = self.diffBranchTree(current_tree, condlist, flowlist)

        # 将 tree 构造为待添加的分支树
        add_tree = self.makeBranchTree(rest_condlist, rest_flowlist, raw_tree)

        # 检查是否存在剩余流列表和剩余树
        # TODO 这里会合并两个always块中的分支
        if rest_flowlist and rest_tree is not None:
            # if rest_flowlist and rest_tree is not None and len(match_flowlist) > 0:
            # 为将剩余树附加到添加树而修改剩余流列表
            _rest_flowlist = rest_flowlist[:-1] + (not rest_flowlist[-1],)
            # 使用修改后的剩余流列表将剩余树附加到添加树
            add_tree = self.appendBranchTree(add_tree, _rest_flowlist, rest_tree)

        # 将需要插入的分支追加到主干上，并更新概率
        tree = reorder.reorder(
            self.appendBranchTree(current_tree, match_flowlist, add_tree))

        # 检查目的地数量是否大于1
        if num_dst > 1:
            # 如果需要，对树应用部分选择
            tree = reorder.reorder(
                DFPartselect(tree, part_msb, part_lsb, probability=tree.probability))

        # 返回从最终树和给定参数构造的Bind对象
        return Bind(tree, name, msb, lsb, ptr, alwaysinfo, bindtype)

    def diffBranchTree(self, tree, condlist, flowlist, matchflowlist=()):
        if len(condlist) == 0:  # 没有条件需要比较了
            return (tree, condlist, flowlist, matchflowlist)

        if not isinstance(tree, DFBranch):  # 非分支节点
            return (tree, condlist, flowlist, matchflowlist)

        if condlist[0] != tree.condnode:  # 条件不匹配
            return (tree, condlist, flowlist, matchflowlist)
        # 递归处理比较 tree与 root的差异，在matchflowlist中记录相同的分支
        if flowlist[0]:
            return self.diffBranchTree(
                tree.truenode, condlist[1:], flowlist[1:],
                matchflowlist + (flowlist[0],))
        else:
            return self.diffBranchTree(
                tree.falsenode, condlist[1:], flowlist[1:],
                matchflowlist + (flowlist[0],))

    def makeBranchTree(self, condlist, flowlist, node):
        if len(condlist) == 0 or len(flowlist) == 0:
            return node
        if len(condlist) == 1:
            if flowlist[0]:
                return DFBranch(condlist[0], node, None, probability=node.probability)
            else:
                return DFBranch(condlist[0], None, node, probability=node.probability)
        else:
            if flowlist[0]:
                truenode = self.makeBranchTree(condlist[1:], flowlist[1:], node)
                return DFBranch(
                    condlist[0],
                    truenode,
                    None
                    , probability=truenode.probability)
            else:
                falsenode = self.makeBranchTree(condlist[1:], flowlist[1:], node)
                return DFBranch(
                    condlist[0],
                    None,
                    falsenode
                    , probability=falsenode.probability)

    def appendBranchTree(self, base, pos, tree):
        if len(pos) == 0:  # 当pos 参数为空 也就是 true或者 false分支都没有，说明子树tree就是根节点
            return tree
        if len(pos) == 1:  # 否则将子树tree追加到 base分支上
            if pos[0]:
                return DFBranch(base.condnode, tree, base.falsenode,
                                probability=tree.probability + base.falsenode.probability)
            else:
                return DFBranch(base.condnode, base.truenode, tree,
                                probability=tree.probability + base.truenode.probability)
        else:
            if pos[0]:
                base_falsenode_probability = 0 if base.falsenode is None else base.falsenode.probability
                truenode = self.appendBranchTree(base.truenode, pos[1:], tree)
                return DFBranch(
                    base.condnode,
                    truenode,
                    base.falsenode, probability=base_falsenode_probability + truenode.probability)
            else:
                base_truenode_probability = 0 if base.truenode is None else base.truenode.probability

                falsenode = self.appendBranchTree(base.falsenode, pos[1:], tree)
                return DFBranch(
                    base.condnode,
                    base.truenode,
                    falsenode
                    , probability=base_truenode_probability + falsenode.probability)
