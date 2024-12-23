# -------------------------------------------------------------------------------
# scope.py
#
# classes for definition of scope
#
# Copyright (C) 2013, Shinya Takamaeda-Yamazaki
# License: Apache 2.0
# -------------------------------------------------------------------------------
from __future__ import absolute_import
from __future__ import print_function
import sys
import os
import copy

scopetype_list_unprint = ('generate', 'always', 'function',  # 'functioncall',
                          'task', 'taskcall', 'initial', 'for', 'while', 'if')
scopetype_list_print = ('module', 'block', 'signal', 'functioncall',)
scopetype_list = scopetype_list_unprint + scopetype_list_print + ('any', )


class ScopeLabel(object):
    def __init__(self, scopename, scopetype='any', scopeloop=None):
        self.scopename = scopename
        if scopetype not in scopetype_list:
            raise DefinitionError('No such Scope type')
        self.scopetype = scopetype
        self.scopeloop = scopeloop

    def __repr__(self):
        ret = []
        ret.append(self.scopename)
        if self.scopeloop is not None:
            ret.append('[')
            ret.append(str(self.scopeloop))
            ret.append(']')
        return ''.join(ret)

    def tocode(self):
        if self.scopetype in scopetype_list_unprint:
            return ''
        return self.scopename

    def __eq__(self, other):
        # if type(self) != type(other):
        #     return False
        # if self.scopetype == 'any' or other.scopetype == 'any':
        #     return ((self.scopename, self.scopeloop)
        #             == (other.scopename, other.scopeloop))
        # return (self.scopename, self.scopetype, self.scopeloop) == (other.scopename, other.scopetype, other.scopeloop)
        # update 原因：执行时间太长，不比较数组，直接比较元素 2024 年 10 月 23 日 09:17:32
        if not isinstance(other, type(self)):
            return False

        if self.scopetype == 'any' or other.scopetype == 'any':
            return self.scopename == other.scopename and self.scopeloop == other.scopeloop

        return (self.scopename == other.scopename and
                self.scopetype == other.scopetype and
                self.scopeloop == other.scopeloop)

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        # return hash((self.scopename, self.scopetype, self.scopeloop))
        return hash((self.scopename, self.scopeloop))  # to use for dict key with any scopetype

    def isPrintable(self):
        return self.scopetype in (scopetype_list_print + ('any',))


class ScopeChain(object):
    def __init__(self, scopechain=None):
        self.scopechain = []
        if scopechain is not None:
            self.scopechain = scopechain

    def __add__(self, r):
        # new_chain = copy.deepcopy(self) # zs 取消 deepcopy, 原因：耗时太长, 2024 年 10 月 22 日 10:12:54
        new_chain = ScopeChain(copy.copy(self.scopechain))
        if isinstance(r, ScopeLabel):
            new_chain.append(r)
        elif isinstance(r, ScopeChain):
            new_chain.extend(r.scopechain)
        else:
            raise verror.DefinitionError('Can not add %s' % str(r))
        return new_chain

    def find(self, old):
        sub_length = len(old)
        result = []
        i = 0
        scope_chain = self.scopechain
        while i < len(scope_chain):
            # 检查是否找到子数组
            if scope_chain[i:i + sub_length] == old.scopechain:
                return True
            else:
                result.append(scope_chain[i])  # 保留当前元素
                i += 1
        return False

    def replace(self, old, new):
        sub_length = len(old)
        result = []
        i = 0
        scope_chain = self.scopechain
        while i < len(scope_chain):
            # 检查是否找到子数组
            if scope_chain[i:i + sub_length] == old.scopechain:
                result.extend(new.scopechain)  # 替换为另一个数组
                i += sub_length  # 跳过子数组的长度
            else:
                result.append(scope_chain[i])  # 保留当前元素
                i += 1
        return ScopeChain(result)

    def append(self, r):
        self.scopechain.append(r)

    def extend(self, r):
        self.scopechain.extend(r)

    def tocode(self):
        ret = []
        it = None
        for scope in self.scopechain:
            l = scope.tocode()
            if l:
                ret.append(l)
            if it is not None:
                ret.append(it)
            if l:
                # ret.append('.')
                # ret.append('_dot_')
                ret.append('_')
            if scope.scopetype == 'for' and scope.scopeloop is not None:
                #it = '[' + str(scope.scopeloop) + ']'
                #it = '_L_' + str(scope.scopeloop) + '_R_'
                it = '_' + str(scope.scopeloop) + '_'
            else:
                it = None
        ret = ret[:-1]
        return ''.join(ret)

    def get_module_list(self):
        return [scope for scope in self.scopechain if scope.scopetype == 'module']

    def __repr__(self):
        ret = ''
        for scope in self.scopechain:
            l = scope.__repr__()
            ret += l + '.'
        ret = ret[:-1]
        return ret

    def __len__(self):
        return len(self.scopechain)

    def __eq__(self, other):
        if type(self) != type(other):
            return False
        return self.scopechain == other.scopechain

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash(tuple(self.scopechain))

    def __getitem__(self, key):
        if isinstance(key, slice):
            indices = key.indices(len(self))
            return ScopeChain([self.scopechain[x] for x in range(*indices)])
        return self.scopechain[key]

    def __iter__(self):
        for scope in self.scopechain:
            yield scope
