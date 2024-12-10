# -------------------------------------------------------------------------------
# graphgen.py
#
# Dataflow graph generator (Only Python 2.7)
#
# pygraphviz and graphviz are required
#
# Copyright (C) 2013, Shinya Takamaeda-Yamazaki
# License: Apache 2.0
# -------------------------------------------------------------------------------
from __future__ import absolute_import
from __future__ import print_function

import subprocess
import sys
import os
import pygraphviz as pgv
from optparse import OptionParser

# the next line can be removed after installation
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import pyverilog
from pyverilog.dataflow.dataflow_analyzer import VerilogDataflowAnalyzer
from pyverilog.dataflow.optimizer import VerilogDataflowOptimizer
from pyverilog.dataflow.graphgen import VerilogGraphGenerator

"""
    filelist = ["/Users/hzs/code/pycharm/Pyverilog/verilogcode/vga.v"]
    topmodule = "top"
    output="vga.dot"
"""

"""
    filelist = ["/Users/hzs/code/pycharm/Pyverilog/verilogcode/det1011.v"]
    topmodule = "top"
    output="det1011.dot"
"""

def main():

    # filelist = ["/Users/hzs/code/pycharm/Pyverilog/verilogcode/case_if.v"]
    type = "rs232"
    filelist = [f"/Users/hzs/code/pycharm/Pyverilog/verilogcode/{type}.v"]
    topmodule = "top"
    output=f"{type}.dot"

    for f in filelist:
        if not os.path.exists(f):
            raise IOError("file not found: " + f)

    analyzer = VerilogDataflowAnalyzer(filelist, topmodule)
    analyzer.generate()

    directives = analyzer.get_directives()
    terms = analyzer.getTerms()
    binddict = analyzer.getBinddict()

    optimizer = VerilogDataflowOptimizer(terms, binddict)

    optimizer.resolveConstant()
    resolved_terms = optimizer.getResolvedTerms()
    resolved_binddict = optimizer.getResolvedBinddict()
    constlist = optimizer.getConstlist()

    graphgen = VerilogGraphGenerator(topmodule, terms, binddict,
                                     resolved_terms, resolved_binddict, constlist, output)
    signals = [str(bind) for bind in graphgen.binddict]

    for num, signal in enumerate(sorted(signals, key=str.casefold), start=1):
        graphgen.generate(signal, walk=False)
    # for target in searchtarget:
    #     graphgen.generate(target)

    graphgen.draw()
    subprocess.call(["xdot", output])


if __name__ == '__main__':
    main()
