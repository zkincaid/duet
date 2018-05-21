#!/bin/bash
import subprocess, os
import matplotlib
import matplotlib.pyplot as plt

import networkx as nx
from fractions import Fraction

matplotlib.rcParams['mathtext.fontset'] = 'stix'

NI = float("-inf")
outputdir = "output/"
outputfilename = "max-plus-examples.tex"

try : os.mkdirs(outputdir)
except : pass

os.chdir(outputdir)

# get rid of pointless matplotlib warning:
import warnings
warnings.filterwarnings("ignore", category=DeprecationWarning) 

doctemplate = (
r"""
\title{\vspace{-10ex}Max-Plus: Some Examples}
\author{
        Jason Breck
}
\date{\today}

\documentclass[12pt]{article}

\usepackage[margin=0.5in]{geometry}

\usepackage{listings}
\usepackage{amsmath}
\usepackage{color}
\usepackage{graphicx}
\usepackage{wrapfig}
\usepackage{fancyvrb}

\newcommand{\vecf}[0]{\textbf{f}}
\newcommand{\vecx}[0]{\textbf{x}}
\newcommand{\ttimes}[0]{{\color{red}\boldsymbol\otimes}}
\newcommand{\tplus}[0]{{\color{red}\boldsymbol\oplus}}

\setcounter{MaxMatrixCols}{20}

\begin{document}
%% \maketitle

%% Warning: this document is auto-generated and should not be edited manually!

%s

\end{document}

""")

def latnum(number) :
    if number == NI : return r"-\infty"
    return str(number)

#def create_plot(x,y,filename,xlabel,ylabel) :
#    #plt.rc('text', usetex=True)
#    #plt.rc('font', family='serif')
#    plt.plot(x,y, marker='o')
#    plt.xlabel(xlabel)
#    plt.ylabel(ylabel)
#    plt.savefig(filename,bbox_inches='tight')
#    plt.close()

def pngname(loopname) : return "loop_trace_" + loopname + ".png"
def pdfname(loopname) : return "loop_trace_" + loopname + ".pdf"

def extract_last_variable(trace) :
    return [ var[-1] for var in trace ]

def varname(i) : return chr(ord("a")+i) # zero-based
def plusterm(var, additive) :
    if additive == NI : raise Exception("Don't call plusterm with -inf additive")
    if additive == 0 : return varname(var)
    if additive < 0 : return varname(var) + " - " + str(-additive)
    return varname(var) + " + " + str(additive)
def maxterm(row) :
    non_NI = [I for I, ENTRY in enumerate(row) if ENTRY != NI] # entries != -inf
    if len(non_NI) == 0 : raise Exception("No matrix row should have only -inf entries")
    if len(non_NI) == 1 : return plusterm(non_NI[0],row[non_NI[0]])
    return "max(" + ", ".join(plusterm(I,row[I]) for I in non_NI) + ")"
def assignment(var, row) :
    if all((E == NI and V != var) or (E == 0 and V == var) for V,E in enumerate(row)) :
        return "" # var = var; i.e., the var is not updated in the loop; no code needed!
    return varname(var) + "_new = " + maxterm(row) + ";"
def generate_loop_code(initial, matrix) :
    if len(initial) <= 8 : 
        S = lambda x:" "+x+" " # put space surrounding text
        A = lambda x:x+" "     # put space after text
    else :
        S = lambda x:x
        A = lambda x:x
    indent = "    "
    output = ""
    output += "{ \small \n"
    output += "\\begin{lstlisting}\n"
    for var, value in enumerate(initial) :
        output += varname(var) + S("=") + str(value) + A(";")
    output += "\n"
    output += "while(*) { \n"
    updated = list()
    for var, row in enumerate(matrix) :
        assign = assignment(var, row)
        if assign : 
            output += indent + assign + "\n"
            updated.append(var)
    output += "\n"
    output += indent
    for i, var in enumerate(updated) :
        output += varname(var) + S("=") + varname(var) + A("_new;")
        if i % 10 == 9 : output += "\n"+indent
    output += "\n"
    output += "}\n"
    output += "\\end{lstlisting}\n"
    output += " }\n "
    return output

def multiply(matrix, vector) :
    newvalues = list()
    for i, row in enumerate(matrix) :
        value = NI
        for j, entry in enumerate(row) :
            value = max(value, entry + vector[j])
        newvalues.append(value)
    return newvalues

class SimpleMaxPlusMatrixLoop(object) :
    def __init__(self, name, matrix, K, initial) :
        self.name = name
        self.matrix = matrix
        self.initial = initial
        self.K = K
        self.trace = list()
        self.summaryPoints = list()
        self.summaryText = "<no summary yet>"
    def run(self) :
        self.trace = list()
        values = self.initial[:]
        self.trace.append(values)
        for k in range(self.K) :
#            nextvalues = list()
#            for i, row in enumerate(self.matrix) :
#                value = NI
#                for j, entry in enumerate(row) :
#                    value = max(value, entry + values[j])
#                nextvalues.append(value)
#            values = nextvalues
            values = multiply(self.matrix, values)
            self.trace.append(values)
    def computeSummaryPoints(self) :
        lastVar = len(self.initial)-1 # This is the one variable whose value we plot
        self.summaryPoints = list()
        for k in range(self.K+1) : # number of iterations
            # This list holds the maxands of the summary for the last variable
            summaryRow = list()
            for iInitial in range(len(self.initial)) : # which initial variable
                summaryValue = (self.bounding_intercept[lastVar,iInitial] 
                                + k * self.bounding_slope[lastVar,iInitial]
                                + self.initial[iInitial])
                summaryRow.append(summaryValue)
            self.summaryPoints.append(summaryRow)
    def createSummary(self) :
        self.summaryText = ""
        # * 1. Construct a graph representation of the loop body matrix
        G = nx.DiGraph()
        print ""
        print "*** EXAMPLE *** " + self.name 
        print "MATRIX: "
        for i, row in enumerate(self.matrix) :
            print row
            for j, entry in enumerate(row) :
                if entry != NI : 
                    G.add_edge(i,j,weight=entry)
        print ""
        #
        # * 2. Compute the condensation of our graph
        condensation = nx.condensation(G)
        componentContaining = dict()
        componentContents = dict()
        componentsInTopologicalOrder = list()
        for iComponent in reversed(list(nx.topological_sort(condensation))) :
            component = list(condensation.nodes()[iComponent]['members'])
            for node in component : componentContaining[node] = iComponent
            componentContents[iComponent] = component
            componentsInTopologicalOrder.append(iComponent)
        #
        # * 3. Compute critical circuit average weights (a.k.a. "critical weights")
        critical_weight = dict()
        for iComponent in componentContents.keys() :
            critical_weight[iComponent] = NI
        for cycle in nx.simple_cycles(G) :
            #print "CYCLE"
            weight = 0
            prevNode = cycle[-1]
            for nextNode in list(cycle) :
                #print (prevNode,nextNode)
                w = G.get_edge_data(prevNode,nextNode)['weight']
                #print w
                weight += w
                prevNode = nextNode
            average = Fraction(weight, len(cycle))
            #print "Cycle " + str(cycle) + " has average weight " + str(average)
            node = cycle[0]
            iComponent = componentContaining[node]
            if critical_weight[iComponent] < average : 
                critical_weight[iComponent] = average
        #
        # * 4. Compute the bounding slopes:
        #    
        #     First, initialize the values
        N = len(self.initial) # number of variables
        bounding_slope = dict()
        for iFrom in range(N) :
            for iTo in range(N) :
                bounding_slope[iTo,iFrom] = NI
        #
        #     The bounding slope in position (i,k) is the highest critical weight that is found
        #       in any circuit that is reachable from i and that can reach k.
        #     So, we loop over each SCC (call it j),
        #       find all upstream SCCs (call each such i),
        #       and downstream SCCs (call each such k);
        #       then, what we have is (SCC_i) --*--> (SCC_j) --*--> (SCC_k)
        #     Each time we find such a j, we update our slope for (i,k) to be j's critical weight
        #       if j's critical weight is greater than our current slope for (i,k).
        for jComponent in componentsInTopologicalOrder :
            downstreamComponents = list(nx.descendants(condensation,jComponent)) + [jComponent]
            upstreamComponents = list(nx.ancestors(condensation,jComponent)) + [jComponent]
            for iComponent in upstreamComponents :
                for iVariable in componentContents[iComponent] :
                    for kComponent in downstreamComponents :
                        for kVariable in componentContents[kComponent] :
                            bounding_slope[iVariable,kVariable] = max(
                                    bounding_slope[iVariable,kVariable],
                                    critical_weight[jComponent])
        #
        # * 5. Compute the bounding intercepts (perform the "intercept propagation" steps)
        bounding_intercept = dict()
        for iFrom in range(N) :
            for iTo in range(N) :
                bounding_intercept[iTo,iFrom] = 0 if iTo == iFrom else NI
        for iInput in range(N) : 
            for iIteration in range(N) :
                for iTo in range(N) :
                    for iFrom in range(N) :
                        bounding_intercept[iTo,iInput] = max(bounding_intercept[iTo,iInput],
                               ( bounding_intercept[iFrom,iInput]  # var_iFrom's intercept
                                 + self.matrix[iTo][iFrom]         # + edge weight
                                 - bounding_slope[iTo,iInput] )    # - slope
                             )
        #
        # * Print our loop summary:
        print "Bounding summary:"
        TCR_L = "\\textcolor{red}{"
        TCR_R = "}"
        for iTo in range(N) :
            lhs = "  " + varname(iTo) + "[K]"
            var_summary = lhs + " <= "
            maxands = list()
            for iFrom in range(N) :
                if bounding_slope[iTo,iFrom] != NI and bounding_intercept[iTo,iFrom] != NI:
                    if bounding_slope[iTo,iFrom] == 0 : bs = ""
                    else : bs = " + (K * " + str(bounding_slope[iTo,iFrom]) + ")"
                    if bounding_intercept[iTo,iFrom] == 0 : bi = ""
                    else : bi = " + " + str(bounding_intercept[iTo,iFrom])
                    maxands.append(varname(iFrom) + "[0]" + bs + bi)
            nl_indent = "\n             "
            if len(maxands) == 0 : 
                rhs = "???"
                rhs2 = TCR_L + rhs + TCR__R 
                raise Exception("No max-terms in bounding summary; illegal input matrix, maybe?")
            elif len(maxands) == 1 : 
                rhs = maxands[0]
                rhs2 = TCR_L + rhs + TCR_R 
            else :
                #rhs += "max("+nl_indent+" "+(","+nl_indent+" ").join(maxands)+nl_indent+")"
                rhs = "max("+(","+nl_indent+" ").join(maxands)+")"
                rhs2 = ("max(" + (","+nl_indent+" ").join(TCR_L + M + TCR_R for M in maxands) + ")")
            print lhs + " <= " + rhs
            if iTo < N - 1 :
                self.summaryText += lhs + " <= " + rhs + "\n"
            else :
                self.summaryText += "\\textcolor{blue}{" + lhs + "} <= " + rhs2 + "\n"

        #
        # * Save summary for later use
        self.bounding_slope = bounding_slope
        self.bounding_intercept = bounding_intercept
        
    def analyze(self) :
        self.createSummary()
        self.computeSummaryPoints()
    def document(self) :
        output = ""
        output += r"\subsection{Example: "+self.name+"}"
        output += generate_loop_code(self.initial, self.matrix)
        output += """\
\\[
  \\vecx^{[K+1]} = \\begin{bmatrix}"""
        output += "\\\\\n".join(" & ".join(latnum(E) for E in R) for R in self.matrix)
        output += """\
                \\end{bmatrix} \\ttimes ~\\vecx^{[K]} \qquad \\vecx^{[0]} = \\begin{bmatrix} """
        output += " \\\\ ".join(latnum(E) for E in self.initial)
        output += """ \\end{bmatrix} \
\\]
"""
        self.analyze()
        pdf = pdfname(self.name)
        self.plot(pdf)
        #output += r"\includegraphics[width=0.9\textwidth]{"+pdf+"}"
        #output += r"\begin{wrapfigure}{r}{0.5\textwidth}"+"\n"
        output += r"\begin{minipage}{0.65\textwidth}"+"\n"
        output += r"\includegraphics[width=\textwidth]{"+pdf+"}"+"\n"
        #output += r"\includegraphics[width=0.7\textwidth]{"+pdf+"}"+"\n"
        output += r"\end{minipage}"+"\n"
        output += r"\begin{minipage}{0.34\textwidth}"+"\n"
        #output += "Hello, world, I am some text."+"\n"
        #output += r"\verbatimfont{\small}%"+"\n"
        output += r"\begin{Verbatim}[fontsize=\footnotesize,commandchars=\\\{\}]"+"\n"
        #output += "Hello, world, I am some text."+"\n"
        output += "UPPER BOUND SUMMARY:\n\n"
        output += self.summaryText
        output += r"\end{Verbatim}"+"\n"
        output += r"\end{minipage}"+"\n"
        #output += r"\end{wrapfigure}"+"\n"
        return output
    def plot(self, filename) :
        x = range(len(self.trace))
        y = extract_last_variable(self.trace)
        #filename = filename
        xlabel = "iteration number (K)"
        #"last variable $(x_"+str(len(self.initial))+")$")
        ylabel = "last variable ("+varname(len(self.initial)-1)+")"
        #
        plt.plot(x,y, marker='o')
        #
        for iInitial in range(len(self.initial)) : # which initial variable
            x = list()
            y = list()
            for k in range(self.K+1) : # number of iterations
                x.append(k)
                y.append(self.summaryPoints[k][iInitial])
            plt.plot(x,y,color='r')
        #
        axes = plt.gca()
        ymin, ymax = axes.get_ylim()
        axes.set_ylim([ymin-1,ymax+1])
        axes.set_xlim([0,self.K])
        #
        plt.xlabel(xlabel)
        plt.ylabel(ylabel)
        plt.savefig(filename,bbox_inches='tight')
        plt.close()
        #create_plot(range(len(self.trace)),
        #            extract_last_variable(self.trace),
        #            filename,
        #            "iteration number", 
        #            #"last variable $(x_"+str(len(self.initial))+")$")
        #            "last variable ("+varname(len(self.initial)-1)+")")

###############################################################################

# Random goofy thought:
#   We could integrate with ICRA by having ICRA use its closed forms
#   to compute an affine upper bound for some other variable and then
#   using that upper bound inside this model...

###############################################################################


output = """
\section{Examples}
"""
loop = SimpleMaxPlusMatrixLoop(
          "knee-1",
          [[  0, NI, NI],
           [-14,  3, NI],
           [ NI,  0, 1]],
          15,
          [0, -90, 0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "knee-2b",
          [[ 5, NI, NI, NI, NI, NI],
           [ 0,  0, NI, NI, NI, NI],
           [NI,  0,  0, NI, NI, NI],
           [NI, NI,  0,  0, NI, NI],
           [NI, NI, NI,  0,  0, NI],
           [NI, NI, NI, NI,  0,  1]],
          12,
          [0,-50,-51,-52,-53, 0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "knee-3",
          [[-2, NI, NI, NI, NI, NI],
           [-2, -2, NI, NI, NI, NI],
           [NI, -2, -2, NI, NI, NI],
           [NI, NI, -2, -2, NI, NI],
           [NI, NI, NI, -2, -2, NI],
           [NI, NI, NI, NI, -2, -5]],
          12,
          [0,-50,-50,-50,-50, 0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "knee-4b",
          [[-2, NI, NI, NI, NI, NI],
           [ 0, -2, NI, NI, NI, NI],
           [NI,  0, -2, NI, NI, NI],
           [NI, NI,  0, -2, NI, NI],
           [NI, NI, NI,  0, -2, NI],
           [NI, NI, NI, NI,  0, -5]],
          12,
          [0,-50,-50,-50,-50, 0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "knee-5",
          [[-1, NI, NI, NI, NI, NI],
           [ 0, -9, NI, NI, NI, NI],
           [NI,  0, -9, NI, NI, NI],
           [NI, NI,  0, -9, NI, NI],
           [NI, NI, NI,  0, -9, NI],
           [NI, NI, NI, NI,  0,-20]],
          12,
          [0,-50,-50,-50,-50, 0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "zigzag-1b",
          [[ 0, NI, NI,  8],
           [ 0,  0, NI, NI],
           [NI,  0,  0, NI],
           [NI, NI,  0,  1]],
          20,
          [0,-50,-50, 0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "zigzag-2b",
          [[NI, NI, NI,  7],
           [ 0, NI, NI, NI],
           [NI,  0, NI, NI],
           [NI, NI,  1, NI]],
          15,
          [0, 1,  -8, 0])
loop.run()
output += loop.document()


#output += "\\newpage\n"
#loop = SimpleMaxPlusMatrixLoop(
#          "zigzag-3",
#          [[NI, NI, NI,  9],
#           [ 0, NI, NI, NI],
#           [NI,  0, NI, NI],
#           [NI, NI,  1, NI]],
#          15,
#          [2, 0, 0, 2])
#loop.run()
#output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "zigzag-3",
          [[ NI, NI, NI, -3],
           [ -1, NI, NI, NI],
           [ NI, -1, NI, NI],
           [ NI, NI,-15, NI]],
          20,
          [-2, -2, -2, 0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "zigzag-4",
          [[NI, -1],
           [ 1, NI]],
          15,
          [0, 0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "zigzag-5",
          [[ NI,  2, NI, NI, NI],
           [  0, NI, NI, NI, NI],
           [ NI, NI, NI, 10, NI],
           [ NI, NI,  0, NI, NI],
           [  0, NI, NI,  0, NI]],
          60,
          [0,-150,0,-150,  0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "zigzag-6",
          [[-20, NI, NI, 80],
           [-20,-20, NI, NI],
           [ NI,-20,-20, NI],
           [ NI, NI,-20,-19]],
          20,
          [15,-5,-5, 0])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "oddball-1",
          [[ NI, -1, NI, NI],
           [ -1, NI, NI, -2],
           [ NI, -2, NI, NI],
           [ NI, NI, -2, NI]],
          20,
          [0,-50,-50,-50])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "oddball-2",
          [[  0, NI, NI],
           [-14,  3, NI],
           [-50,  0, NI]],
          15,
          [0, -10, -30])
loop.run()
output += loop.document()


output += "\\newpage\n"
loop = SimpleMaxPlusMatrixLoop(
          "expo-1",
          [[ NI,  1, NI, NI, NI, NI, NI, NI, NI, NI, NI],
           [  1, NI, NI, NI, NI, NI, NI, NI, NI, NI, NI],
           [ NI, NI, NI, NI,  1, NI, NI, NI, NI, NI, NI],
           [ NI, NI,  1, NI, NI, NI, NI, NI, NI, NI, NI],
           [ NI, NI, NI,  1, NI, NI, NI, NI, NI, NI, NI],
           [ NI, NI, NI, NI, NI, NI, NI, NI, NI,  1, NI],
           [ NI, NI, NI, NI, NI,  1, NI, NI, NI, NI, NI],
           [ NI, NI, NI, NI, NI, NI,  1, NI, NI, NI, NI],
           [ NI, NI, NI, NI, NI, NI, NI,  1, NI, NI, NI],
           [ NI, NI, NI, NI, NI, NI, NI, NI,  1, NI, NI],
           [  0, NI,  0, NI, NI,  0, NI, NI, NI, NI, NI]],
          90,
          [0,9,5,13,10,11,1,12,4,12,8])
loop.run()
output += loop.document()

with open(outputfilename,"w") as outputfile :
    outputfile.write(doctemplate % output)

subprocess.call(["pdflatex", outputfilename])


