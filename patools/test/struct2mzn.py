#! /usr/bin/python2.7

import sys, re
from sets import Set
from timeit import timeit
import subprocess

def parse(file_name):
    File = open(file_name, 'r')
    data = "".join(["".join(line.split()) for line in File.readlines()]) # Remove All White Space
    File.close()

    data = re.sub(re.compile(r'\(\*.*?\*\)'), '', data)
    data = [datum.split("}")[0] for datum in data.split("{")][1:]
    return map(parse_struct, data)

def parse_struct(data):
    data = data.split(',')
    last = ""
    DATA = []
    for datum in data:
        if last != "":
            DATA.append("".join([last, ",", datum]))
            last = ""
        else:
            if datum.find('(') != -1 and datum.find(')') == -1:
                last = datum
            else:
                DATA.append(datum)
    return map(parse_prop, DATA)

def parse_prop(data):
    data = data.strip(')').split('(')
    data.append("")
    data[1] = [int(x) for x in data[1].split(',') if x != '']
    return (data[0], data[1])

if len(sys.argv) != 2:
    print "Usage: python", sys.argv[1], "<struct_file>"
    exit(1)

structs = parse(sys.argv[1])
if len(structs)%2 == 1:
    print "Error: number of input structures must be even"
    exit(1)

def unique(l):
    seen = {}
    result = []
    for item in l:
        if item in seen: continue
        seen[item] = 1
        result.append(item)

def sigs(struct):
    sigs = {}
    for (pred, args) in struct:
        for i in xrange(len(args)):
            if args[i] in sigs:
                sigs[args[i]].add((pred, i))
            else:
                sigs[args[i]] = Set([(pred, i)])
    return sigs
    
for Si in xrange(0, len(structs), 2):
    SigsC = sigs(structs[Si])
    SigsD = sigs(structs[Si+1])

    f = open('tmp.mzn', 'w')
    fail_early = False
    f.write("include \"alldifferent.mzn\";\n\n")
    for (i, sigC) in SigsC.iteritems():
        D = []
        for (j, sigD) in SigsD.iteritems():
            if sigC.issubset(sigD):
                D.append(j)
        if len(D) == 0:
            fail_early = True
            break
        f.write("var 1..%d: x%d;\n" % (len(D), i))
        f.write("array [1..%d] of int: Dx%d = %s;\n\n" % (len(D), i, D))

    f.write("constraint alldifferent([%s]);\n\n" %(",".join(["Dx%d[x%d]" % (i, i) for i in SigsC.keys()])))
    for (predC, argsC) in structs[Si]:
        if len(argsC) < 2: continue
        Cons = []
        for (predD, argsD) in structs[Si+1]:
            if predD != predC: continue
            C = []
            for i in xrange(len(argsC)):
                C.append("Dx%d[x%d] = %d" % (argsC[i], argsC[i], argsD[i]))
            Cons.append("("+" /\\ ".join(C)+")")
        f.write("constraint %s;\n\n" % " \\/ ".join(Cons))

    f.write("solve satisfy;\n\n")

    f.write("output[%s];\n" %(",\n".join(["\"x%d = \", show(Dx%d[x%d]), \"\\n\"" % (i, i, i) for i in SigsC.keys()])))
    f.close()

    if not fail_early:
#        print "%fs" % timeit(stmt = "subprocess.call([\"./run_minizinc.sh\", \"./tmp.mzn\"])",
#                             setup = "import subprocess", number = 1)
        subprocess.call(["./run_minizinc.sh", "./tmp.mzn"]) 
    else:
        print "False0"
