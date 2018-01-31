#! /usr/bin/python
import matplotlib.pyplot as plt
import numpy as np
import sys
import re

def read_data(file_name):
    File = open(file_name, 'r')
    splitter = r'\t+'
    data = map(list, zip(*map(lambda x: re.split(splitter, x.strip('\n')), File.readlines()[1:])))
    data[1:] = map(lambda x: map(lambda y: float(y.split(" ")[0]), x), data[1:])
    return data

if len(sys.argv) < 3:
    print "Usage: %s <data_file> <time_out> [solver list, ...]" % sys.argv[0]
    print "\t1 : MatchEmbeds"
    print "\t2 : CryptoMiniSat"
    print "\t3 : Lingeling"
    print "\t4 : HaifaCSP"
    print "\t5 : Gecode"
    print "\t6 : VF2"
    print "\t7 : OrTools"
    sys.exit(-1)

data = read_data(sys.argv[1])
TO = int(sys.argv[2])

def plot(data, *args, **kwargs):
    vals = [5,6,7,8,9,10,11,12,13,14,15,20,25,30,35,40,45,50,55,60,65,70,75,80,85,90,95,100]
    X = [0]
    Y = [data[0]]
    for i in range(1,len(data)):
        if data[i] > TO:
            break
        X.append(vals[i])
        Y.append(data[i])
    plt.plot(X, Y, *args, **kwargs)

solver = [("MatchEmbeds","s", "b"),
          ("CryptoMiniSat","o", "y"),
          ("Lingeling","h", "r"),
          ("HaifaCSP","*", "m"),
          ("Gecode","d", "c"),
          ("VF2","^", "g"),
          ("OrTools","p", "orange")]
# s - square, v ^ < > - triangles, o - circe, p - pentagon, * - star, h H - hexagon, x - x, d D - diamond

solvers = [i for i in range(len(data)/2)]
if len(sys.argv) > 3:
    solvers = map(int,sys.argv[3:])

if len(data) < 2*len(solvers):
    print "Too few data columns provided for number solvers listed"
    sys.exit(-1)

for i in range(len(solvers)):
    (label, marker, color) = solver[solvers[i]]
    plot(data[2*i+1], '-', marker=marker, color=color, label=label+'+Tree')
    plot(data[2*(i+1)], '--', marker=marker, color=color, label=label+'+List')

plt.xlabel('Number of Threads')
plt.ylabel('Time (s)')
plt.ylim((0,TO))
#plt.yscale('log')
#plt.legend(bbox_to_anchor=(0.38,1.0), loc=2)
plt.legend(loc=0, ncol=1, fontsize=10)
plt.show()
