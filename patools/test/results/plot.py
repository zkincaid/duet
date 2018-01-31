#! /usr/bin/python
import matplotlib.pyplot as plt
import numpy as np
import sys

def read_data(file_name, cols):
    File = open(file_name, 'r')
    data = map(list, zip(*map(lambda x: x.strip('\n').split('\t')[1:], File.readlines()[:-cols])))
    File.close()
    data[cols:] = map(lambda x: map(lambda y: float(y)/1000, x), data[cols:])
    t = [1 if x == "True" else 0 for x in data[0]]
    f = [1 if x == "False" else 0 for x in data[0]]
    n = [1 if x == "--" else 0 for x in data[0]]
    print reduce(lambda x, y: x + y, t)
    print reduce(lambda x, y: x + y, f)
    print reduce(lambda x, y: x + y, n)
    return data

if len(sys.argv) < 4:
    print "Usage: %s <data_file> <time_out> <num_cols> [solver list, ...]" % sys.argv[0]
    print "\t1 : MatchEmbeds"
    print "\t2 : CryptoMiniSat"
    print "\t3 : Lingeling"
    print "\t4 : HaifaCSP"
    print "\t5 : Gecode"
    print "\t6 : VF2"
    print "\t7 : OrTools"
    sys.exit(-1)

cols = int(sys.argv[3])
data = read_data(sys.argv[1], cols)
TO = int(sys.argv[2])

def cactus_plot(data, *args, **kwargs):
    data = [x for x in sorted(data) if x < TO]
    print len(data)
    X = [0]
    Y = [data[0]]
    val = data[0]
    for i in range(1,len(data)):
        if data[i] != val:
            X.append(i)
            Y.append(val)
            val = data[i]
    X.append(len(data))
    Y.append(val)
    plt.plot(X, Y, *args, **kwargs)

solver = [("MatchEmbeds","s", "b"),
          ("CryptoMiniSat","o", "y"),
          ("Lingeling","h", "r"),
          ("HaifaCSP","*", "m"),
          ("Gecode","d", "c"),
          ("VF2","^", "g"),
          ("OrTools","p", "orange")]
# s - square, v ^ < > - triangles, o - circe, p - pentagon, * - star, h H - hexagon, x - x, d D - diamond

solvers = [i for i in range(cols)]
if len(sys.argv) > 4:
    solvers = sys.argv[4:]

for i in range(len(solvers)):
    data_ind = cols+i
    (label, marker, color) = solver[int(solvers[i])]
    cactus_plot(data[data_ind], '-', marker=marker, color=color, label=label)

plt.xlabel('Instances Solved')
plt.ylabel('Time (s)')
plt.ylim((0,TO))
#plt.yscale('log')
#plt.legend(bbox_to_anchor=(0.38,1.0), loc=2)
plt.legend(loc=0, ncol=1, prop={'size': 14})
plt.show()
