#! /usr/bin/python
import matplotlib.pyplot as plt
import numpy as np
import sys

def read_data(file_name):
    File = open(file_name, 'r')
    data = map(list, zip(*map(lambda x: x.strip('\n').split('\t')[1:], File.readlines()[:-5])))
    File.close()
    data[5:] = map(lambda x: map(lambda y: float(y)/1000, x), data[5:])
    return data

if len(sys.argv) != 2:
    print "Usage: %s <data_file>" % sys.argv[0]
    sys.exit(-1)

data = read_data(sys.argv[1])

def cactus_plot(data, *args, **kwargs):
    data = sorted(data)
    X = [0]
    Y = [0]
    val = data[0]
    for i in range(1,len(data)):
        if data[i] != val:
            X.append(i-1)
            Y.append(val)
            val = data[i]
        if val >= 600:
            break;
    if val < 600:
        X.append(len(data))
        Y.append(val)
    plt.plot(X, Y, *args, **kwargs)

cactus_plot(data[5], '-bs', label='Min Var')
cactus_plot(data[6], '-gv', label='Max Conflicts')
cactus_plot(data[7], '-yo', label='Gecode')
cactus_plot(data[8], '-m*', label='OrTools')
cactus_plot(data[9], '-cd', label='HaifaCSP')
# s - square, v ^ < > - triangles, o - circe, p - pentagon, * - star, h H - hexagon, x - x, d D - diamond

plt.xlabel('Instances Solved')
plt.ylabel('Time (s)')
plt.legend(bbox_to_anchor=(0.38,1.0), loc=2)
plt.show()
