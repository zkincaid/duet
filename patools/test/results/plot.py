#! /usr/bin/python
import matplotlib.pyplot as plt
import numpy as np
import sys

def read_data(file_name):
    File = open(file_name, 'r')
    data = map(list, zip(*map(lambda x: x.strip('\n').split('\t')[1:], File.readlines()[:-4])))
    File.close()
    data[4:] = map(lambda x: map(lambda y: float(y)/1000, x), data[4:])
    return data

if len(sys.argv) != 3:
    print "Usage: %s <data_file> <time_out>" % sys.argv[0]
    sys.exit(-1)

data = read_data(sys.argv[1])
TO = int(sys.argv[2])

def cactus_plot(data, *args, **kwargs):
    data = [x for x in sorted(data) if x < TO]
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

cactus_plot(data[4], '-bs', label='Embeds')
cactus_plot(data[5], '-yo', label='Gecode')
cactus_plot(data[6], '-m*', label='OrTools')
cactus_plot(data[7], '-gd', label='HaifaCSP')
# s - square, v ^ < > - triangles, o - circe, p - pentagon, * - star, h H - hexagon, x - x, d D - diamond

plt.xlabel('Instances Solved')
plt.ylabel('Time (s)')
plt.yscale('log')
#plt.legend(bbox_to_anchor=(0.38,1.0), loc=2)
plt.legend(loc=0)
plt.show()
