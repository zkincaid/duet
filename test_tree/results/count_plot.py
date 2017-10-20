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

if len(sys.argv) != 3:
    print "Usage: %s <data_file> <time_out>" % sys.argv[0]
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

plot(data[1], '-bs', label='MatchEmbeds + Tree')
plot(data[2], '-yo', label='MatchEmbeds + List')
plot(data[3], '-m*', label='Gecode + Tree')
plot(data[4], '-gd', label='Gecode + Llist')
plot(data[5], '-cp', label='Haifa + Tree')
plot(data[6], '-kh', label='Haifa + List')
plot(data[7], '-v', color="orange", label='OrTools + List')
plot(data[8], '-<', color="pink", label='OrTools + List')
# s - square, v ^ < > - triangles, o - circe, p - pentagon, * - star, h H - hexagon, x - x, d D - diamond

plt.xlabel('Number of Threads')
plt.ylabel('Time (s)')
plt.ylim((0,TO))
#plt.yscale('log')
#plt.legend(bbox_to_anchor=(0.38,1.0), loc=2)
plt.legend(loc=0, fontsize=11)
plt.show()
