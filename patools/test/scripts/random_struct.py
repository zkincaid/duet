import random
import sys

universe = int(sys.argv[1])
predicates = int(sys.argv[2])
p_predicate = float(sys.argv[3])
p_edge = float(sys.argv[4])

comma = False
sys.stdout.write("{")
for i in range(1, universe):
    trivial = True
    while trivial:
        for p in range(1, predicates):
            if random.uniform(0.0,1.0) <= p_predicate:
                if comma:
                    sys.stdout.write(", ")
                sys.stdout.write("p%d(%d)" % (p, i))
                comma = True
                trivial = False

for i in range(1, universe):
    for j in range(1, universe):
            if random.uniform(0.0,1.0) <= p_edge:
                if comma:
                    sys.stdout.write(", ")
                sys.stdout.write("link(%d, %d)" % (i, j))
                comma = True

sys.stdout.write("}\n")
sys.stdout.flush()
