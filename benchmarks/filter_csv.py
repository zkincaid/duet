import argparse
import xml.etree.ElementTree as ET
import os

def parse(infile, outfile):
    print(f"opening file {infile}")
    to_find = "failure (SubspaceConeAccelerated"
    sc_more_precise = []
    with open(infile) as f:
        for line in f:
            if 'failure' in line:
                print(line.split("\t")[0])
    out = open(outfile, "a")
    for filename in sc_more_precise:
        path = os.path.relpath(filename, start="../tasks/convhull")
        out.write(f"{path}\n")
    out.close()

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--infile")
    parser.add_argument("--outfile")
    args = parser.parse_args()
    parse(args.infile, args.outfile)
