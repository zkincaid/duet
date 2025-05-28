import argparse
import xml.etree.ElementTree as ET
import os

def parse(infile, outfile):
    tree = ET.parse(infile)
    print(f"opening file {infile}")
    root = tree.getroot()
    to_find = "failure (SubspaceConeAccelerated"
    sc_more_precise = []
    for run in root:
        if run.tag == "run":
            for column in run:
                if column.tag == "column" \
                and column.attrib["title"] == "status" \
                and to_find in column.attrib["value"]:
                    sc_more_precise = sc_more_precise + [run.attrib["name"]]
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
