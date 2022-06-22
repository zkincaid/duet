import argparse
import os
import re
from pathlib import Path
from string import Template

template = Template("""
format_version: '1.0'

input_files: '$fname'

properties:
  - property_file: ../../properties/sat.prp
    expected_verdict: $verdict
""")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--folder', type=Path)
    p = parser.parse_args()
    dir = p.folder
    if dir is not None:
        print(dir)
        directory = os.fsencode(dir)
        for root, _, files in os.walk(dir):
            for file in files:
                if file.endswith(".smt2"):
                    with open(os.path.join(root,file)) as f:
                        for line in f:
                            r = re.search("set-info\s+:status\s+(sat|unsat|unknown)", line)
                            if r:
                                status = r.group(1)
                                name = os.path.splitext(file)[0]
                                str = template.safe_substitute(fname = file, verdict = status)
                                with open(os.path.join(root, name + '.yml'), 'w') as out:
                                    out.write(str)
                                break


if __name__ == '__main__':
    main()
    