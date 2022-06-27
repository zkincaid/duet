import argparse
import os
import re
from pathlib import Path
from string import Template
import shutil
from random import sample
import random

template = Template("""
format_version: '1.0'

input_files: '$fname'

properties:
  - property_file: ../../properties/sat.prp
    $verdict
    
""")

random.seed(20220607)

def flatten(directory):
    for dirpath, _, filenames in os.walk(directory, topdown=False):
        for filename in filenames:
            if not filename.endswith(".smt2"):
                os.remove(os.path.join(dirpath, filename))
                continue
            source = os.path.join(dirpath, filename)
            target = os.path.join(directory, filename)
            shutil.move(source, target)
        if dirpath != str(directory):
            os.rmdir(dirpath)
            
def create_ymls(dir):
    for root, _, files in os.walk(dir):
        print(root)
        for file in files:
            print(file)
            if file.endswith(".smt2"):
                with open(os.path.join(root,file)) as f:
                    for line in f:
                        r = re.search("set-info\s+:status\s+(sat|unsat|unknown)", line)
                        if r:
                            status = r.group(1)
                            if status == 'unsat':
                                v = 'expected_verdict: false'
                            elif status == 'sat':
                                v = 'expected_verdict: true'
                            else:
                                v = ''
                                
                            # if status == 'unsat' or status == 'sat':
                            name = os.path.splitext(file)[0]
                            str = template.safe_substitute(fname = file, verdict = v)
                            with open(os.path.join(root, name + '.yml'), 'w') as out:
                                out.write(str)
                                
                            break

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--folder', type=Path)
    parser.add_argument('--num', type=int, required=True, default=10)
    p = parser.parse_args()
    dir = p.folder
    n = p.num
    if dir is None:
        return
    for root, dirs, files in os.walk(dir):
        for d in dirs:
            print('processing dir', d)
            current_subdir_path = os.path.join(root, d)
            flatten(current_subdir_path)
            all_smt_files = []
            for d_path, dirs, files in os.walk(current_subdir_path):
                for f in files:
                    if f.endswith('.smt2'):
                        print('file', f)
                        all_smt_files.append(f)
            # print(all_smt_files)
            m = min(n, len(all_smt_files))
            s = sample(all_smt_files, m)
            # print(s)
            selected = set(s)
            for d_path, dirs, files in os.walk(current_subdir_path):
                for f in files:
                    if not f in selected:
                        os.remove(os.path.join(d_path, f))
    print('flatten complete')
    create_ymls(dir)

if __name__ == '__main__':
    main()
    
