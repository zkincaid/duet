#!/bin/python3

import sys
import os
import glob
import yaml
from string import Template
import tempfile
import subprocess

template="""format_version: '1.0'

input_files: '$target'

properties:
  - property_file: ../properties/termination.prp
    expected_verdict: true
"""

tasks = sys.argv[1:]
for task in tasks:
    with open(os.path.join("tasks",task)) as file:
        task_info = yaml.load(file, Loader=yaml.FullLoader)
        name = os.path.basename(task[:-4])
        task_c = os.path.join("tasks",
                              os.path.dirname(task),
                              task_info['input_files'])

        with tempfile.TemporaryDirectory() as tmp_dir:
            goto_file = "%s/%s.goto" % (tmp_dir,name)
            instr_file = "%s/%s.instr.c" % (tmp_dir,name)
            target_file = "tasks/bitprecise/%s.c" % name
            target_yml = "tasks/bitprecise/%s.yml" % name
            subprocess.call(['goto-cc', task_c, '-c', '-o', goto_file])
            subprocess.call(['goto-instrument',
                             '--dump-c',
                             '-signed-overflow-check',
                             goto_file,
                             instr_file])
            subprocess.call(['gcc', '-E', '-P', "-I.", instr_file, '-o', target_file])
            subst = dict(target = ("%s.c" % name))
            out = open(target_yml, "w")
            out.write(Template(template).substitute(subst))
            out.close()
            print(target_yml)

