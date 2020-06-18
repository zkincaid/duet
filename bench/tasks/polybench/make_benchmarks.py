#!/bin/python3

import sys
import os
import glob
from string import Template
import subprocess
import tempfile
import types

template="""format_version: '1.0'

input_files: '$target'

properties:
  - property_file: ../properties/termination.prp
    expected_verdict: true
"""

for file in sys.argv[1:]:
    dirname = os.path.dirname(file)
    base,_ = os.path.splitext(file)
    target = base + ".merged.c"
    yaml = os.path.basename(base) + ".yml"
#    os.system("gcc -D_Float128=float -D_STDIO_H -D_MATH_H -D_UNISTD_H -D_STRING_H -D_MATH_H -D_TYPES_H -I utilities -I %s utilities/polybench.c %s -E > %s" % (dirname, file, target))
    os.system("cilly --merge -D_Float128=float -I utilities -I %s utilities/polybench.c %s -c -o % s" % (dirname, file, target))
    

    subst = dict(target = target)

    out = open(yaml, "w")
    out.write(Template(template).substitute(subst))
    out.close()
