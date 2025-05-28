import argparse
import os
import shutil
import subprocess

polybench_directories = ["datamining", "linear-algebra", "medley", "stencils"]

reach_safety_directories = \
    [ "loops", "loop-acceleration", "loop-crafted", "loop-invgen",
      "loop-lit", "loop-new", "loop-industry-pattern", "loops-crafted-1",
      "loop-invariants", "loop-simple", "loop-zilu", "verifythis"
      # "nla-digbench", "nla-digbench-scaling", "verifythis"
     ]

reach_safety_directories = ["nla-digbench", "nla-digbench-scaling", "verifythis"]

# reach_safety_verify_this = \
#     ["duplets.c", "elimination_max.c", "lcp.c", "prefixsum_iter.c", \
#      "tree_del_iter.c", "tree_del_iter_incorrect.c"]

def handle_task(command, inroot, outroot, top_level_directories, timeout):
    print(f"handle_task: inroot: {inroot}, outroot: {outroot}")
    replicate_directory_structure(inroot, outroot, top_level_directories)
    hull_mappings = dump_hulls(inroot, outroot, command, top_level_directories, timeout)
    return hull_mappings

def dump_svcomp_reach_safety(svbenchmarks_c_root, svbenchmarks_outroot, command, timeout):
    inroot = svbenchmarks_c_root
    outroot = svbenchmarks_outroot
    replicate_directory_structure(inroot, outroot, reach_safety_directories)
    hull_mappings = dump_hulls(inroot, outroot, command, reach_safety_directories, timeout)
    verifythis_out = os.path.join(outroot, "verifythis")
    os.mkdir(verifythis_out)
    for f in reach_safety_verify_this:
        filename = os.path.join(inroot, "verifythis", f)
        hulls = dump_hulls_for(filename, command, verifythis_out, timeout)
        hull_mappings[filename] = hulls
    return hull_mappings

def dump_polybench(inroot, outroot, command):
    directories = ["datamining", "linear-algebra", "medley", "stencils"]
    replicate_directory_structure(inroot, outroot, directories)
    hull_mappings = dump_hulls(inroot, outroot, command, directories, timeout)
    return hull_mappings

def dump_test1(inroot, outroot, command, timeout):
    directories = ["test1"]
    replicate_directory_structure(inroot, outroot, directories)
    hull_mappings = dump_hulls(inroot, outroot, command, directories, timeout)
    return hull_mappings

def replicate_directory_structure(inroot, outroot, top_level_inclusion):
    at_top = True
    for root, dirs, files in os.walk(inroot):
        print(f"replicate_directory_structure before modification: root: {root}, dirs: {dirs}, files: {files}\n")
        print(f"top level inclusion: {top_level_inclusion}")
        if at_top and top_level_inclusion is not None:
            dirs[:] = [d for d in dirs if d in top_level_inclusion]
            at_top = False
            print(f"replicate_directory_structure after modification: root: {root}, dirs: {dirs}, files: {files}\n")
        for directory in dirs:
            relpath = os.path.relpath(root, start=inroot)
            new_dir = os.path.join(outroot, relpath, directory)
            print(f"creating {new_dir}")
            os.mkdir(new_dir)

def find_smt2_files(filename):
    smt_files = []
    for root, dirs, files in os.walk("/tmp"):
        for f in files:
            exts = os.path.splitext(f)
            (basename, extension) = (exts[0], exts[-1])
            if extension == ".smt2" and basename.startswith(filename):
                smt_files.append(os.path.join(root, f))
    return smt_files

def move_files(files, outdir):
    targets = []
    for f in files:
        outfile = os.path.join(outdir, os.path.basename(f))
        # print(f"Copying {f} to {outfile}")
        shutil.copy(f, outfile)
        os.remove(f)
        targets.append(outfile)
    return targets

def dump_hulls_for(filename, command, output_dir, timeout):
    try:
        subprocess.run(command + [filename], timeout=timeout)
    except subprocess.TimeoutExpired:
        with open("timeouts.txt", "a") as f:
            f.write(f"{command} {filename}")
    smt_output_files = find_smt2_files(os.path.splitext(os.path.basename(filename))[0])
    print(f"Found: {smt_output_files}")
    print(f"Moving files to {output_dir}")
    hulls = move_files(smt_output_files, output_dir)
    return hulls

def dump_hulls(inroot, outroot, command, included, timeout):
    hulls_for = dict()
    at_top = True
    for root, dirs, files in os.walk(inroot):
        if at_top and included is not None:
            dirs[:] = [d for d in dirs if d in included]
            at_top = False
        print(f"dump_hulls: root: {root}, dirs: {dirs}, files: {files}")
        for f in files:
            if os.path.splitext(f)[-1] == ".c":
                infile = os.path.join(root, f)
                relpath = os.path.relpath(root, start=inroot)
                output_dir = os.path.join(outroot, relpath)
                hulls = dump_hulls_for(infile, command, output_dir, timeout)
                hulls_for[infile] = hulls
    return hulls_for

def form_command(cmd, indir, is_polybench):
    # For polybench, even after passing cflags, duet fails because
    # Cil's parsing (Frontc) fails, in turn because _Float128 is not defined.
    # To get around this, make a copy of
    # /usr/include/math.h and /usr/include/bits/floatn.h in utilities/,
    # and in the latter file, do "#define __HAVE_FLOAT128 0"
    polybench_include = os.path.join(indir, "utilities")
    cflags = ["-cflags", f'"-I{polybench_include}"'] if is_polybench else []
    cra_cmd = ["duet.exe"] + cflags + ["-cra", "-monotone", "-dump-hulls"]
    termination_cmd = \
        ["duet.exe"] + cflags + \
        ["-termination", "-monotone", "-termination-no-phase", "-dump-hulls"]
    cmd = cra_cmd if cmd == "cra" else termination_cmd if cmd == "termination" else None
    if cmd is None:
        print("invalid command")
        exit(0)
    return cmd

def which_directories(task):
    if task == "polybench":
        return polybench_directories
    elif task == "svcomp-reach-safety":
        return reach_safety_directories
    else:
        return None

def get_indir_name(task):
    if task == "hola":
        return "HOLA"
    elif task == "c4b":
        return "C4B"
    elif task == "svcomp-reach-safety":
        return "svcomp-reach-safety"
    elif task == "polybench":
        return "PolyBenchC-4.2.1"
    else:
        return None

def run(args):
    tasks = args.which.split(",")
    for task in tasks:
        indir = os.path.join(args.indir, get_indir_name(task))
        prefix = "cra-monotone" if args.cmd == "cra" else "termination-monotone-no-phase"
        outdir_name = f"{prefix}-{task}-hulls"
        outdir = os.path.join(args.outdir, outdir_name)
        print(f"indir: {indir}")
        cmd = form_command(args.cmd, indir, True if task == "polybench" else False)
        timeout = int(args.timeout) * 60 if args.timeout is not None else 120 # 2 minutes
        print(f"Going to run command {cmd} with timeout {args.timeout}")
        os.mkdir(outdir)
        directories = which_directories(task)
        hull_mappings = handle_task(cmd, indir, outdir, directories, timeout)
        if args.mappings is not None:
            with open(args.mappings, "w") as f:
                f.write(str(hull_mappings))

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--indir")
    parser.add_argument("--outdir")
    parser.add_argument("--cmd")
    parser.add_argument("--which", help="comma-separated list with entries in {hola, c4b, polybench, svcomp-reach-safety, test}")
    parser.add_argument("--timeout", help="timeout in minutes")
    parser.add_argument("--mappings")
    args = parser.parse_args()
    run(args)
    # Run with duet.exe available in PATH
