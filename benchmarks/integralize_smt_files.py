import argparse
import os
import shutil
import subprocess

def copy_directory_structure(inroot, outroot):
    print(f"Copying directory structure from {inroot} to {outroot}")
    for root, dirs, files in os.walk(inroot):
        print(f"root: {root}, dirs: {dirs}, files: {files}")
        for directory in dirs:
            relpath = os.path.relpath(root, start=inroot)
            new_dir = os.path.join(outroot, relpath, directory)
            print(f"creating {new_dir}")
            os.mkdir(new_dir)
        for f in files:
            infile = os.path.join(root, f)
            relpath = os.path.relpath(root, start=inroot)
            outfile = os.path.join(outroot, relpath, f)
            print(f"copying {infile} to {outfile}")
            shutil.copy(infile, outfile)


def run_bigtop(option, indir, outdir):
    if option == "integralize":
        option = "-integralize-smt-file"
    elif option == "realify":
        option = "-realify-smt-file"
    else:
        print("Invalid option")
        exit(0)
    def to_delete(f):
        not_integralized = (not f.endswith("_integralized.smt2"))
        not_realified = (not f.endswith("_realified.smt2"))
        not_equivalent = (not f.endswith("_equivalent.smt2"))
        return not_integralized and not_realified and not_equivalent

    for root, dirs, files in os.walk(outdir):
        print(f"root: {root}, files: {files}")
        for f in files:
            if os.path.splitext(f)[-1] == ".smt2":
                smt_file = os.path.join(root, f)
                print(f"Running command: bigtop.exe {option} {smt_file}")
                subprocess.run(["bigtop.exe", option, smt_file])
    for root, dirs, files in os.walk(outdir):
        for f in files:
            if to_delete(f):
                print(f"Deleting {os.path.join(root, f)}")
                os.remove(os.path.join(root, f))

directories = [
    # "cra-monotone-c4b-hulls",
    # "cra-monotone-hola-hulls",
    # "cra-monotone-polybench-hulls",
    "cra-monotone-svcomp-reach-safety-hulls"
    # "termination-monotone-no-phase-c4b-hulls",
    # "termination-monotone-no-phase-hola-hulls",
    # "termination-monotone-no-phase-polybench-hulls",
    # "termination-monotone-no-phase-svcomp-reach-safety-hulls"
]

def run(convhull_root):
    for d in directories:
        original = os.path.join(convhull_root, d)
        integralized = os.path.join(convhull_root, f"{d}-integralized")
        realified = os.path.join(convhull_root, f"{d}-realified")
        os.mkdir(integralized)
        os.mkdir(realified)
        copy_directory_structure(original, integralized)
        copy_directory_structure(original, realified)
        run_bigtop("integralize", original, integralized)
        run_bigtop("realify", original, realified)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument("--indir")
    args = parser.parse_args()
    run(args.indir)
    # Run with bigtop.exe availabie in PATH
