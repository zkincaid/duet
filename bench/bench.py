#!/bin/python3

import sys
import os
import glob
from string import Template
import subprocess
import tempfile
import types
import statistics
from collections import defaultdict

# Configuration -- can be reconfigured via the command line
tools = ['ComPACT', 'CPAchecker', 'UAutomizer', '2ls', 'Termite']
suites = ['Termination', 'bitprecise', 'recursive', 'polybench']
timeout = 600
cache = True
replace_cached = False
num_runs = 1

table_begin = """<?xml version="1.0" ?>
<!DOCTYPE table PUBLIC "+//IDN sosy-lab.org//DTD BenchExec table 1.10//EN" "https://www.sosy-lab.org/benchexec/table-1.10.dtd">
<table>
"""
table_end = "</table>"

# tables are formatted with 1 column for the benchmark name & 3 columns for each tool
#  column 0: benchmark name
#  column 3i + 1: result (output of tool)
#  column 3i + 2: category (whether that result is correct)
#  column 3i + 3: time (s)


def get_name(row):
    return row[0]


def get_result(row, index):
    return row[3 * index + 1]


def get_category(row, index):
    return row[3 * index + 2]


def get_time(row, index):
    return float(row[3 * index + 3])


def has_result(tool, suite):
    return len(glob.glob("results/%s.*.%s.xml.bz2" % (tool, suite))) > 0


def run():
    for suite in suites:
        for tool in tools:
            if replace_cached and has_result(tool, suite):
                recent = recent_result(tool, suite)
                os.remove(recent)

            if cache and has_result(tool, suite):
                print("Result of %s on suite %s is cached" % (tool, suite))
            else:
                print("Running %s on suite %s" % (tool, suite))
                # Add bench dir to PYTHONPATH so benchexec can find the
                # tool module
                my_env = os.environ.copy()
                my_env["PYTHONPATH"] = os.getcwd()
                my_env["PATH"] = my_env["PATH"] + ":" + os.path.abspath('..')
                subprocess.call(["benchexec",
                                 "-W", str(timeout),
                                 "-t", suite,
                                 "--read-only-dir", "/",
                                 "--overlay-dir", "/home",
                                 "benchmark-defs/%s.xml" % tool],
                                env=my_env)


def recent_result(tool, suite, which_run=1):
    results = glob.glob("results/%s.*.%s.xml.bz2" % (tool, suite))
    results.sort()
    if len(results) == 0:
        print("No results for %s on suite %s" % (tool, suite))
        exit(-1)
    else:
        return results[-which_run]


def recent_result_data(tools, suites, num_runs_to_fetch=1):
    multirun_data = []
    for run in range(num_runs_to_fetch):
        data = []
        for suite in suites:
            with tempfile.TemporaryDirectory() as tmp_dir:
                p = subprocess.run(['table-generator',
                                    '-f', 'csv',
                                    '-o', tmp_dir,
                                    '-x', 'simplecsv.xml',
                                    '-q']
                                   + list(map(lambda x: recent_result(x, suite, which_run=run), tools)))
                table = os.path.join(tmp_dir, "simplecsv.table.csv")
                # strip 3 rows of header info
                data += list(map(lambda row: row.rstrip().split('\t'),
                                 open(table).readlines()))[3:]
        multirun_data.append(data)
    return multirun_data


def summarize_result(tool, suite, average_over_runs=1):
    multirun_data = recent_result_data(
        [tool], [suite], num_runs_to_fetch=average_over_runs)
    multirun_results = []
    for run in range(average_over_runs):
        data = multirun_data[run]
        result = types.SimpleNamespace()
        result.total = 0
        result.time = 0
        result.maxvar = 0
        result.correct = 0
        result.timeout = 0
        result.memout = 0
        result.unknown = 0
        result.time_by_verdict = defaultdict(float)
        result.task_times_by_verdict = defaultdict(list)
        result.maxvar_by_verdict = defaultdict(float)
        result.num_by_verdict = defaultdict(int)
        result.correct_by_verdict = defaultdict(int)
        result.timeout_by_verdict = defaultdict(int)
        result.memout_by_verdict = defaultdict(int)
        for entry in data:
            result.total += 1
            if len(entry) > 4:
                result.time += float(entry[4])
                v = entry[1]
                if v == '':
                    v = 'unknown'
                result.num_by_verdict[v] += 1
                t = float(entry[4])
                result.time_by_verdict[v] = result.time_by_verdict[v] + t
                result.task_times_by_verdict[v].append(t)
                if entry[2] == 'TIMEOUT':
                    result.timeout += 1
                    result.timeout_by_verdict[v] = result.timeout_by_verdict[v] + 1
                else:
                    # result.time_by_verdict[v] = result.time_by_verdict[v] + t
                    if entry[3] == 'correct':
                        result.correct += 1
                        result.correct_by_verdict[v] = result.correct_by_verdict[v] + 1
                    elif entry[2] == 'KILLED BY SIGNAL 9':
                        result.memout += 1
                        result.memout_by_verdict[v] = result.memout_by_verdict[v] + 1
                    elif entry[3] == "unknown":
                        result.unknown += 1
                continue
            result.time += get_time(entry, 0)
            if (get_result(entry, 0) == "TIMEOUT"):
                result.timeout += 1
            elif (get_category(entry, 0) == "correct"):
                result.correct += 1
            elif (get_category(entry, 0) == "unknown"):
                result.unknown += 1
        multirun_results.append(result)
    ar = types.SimpleNamespace()
    r = multirun_results[0]
    ar.total = r.total

    multi_run_times = []
    for run in range(average_over_runs):
        multi_run_times.append(multirun_results[run].time)
    mean_run_time = statistics.mean(multi_run_times)
    ar.time = mean_run_time

    max_time_var = 0.0
    for task_id in range(len(multirun_results)):
        times_per_task = []
        for run in range(average_over_runs):
            if len(multirun_data[run][task_id]) > 4:
                times_per_task.append(float(multirun_data[run][task_id][4]))
        var_this_task = 0.0 if average_over_runs == 1 else statistics.variance(
            times_per_task)
        max_time_var = max(max_time_var, var_this_task)
    ar.maxvar = max_time_var

    ar.correct = r.correct
    ar.timeout = r.timeout
    ar.memout = r.memout
    ar.unknown = r.unknown

    ar.time_by_verdict = defaultdict(float)
    ar.maxvar_by_verdict = defaultdict(float)
    for v in ['true', 'false', 'unknown']:
        multi_run_times = []
        for run in range(average_over_runs):
            multi_run_times.append(multirun_results[run].time_by_verdict[v])
        mean_run_time = statistics.mean(multi_run_times)
        ar.time_by_verdict[v] = mean_run_time

        max_time_var = 0.0
        for task_id in range(len(r.task_times_by_verdict[v])):
            times_per_task = []
            for run in range(average_over_runs):
                if len(multirun_data[run][task_id]) > 4:
                    times_per_task.append(multirun_data[run][task_id][4])
            var_this_task = 0.0 if average_over_runs == 1 else statistics.variance(
                times_per_task)
            max_time_var = max(max_time_var, var_this_task)
        ar.maxvar_by_verdict[v] = max_time_var

    ar.num_by_verdict = r.num_by_verdict
    ar.correct_by_verdict = r.correct_by_verdict
    ar.timeout_by_verdict = r.timeout_by_verdict
    ar.memout_by_verdict = r.memout_by_verdict
    return ar


def summary_by_verdict(average_over_runs=1):
    res = {}

    num = {}
    total_correct = {}
    total_time = {}
    num_timeout = {}
    num_memout = {}
    max_variance = {}

    for tool in tools:
        total_correct[tool] = 0
        num_timeout[tool] = 0
        num_memout[tool] = 0
        total_time[tool] = 0
        max_variance[tool] = 0

    for s in suites:
        r = {}
        for t in tools:
            r[t] = summarize_result(t, s)
        res[s] = r

    for suite in suites:
        for verd in ['true', 'false', 'unknown']:
            row_name = suite + ' - ' + verd
            for tool in tools:
                r = res[suite][tool]
                num_suite = r.num_by_verdict[verd]
                total_correct[tool] += r.correct_by_verdict[verd]
                total_time[tool] += r.time_by_verdict[verd]
                max_variance[tool] = max(max_variance[tool], r.maxvar)
                num_timeout[tool] += r.timeout_by_verdict[verd]
                num_memout[tool] += r.memout_by_verdict[verd]
            num[row_name] = num_suite

    print("\\begin{tabular}{@{}lc|%s@{}}" %
          ("|".join(["c@{}c@{}r@{}r"] * (len(tools)))))
    print("\\toprule")
    print(" &", end='')
    for tool in tools[:-1]:
        print(" & \\multicolumn{4}{c|}{%s}" % tool, end='')
    print(" & \\multicolumn{4}{c}{%s}\\\\" % tools[-1])

    print(" & \#tasks & %s\\\\\\midrule" % " & ".join(
        ["\#P & \#E & t & $\sigma$ "] * len(tools)))

    for suite in suites:
        for verd in ['true', 'false', 'unknown']:
            suite_name = suite + ' - ' + verd
            print("%s & %d" % (suite_name, num[suite_name]), end='')
            for tool in tools:
                c = res[suite][tool]
                print(" & %d" % c.correct_by_verdict[verd], end='')
                print(
                    " & %d/%d" % (c.timeout_by_verdict[verd], c.memout_by_verdict[verd]), end='')
                print(" & %.1f" % c.time_by_verdict[verd], end='')
                print(" & %.2f" % c.maxvar_by_verdict[verd], end='')

            print("\\\\")
    print("\\midrule")

    print("Total & %d " % sum(num.values()), end='')
    for tool in tools:
        print(" & %d" % total_correct[tool], end='')
        print(" & %d/%d" % (num_timeout[tool], num_memout[tool]), end='')
        print(" & %.1f" % total_time[tool], end='')
        print(" & %.2f" % max_variance[tool], end='')
    print("\\\\")

    print("\\bottomrule")
    print("\\end{tabular}")


def summary(average_over_runs=1):
    matrix = {}

    best_time = {}
    best_correct = {}
    num = {}
    total_correct = {}
    total_time = {}
    max_variance = {}
    num_timeout = {}

    for tool in tools:
        total_correct[tool] = 0
        total_time[tool] = 0
        max_variance[tool] = 0
        num_timeout[tool] = 0

    for suite in suites:
        row = {}
        best_time_suite = 999999999.0
        best_correct_suite = 0
        num_suite = 0
        for tool in tools:
            r = summarize_result(
                tool, suite, average_over_runs=average_over_runs)

            best_correct_suite = max(best_correct_suite, r.correct)
            num_suite = r.total
            row[tool] = r
            total_correct[tool] += r.correct

            total_time[tool] += r.time
            best_time_suite = min(best_time_suite, r.time)
            max_variance[tool] = max(max_variance[tool], r.maxvar)
            num_timeout[tool] += r.timeout

        best_time[suite] = best_time_suite
        best_correct[suite] = best_correct_suite
        num[suite] = num_suite
        matrix[suite] = row

    print("\\begin{tabular}{@{}lc|%s@{}}" %
          ("|".join(["c@{}r@{}r"] * (len(tools)))))
    print("\\toprule")
    print(" &", end='')
    for tool in tools[:-1]:
        print(" & \\multicolumn{3}{c|}{%s}" % tool, end='')
    print(" & \\multicolumn{3}{c}{%s}\\\\" % tools[-1])

    print(" & \#tasks & %s\\\\\\midrule" %
          " & ".join(["\#correct & time & var"] * len(tools)))

    for suite in suites:
        print("%s & %d" % (suite, num[suite]), end='')
        for tool in tools:
            if (matrix[suite][tool].correct == best_correct[suite]):
                print(" & \\textbf{%d}" % best_correct[suite], end='')
            else:
                print(" & %d" % matrix[suite][tool].correct, end='')

            if (matrix[suite][tool].time == best_time[suite]):
                print(" & \\textbf{%.1f}" % best_time[suite], end='')
            else:
                print(" & %.1f" % matrix[suite][tool].time, end='')
        print("\\\\")
    print("\\midrule")

    best_total_time = min(total_time.values())
    best_total_correct = max(total_correct.values())

    print("Total & %d " % sum(num.values()), end='')
    for tool in tools:
        if (total_correct[tool] == best_total_correct):
            print(" & \\textbf{%d}" % best_total_correct, end='')
        else:
            print(" & %d" % total_correct[tool], end='')

        if (total_time[tool] == best_total_time):
            print(" & \\textbf{%.1f},max $\\sigma$=(%.2f)" %
                  (best_total_time, max_variance[tool]), end='')
        else:
            print(" & %.1f, max $\\sigma$=(%.2f)" %
                  (total_time[tool], max_variance[tool]), end='')
    print("\\\\")

    print("Timeouts & ", end='')
    for tool in tools:
        print(" & \\multicolumn{2}{c}{%d}" % num_timeout[tool], end='')

    print("\\\\")

    print("\\bottomrule")
    print("\\end{tabular}")


def make_table():
    with tempfile.TemporaryDirectory() as tmp_dir:
        tmp_file = os.path.join(tmp_dir, "results.xml")
        tmp = open(tmp_file, "w")
        tmp.write(table_begin)
        for tool in tools:
            tmp.write("<union>\n")
            for suite in suites:
                tmp.write('<result filename="')
                tmp.write(os.path.join(
                    os.getcwd(), recent_result(tool, suite)))
                tmp.write('" />\n')
            tmp.write("</union>\n")
        tmp.write(table_end)
        tmp.close()
        os.system("table-generator -x %s -o results" % tmp_file)


def cactus_data(data, out):
    times = []
    for entry in data:
        # Only include correct benchmarks
        if get_category(entry, 0) == "correct":
            times.append(get_time(entry, 0))
    times = sorted(times)
    prev = times[0]
    last = len(times)
    for instance in range(1, last):
        if prev != times[instance]:
            prev = times[instance]
            out.write("%d %f\n" % (instance, times[instance - 1]))
    out.write("%d %f\n" % (last, times[last - 1]))


def cactus_plot():

    legend = ""
    data = ""

    for tool_name in tools:
        matrix = recent_result_data([tool_name], suites)[0]

        print("Writing data to %s.dat" % tool_name)
        f = open("%s.dat" % tool_name, "w")
        cactus_data(matrix, f)
        f.close()
        if legend == "":
            legend = tool_name
        else:
            legend += "," + tool_name
        data += ('    \\addplot table {%s.dat};\n' % tool_name)

    subst = dict(legend=legend,
                 data=data,
                 bench_size=len(matrix))
    print(Template(open("cactus.template").read()).substitute(subst))


def scatter_plot():
    if (len(tools) != 2):
        print("For scatter plot, must supply exactly two tools to compare")
        exit(-1)

    matrix = recent_result_data(tools, suites)[0]

    # Don't include points where one tool gave a wrong answer
    ok_results = ["correct", "TIMEOUT", "unknown"]

    min_time = 1
    max_time = 1

    # both correct figure
    filename_tt = "scatter_%s_%s_tt.dat" % (tools[0], tools[1])
    print("Writing data to %s" % filename_tt)
    out = open(filename_tt, "w")
    legendentry_tt = "%s %s both correct" % (tools[0], tools[1])

    for i in range(len(matrix)):
        # if get_category(matrix[i],0) in ok_results and get_category(matrix[i],1) in ok_results:
        if get_category(matrix[i], 0) == "correct" and get_category(matrix[i], 1) == "correct":
            time1 = get_time(matrix[i], 0)
            time2 = get_time(matrix[i], 1)
            out.write("%f %f\n" % (time1, time2))

            min_time = min(min_time, time1, time2)
            max_time = max(max_time, time1, time2)

    out.close()

    # first tool correct, second tool not correct
    filename_tf = "scatter_%s_%s_tf.dat" % (tools[0], tools[1])
    print("Writing data to %s" % filename_tf)
    out = open(filename_tf, "w")
    legendentry_tf = "%s correct, %s not correct" % (tools[0], tools[1])

    for i in range(len(matrix)):
        # if get_category(matrix[i],0) in ok_results and get_category(matrix[i],1) in ok_results:
        if get_category(matrix[i], 0) == "correct" and get_category(matrix[i], 1) != "correct":
            time1 = get_time(matrix[i], 0)
            time2 = get_time(matrix[i], 1)
            out.write("%f %f\n" % (time1, time2))

            min_time = min(min_time, time1, time2)
            max_time = max(max_time, time1, time2)

    out.close()

    # first tool correct, second tool not correct
    filename_ft = "scatter_%s_%s_ft.dat" % (tools[0], tools[1])
    print("Writing data to %s" % filename_ft)
    out = open(filename_ft, "w")
    legendentry_ft = "%s not correct, %s correct" % (tools[0], tools[1])

    for i in range(len(matrix)):
        # if get_category(matrix[i],0) in ok_results and get_category(matrix[i],1) in ok_results:
        if get_category(matrix[i], 0) != "correct" and get_category(matrix[i], 1) == "correct":
            time1 = get_time(matrix[i], 0)
            time2 = get_time(matrix[i], 1)
            out.write("%f %f\n" % (time1, time2))

            min_time = min(min_time, time1, time2)
            max_time = max(max_time, time1, time2)

    out.close()

    # first tool correct, second tool not correct
    filename_ff = "scatter_%s_%s_ff.dat" % (tools[0], tools[1])
    print("Writing data to %s" % filename_ff)
    out = open(filename_ff, "w")
    legendentry_ff = "%s %s both not correct" % (tools[0], tools[1])

    for i in range(len(matrix)):
        # if get_category(matrix[i],0) in ok_results and get_category(matrix[i],1) in ok_results:
        if get_category(matrix[i], 0) != "correct" and get_category(matrix[i], 1) != "correct":
            time1 = get_time(matrix[i], 0)
            time2 = get_time(matrix[i], 1)
            out.write("%f %f\n" % (time1, time2))

            min_time = min(min_time, time1, time2)
            max_time = max(max_time, time1, time2)

    out.close()

    subst = dict(min=min_time,
                 max=max_time,
                 x=tools[0],
                 y=tools[1],
                 datatt=filename_tt,
                 ttlegend=legendentry_tt,
                 datatf=filename_tf,
                 tflegend=legendentry_tf,
                 dataft=filename_ft,
                 ftlegend=legendentry_ft,
                 dataff=filename_ff,
                 fflegend=legendentry_ff,
                 )
    print(Template(open("scatter.template").read()).substitute(subst))


if __name__ == "__main__":
    if (len(sys.argv) <= 1):
        print("No command provided")

    command = sys.argv[1]
    opts = sys.argv[2:]
    while (len(opts) > 0):
        if (opts[0] == "--timeout"):
            timeout = int(opts[1])
            opts = opts[2:]
        elif (opts[0] == "--tools"):
            tools = opts[1].split(",")
            opts = opts[2:]
        elif (opts[0] == "--suites"):
            suites = opts[1].split(",")
            opts = opts[2:]
        elif (opts[0] == "--no-cache"):
            cache = False
            opts = opts[1:]
        elif (opts[0] == "--replace-cached"):
            cache = False
            replace_cached = True
            opts = opts[1:]
        elif (opts[0] == "--collect-multiple-runs"):
            num_runs = int(opts[1])
            opts = opts[2:]
        else:
            print("Unrecognized option: %s" % opts[0])
            exit(-1)

    if (command == "run"):
        run()
    elif (command == "table"):
        make_table()
    elif (command == "cactus"):
        cactus_plot()
    elif (command == "scatter"):
        scatter_plot()
    elif (command == "summary"):
        summary()
    elif (command == "summarybyverdict"):
        summary_by_verdict()
    else:
        print("Unknown command")
