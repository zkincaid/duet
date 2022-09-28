import sys
import os
import glob
import yaml
import subprocess

#tasks = glob.glob("tasks/termination-crafted/*.yml") + glob.glob("tasks/termination-crafted-lit/*.yml") + glob.glob("tasks/termination-numeric/*.yml") + glob.glob("tasks/termination-restricted-15/*.yml")
#tasks = glob.glob("tasks/recursive/*.yml")
my_env = os.environ.copy()
my_env['PATH'] = my_env['PATH'] + ':' + os.path.abspath('..')

pattern = {}

opts = sys.argv[1:]
while(len(opts) > 0):
    opt = opts[0]
    opts = opts[1:]
    if (opt == "--"):
        break
    key, val = opt.split('=')
    pattern[key[2:]] = (val == "True")

for task in opts:
    with open(task) as file:
        task_info = yaml.load(file, Loader=yaml.FullLoader)
        for prop in task_info['properties']:
            if prop['property_file'] == '../properties/termination.prp' or prop['property_file'] == '../properties/unreach-call.prp':
                input_file = os.path.join(os.path.dirname(task),
                                          task_info['input_files'])
                result = subprocess.run(['duet.exe', '-categorize', input_file],
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE,
                                        env=my_env)
                categories = yaml.load(result.stdout, Loader=yaml.FullLoader)
                use_task = True
                for k in pattern:
                    if k == "verdict":
                        if 'expected_verdict' in prop:
                            use_task = use_task and prop.get('expected_verdict') == pattern[k]
                        else:
                            use_task = False
                    else:
                        use_task = use_task and pattern[k] == categories[k]
                if use_task:
                    print (task[6:])
