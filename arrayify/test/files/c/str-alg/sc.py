import os
import yaml

# Get the list of all C files in the current directory
c_files = [f for f in os.listdir('.') if f.endswith('.c')]

# Template for the YAML content
template = {
    'format_version': '2.0',
    'input_files': '',
    'properties': [
        {
            'property_file': '../properties/unreach-call.prp',
            'expected_verdict': True
        }
    ],
    'options': {
        'language': 'C',
        'data_model': 'ILP32'
    }
}

# Create a YAML file for each C file
for c_file in c_files:
    yaml_content = template.copy()
    yaml_content['input_files'] = c_file
   
    yaml_filename = f"{os.path.splitext(c_file)[0]}.yml"
    with open(yaml_filename, 'w') as yaml_file:
        yaml.dump(yaml_content, yaml_file, default_flow_style=False)

print("YAML files created for all C files in the current directory.")
