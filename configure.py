#!/usr/bin/env python3
"""
Configure PyLayers directories and paths
"""
from pathlib import Path

def main():
    home = Path.home()
    current_dir = Path.cwd()
    project_dir = current_dir / 'pylayers_project'
    
    # Create .pylayers config
    config_content = f"source\n{current_dir}\nproject\n{project_dir}\n"
    with open(home / '.pylayers', 'w') as f:
        f.write(config_content)
    
    # Create project directory
    project_dir.mkdir(exist_ok=True)
    
    # Create required subdirectories
    subdirs = [
        'ini', 'ant', 'output', 'geom', 'meas', 'netsave', 'body', 'gis',
        'struc/wrl', 'struc/lay', 'struc/osm', 'struc/furnitures', 
        'struc/images', 'struc/gpickle', 'struc/res', 'struc/str',
        'output/Tx001', 'output/r2d', 'output/r3d', 'output/Ct', 'output/H',
        'body/c3d', 'body/wear', 'gis/osm'
    ]
    
    for subdir in subdirs:
        (project_dir / subdir).mkdir(parents=True, exist_ok=True)
    
    print(f"Configuration created: {home / '.pylayers'}")
    print(f"Project directory: {project_dir}")

if __name__ == '__main__':
    main()