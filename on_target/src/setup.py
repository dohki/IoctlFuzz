import os
import winshell

import util

def add_script_to_startup_dir():
    script_path = os.path.join(winshell.startup(), 'on_target_boot.bat')

    with open(script_path, 'w') as f:
        cmds  = util.make_line('pushd {}'.format(os.getcwd()))
        cmds += util.make_line('start "" py -3 fuzzer.py')
        f.write(cmds)

def mkdirs():
    dir_names = ['dict', 'corpus', 'crash']
    for dir_name in dir_names:
        try:
            os.mkdir(os.path.join('..', dir_name))
        except FileExistsError:
            pass

if __name__ == '__main__':
    add_script_to_startup_dir()
    mkdirs()
