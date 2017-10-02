import os
import winshell

def make_line(string):
        return '{}\n'.format(string)

def add_script_to_startup_dir():
	script_path = os.path.join(winshell.startup(), 'on_target_boot.bat')

	with open(script_path, 'w') as f:
		cmds  = make_line('pushd {}'.format(os.getcwd()))
		cmds += make_line('start "" python ioctl_fuzzer.py')
		f.write(cmds)

def create_ioctl_items_dir():
        try:
                os.mkdir('ioctl_items')
        except FileExistsError:
                pass

if __name__ == '__main__':
	add_script_to_startup_dir()
	create_ioctl_items_dir()