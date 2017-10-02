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

def create_dirs():
	def try_mkdir(dir_name):
	    try:
	            os.mkdir(dir_name)
	    except FileExistsError:
	            pass

	dir_names = ['ioctl_items', 'backups']
	for dir_name in dir_names:
		try_mkdir(dir_name)

if __name__ == '__main__':
	add_script_to_startup_dir()
	create_dirs()