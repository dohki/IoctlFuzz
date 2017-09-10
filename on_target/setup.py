import winreg

def add_script_to_startup_dir():
	# TODO: Where SHGFP_TYPE_CURRENT or DEFAULT are defined?
	startup_dir_path = win32com.shell.shell.SHGetFolderPath(None, win32com.shell.shellcon.CSIDL_STARTUP, None, 0)
	script_path = os.path.join(startup_dir_path, 'on_target_boot.bat')

	with open(script_path, 'w') as f:
		cmds  = make_line('pushd {}'.format(os.getcwd()))
		cmds += make_line('start "" python ioctl_fuzzer.py')
		f.write(cmds)

if __name__ == '__main__':
	add_script_to_startup_dir()