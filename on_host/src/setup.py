import argparse
import os
import ctypes
import json
import winreg
import winshell

def mkdirs():
	dir_names = ['config']
	for dir_name in dir_names:
		try:
			os.mkdir(os.path.join('..', dir_name))
		except FileExistsError:
			pass

# TODO: Update
def parse_args():
	parser = argparse.ArgumentParser(description='Set configs for WinDFuzz (Automated Windows Driver Fuzzing Enviroment).', formatter_class=argparse.RawTextHelpFormatter)

	parser.add_argument('vmmon_path', help=r'vmmmon path in VirtualKD (e.g. C:\VirtualKD-3.0\vmmon64.exe)')
	parser.add_argument('target_vmx_path', help=r'vmx path of target vm (e.g. %%UserProfile%%\Documents\Virtual Machines\Windows 7 x86\Windows 7 x86.vmx)')
	parser.add_argument('--run-on-boot', action='store_true', help='let everything run automatically on host boot')

	return parser.parse_args()

def validate_args(args):
	assert os.path.isfile(args.vmmon_path)
	assert os.path.isfile(args.target_vmx_path)

	assert args.vmmon_path.endswith('.exe')
	assert args.target_vmx_path.endswith('.vmx')

def save_args(args):
	with open('../config/env_conf.txt', 'w') as f:
		f.write(json.dumps(vars(args)))

def reg_edit(key_name, reg_dict):
	# TODO: lower priv than winreg.KEY_ALL_ACCESS?
	key = winreg.CreateKeyEx(winreg.HKEY_LOCAL_MACHINE, key_name, reserved=0, access=winreg.KEY_ALL_ACCESS)
	for reg_name, (reg_type, reg_data) in reg_dict.items():
		winreg.SetValueEx(key, reg_name, 0, reg_type, reg_data)

def turn_uac(on_off):

	def bool_to_int(bool_val):
		return ctypes.c_int(bool_val).value

	key_name = r'SOFTWARE\Microsoft\Windows\CurrentVersion\Policies\System'
	reg_dict = {'EnableLUA': (winreg.REG_DWORD, bool_to_int(on_off))}
	reg_edit(key_name, reg_dict)

def set_virtual_kd_configs():
	key_name = r'SOFTWARE\BazisSoft\KdVMWare\Monitor'
	reg_dict = {
		'AutoCloseDebugger': (winreg.REG_DWORD, 0),
		'AutoInvokeDebugger': (winreg.REG_DWORD, 1),
		# reference: https://github.com/sysprogs/VirtualKD/blob/master/vmmon/MainDlg.cpp#L774
		'CustomDebuggerTemplate': (winreg.REG_SZ, r'"$(toolspath)\windbg.exe" -b -k com:pipe,resets=0,reconnect,port=$(pipename) -c "$><{}"'.format(os.path.abspath('on_windbg_startup.txt'))),
		'DebuggerType': (winreg.REG_DWORD, 2),
		'DebugLevel': (winreg.REG_DWORD, 1),
		'InitialBreakIn': (winreg.REG_DWORD, 1),
		'PatchDelay': (winreg.REG_DWORD, 3),
		'ToolsNotInstalled': (winreg.REG_DWORD, 0),
		# TODO: hard coding...
		'ToolsPath': (winreg.REG_SZ, r'C:\Program Files (x86)\Windows Kits\10\Debuggers\x86'),
		'WaitForOS': (winreg.REG_DWORD, 1),
	}
	reg_edit(key_name, reg_dict)

def make_line(data):
    return '{}\n'.format(data)

def add_script_to_startup_dir(run_on_boot):
	script_path = os.path.join(winshell.startup(), 'on_host_boot.bat')

	if run_on_boot:
		with open(script_path, 'w') as f:
			cmds  = make_line('pushd {}'.format(os.getcwd()))
			cmds += make_line('start "" python start_fuzzing.py')
			f.write(cmds)
	else:
		try:
			os.remove(script_path)
		except:
			pass

def make_windbg_script():
	with open('../src/on_windbg_startup.txt', 'w') as f:
		cmds  = make_line('.load msec')
		cmds += make_line('.load pykd')
		cmds += make_line('!py {}'.format(os.path.abspath('on_windbg_run.py')))
		f.write(cmds)
        
if __name__ == '__main__':
	mkdirs()

	args = parse_args()
	validate_args(args)
	save_args(args)

	turn_uac(not args.run_on_boot)
	add_script_to_startup_dir(args.run_on_boot)

	set_virtual_kd_configs()
	make_windbg_script()