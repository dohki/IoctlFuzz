import platform
import winreg
import json
import subprocess
import os

__author__ = 'illuxic'

def load_configs():
	with open('configs.txt', 'r') as f:
		return json.load(f)

def run_vmmon(vmmon_path):
	subprocess.Popen([vmmon_path])

def run_target_vm(target_vmx_path):
	nbit = platform.architecture()[0]
	optional_path = r'\WOW6432Node' if nbit == '64bit' else ''

	key_name = r'SOFTWARE{}\VMware, Inc.\VMware Workstation'.format(optional_path)
	key = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, key_name, reserved=0, access=winreg.KEY_READ)
	vmware_install_path = winreg.QueryValueEx(key, 'InstallPath')[0]

	vmrun_path = os.path.join(vmware_install_path, 'vmrun.exe')
	subprocess.Popen([vmrun_path, 'start', target_vmx_path])

if __name__ == '__main__':
	configs = load_configs()

	run_vmmon(configs['vmmon_path'])
	run_target_vm(configs['target_vmx_path'])