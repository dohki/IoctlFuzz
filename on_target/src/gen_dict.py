import re
import json

def get_file_name():
	DRV_EXTS     = ['386', 'drv', 'dsk', 'lan', 'nlm', 'sys', 'vxd']
	DRV_EXT_PAT  = '\.({})$'.format('|'.join(DRV_EXTS))
	
	def is_valid(drv_name):
		return re.match('\w+{}'.format(DRV_EXT_PAT), drv_name) is not None

	while True:
		drv_name = input('Driver Name: ')
		if is_valid(drv_name):
			break
		else:
			print('Error: This extension is not for drivers.')

	return re.sub(DRV_EXT_PAT, '.txt', drv_name)

def get_dev_names():
	
	def is_valid(dev_name):
		drv_handle = ctypes.windll.kernel32.CreateFileW(
			dev_name, 
			win32file.GENERIC_READ | win32file.GENERIC_WRITE,
			0, 
			None, 
			win32file.OPEN_EXISTING, 
			0, 
			None
			)

		if drv_handle:
			ctypes.windll.kernel32.CloseHandle(drv_handle)
			return True
		else:
			return False

	while True:
		dev_name = '\\\\.\\{}'.format(input())
		if is_valid(dev_name):
			return dev_name
		else:
			print('Error: Cannot get drvier handle with this device name.')

def get_ioctl_dict():

	def is_valid(ioctl_item):
		return len(ioctl_item) == 3

	print('IOCTL dict:')

	ioctl_dict = {}
	while True:
		ioctl_item = input()
		if not ioctl_item:
			break

		ioctl_item = list(map(lambda e: e.strip(), ioctl_item.split(',')))
		if not is_valid(ioctl_item):
			print('Error: Format should be {ioctl code}, {in_buf_size_cond}, {out_buf_size_cond}.')
			continue

		# TODO: Ensure z3 expression.
		ioctl_code		= ioctl_item[0]
		buf_size_conds	= ioctl_item[1:]
		ioctl_dict[ioctl_code] = list(map(lambda e: None if not e else e), buf_size_conds)

	return ioctl_dict

if __name__ == '__main__':
	file_name = get_file_name()
	info = dict(dev_names=get_dev_names(), ioctl_dict=get_ioctl_dict())

	with open('../dicts/{}'.format(file_name), 'w') as f:
		f.write(json.dumps(info))