import re
import json
import ctypes
import win32file
import util

def teardown():
    for i in range(2):
        print('-' * 100)

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

    teardown()

    return re.sub(DRV_EXT_PAT, '.txt', drv_name)

def get_dev_name():
    
    def is_valid(dev_name):
        util.notify('Validating device name...')

        drv_handle = util.create_drv_handle(dev_name)

        if drv_handle != -1:
            ctypes.windll.kernel32.CloseHandle(drv_handle)
            return True
        else:
            return False

    while True:
        dev_name = '\\\\.\\{}'.format(input('Device Name: '))
        if is_valid(dev_name):
            print('OK')
            teardown()

            return dev_name
        else:
            print('Error: Cannot get drvier handle with this device name.')

def get_ioctl_dict():

    def is_valid(ioctl_item):
        return len(ioctl_item) == 3

    ioctl_dict = {}
    while True:
        ioctl_item = input('IOCTL Item: ')
        if not ioctl_item:
            break

        ioctl_item = list(map(lambda e: e.strip(), ioctl_item.split(',')))
        if not is_valid(ioctl_item):
            print('Error: Format should be {ioctl code}, {in_buf_size_cond}, {out_buf_size_cond}.')
            continue

        # TODO: Ensure z3 expression.
        ioctl_code		= ioctl_item[0]
        buf_size_conds	= ioctl_item[1:]
        ioctl_dict[ioctl_code] = list(map(lambda e: None if not e else e, buf_size_conds))

    return ioctl_dict

if __name__ == '__main__':
    file_name = get_file_name()
    info = dict(dev_name=get_dev_name(), ioctl_dict=get_ioctl_dict())

    with open('../dicts/{}'.format(file_name), 'w') as f:
        f.write(json.dumps(info))