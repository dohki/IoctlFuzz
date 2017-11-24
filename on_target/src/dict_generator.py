import re
import json
import ctypes
import win32file

import util

def get_dict_name():
    DRV_EXTS     = ['386', 'drv', 'dsk', 'lan', 'nlm', 'sys', 'vxd']
    DRV_EXT_PAT  = '\.({})$'.format('|'.join(DRV_EXTS))
    
    def is_valid(drv_name):
        return re.match('\w+{}'.format(DRV_EXT_PAT), drv_name) is not None

    while True:
        drv_name = input('Driver Name: ')
        if is_valid(drv_name):
            util.hr()

            return re.sub(DRV_EXT_PAT, '.txt', drv_name)
        else:
            util.notify_err('Not a driver extension')

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
        dev_name = input('Device Name: ')
        if dev_name == 'pass' or is_valid(dev_name):
            util.hr()
            
            return dev_name
        else:
            util.notify_err('Cannot get drvier handle for this device name')

def get_ioctl_dict():

    def is_valid(ioctl_item):
        return len(ioctl_item) == 3

    ioctl_dict = {}
    while True:
        ioctl_item = input('IOCTL Item: ').strip()
        
        if not ioctl_item:
            continue

        elif ioctl_item == 'done':
            return ioctl_dict

        ioctl_item = list(map(lambda e: e.strip(), ioctl_item.split(';')))
        if not is_valid(ioctl_item):
            util.notify_err('Format is {ioctl_code}; {in_buf_size_cond}; {out_buf_size_cond}')
            continue

        # TODO: Ensure z3 expression.
        ioctl_code		= ioctl_item[0]
        buf_size_conds	= ioctl_item[1:]
        ioctl_dict[ioctl_code] = list(map(lambda e: None if not e else e, buf_size_conds))

if __name__ == '__main__':
    dict_name   = get_dict_name()
    info        = dict(dev_name=get_dev_name(), ioctl_dict=get_ioctl_dict())

    with open('../dict/{}'.format(dict_name), 'w') as f:
        f.write(json.dumps(info))