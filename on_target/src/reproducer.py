import ctypes
import json

import util

def load_crash_info(crash_name):
    with open(crash_name, 'r') as f:
        return json.load(f)

def reproduce(crash_name):
    crash_info  = load_crash_info(crash_name)
    drv_handle  = util.create_drv_handle(crash_info['dev_name'])

    ret_val = util.do_fuzz(drv_handle, crash_info)
    success = ret_val == 0

    if success:
        util.handle_err(None)
    else:
        print('Error: Failed to reproduce crash.')

    ctypes.windll.kernel32.CloseHandle(drv_handle)

    return success

if __name__ == '__main__':
    crash_num   = input('Crash Number: ')
    crash_name  = '../crash/{}.txt'.format(crash_num)
    
    reproduce(crash_name)