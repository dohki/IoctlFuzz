import json
import util

def load_crash_info(crash_num):
    with open('../crashes/{}.txt'.format(crash_num), 'r') as f:
        return json.load(f)

def handle_err():
    err_code = ctypes.windll.kernel32.GetLastError()

    assert err_code != 0
	
    util.print_err(err_code)

if __name__ == '__main__':
    crash_num   = input('Crash Number: ')
    crash_info  = load_crash_info(crash_num)

    drv_handle  = util.create_drv_handle(crash_info['dev_name'])

    ret_val = util.do_fuzz(drv_handle, crash_info)
    if ret_val == 0:
        handle_err()
    else:
        print('Error: Failed to reproduce crash.')