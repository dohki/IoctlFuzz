import random
import ctypes
import json
import glob
import os

GENERIC_READ    = 0x80000000
GENERIC_WRITE   = 0x40000000
OPEN_EXISTING   = 0x3

# TODO: Do not backup on target. Do backup on host with WinDbg.
def backup():
    backups = glob.glob(os.path.join('backups', '*'))
    try:
        os.rename('last_fuzz_info.txt', os.path.join('backups', '{}.txt'.format(len(backups))))
    except FileNotFoundError:
        pass

def choose_item():
    items   = glob.glob(os.path.join('ioctl_items', '*'))
    item    = random.choice(items)

    return item

def load_item(item):
    with open(item) as f:
        return json.load(f)
    
def get_valid_devices(devices):
    
    def beautify_device(device):
        return r'\\.\{}'.format(device.split('\\')[-1])
    
    def is_valid_device(device):
        driver_handle   = ctypes.windll.kernel32.CreateFileW(device, GENERIC_READ | GENERIC_WRITE, 0, None, OPEN_EXISTING, 0, None)
        if driver_handle:
            ctypes.windll.kernel32.CloseHandle(driver_handle)
            return True
        else:
            return False

    return list(filter(is_valid_device, list(set(map(beautify_device, devices)))))

def get_len(length):
    if length is None:
        return random.randint(0, 100)
    else:
        return length

def get_fake_len(length):
    if length is None:
        return random.randint(0, 100)
    else:
        return length + random.randint(-1 * length, length)

if __name__ == '__main__':
    backup()

    i = 0
    while True:
        if i % 1000 == 0:
            print(i, end='\r')
        
        item                = choose_item()
        devices, ioctl_sets = load_item(item)
        valid_devices       = get_valid_devices(devices)

        device                              = random.choice(valid_devices)
        ioctl_code                          = random.choice(list(ioctl_sets.keys()))
        out_buf_len, in_buf_len             = map(get_len,      ioctl_sets[ioctl_code])
        fake_out_buf_len, fake_in_buf_len   = map(get_fake_len, ioctl_sets[ioctl_code])

        out_buf = (ctypes.c_char * fake_out_buf_len)()
        in_buf  = ''.join([chr(random.randint(0x00, 0xff)) for i in range(fake_in_buf_len)])
        ret_buf = ctypes.c_ulong(random.randint(0, 100))

        info = dict(item=item, device=device, fake_out_buf_len=fake_out_buf_len, fake_in_buf_len=fake_in_buf_len, in_buf=in_buf, ioctl_code=ioctl_code)
        with open('last_fuzz_info.txt', 'w') as f:
            f.write(json.dumps(info))

        driver_handle = ctypes.windll.kernel32.CreateFileW(device, GENERIC_READ | GENERIC_WRITE, 0, None, OPEN_EXISTING, 0, None)
        ret_val = ctypes.windll.kernel32.DeviceIoControl(driver_handle, ioctl_code, in_buf, in_buf_len, ctypes.byref(out_buf), out_buf_len, ctypes.byref(ret_buf), None)
        if ret_val == 0:
            print('Error Code: {}'.format(ctypes.windll.kernel32.GetLastError()))
        ctypes.windll.kernel32.CloseHandle(driver_handle)

        i += 1
