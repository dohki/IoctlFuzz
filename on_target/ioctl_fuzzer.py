import random
import ctypes
import json

GENERIC_READ    = 0x80000000
GENERIC_WRITE   = 0x40000000
OPEN_EXISTING   = 0x3

def load_data():
    '''
    with open('data.txt') as f:
        return json.load(f)
    '''
    raise NotImplementedError

def get_valid_devices(devices):
    valid_devices = []
    for device in devices:
        device_filename = r'\\.\{}'.format(device.split('\\')[-1])
        driver_handle = ctypes.windll.kernel32.CreateFileW(device_filename, GENERIC_READ | GENERIC_WRITE, 0, None, OPEN_EXISTING, 0, None)
        if driver_handle:
            if device_filename not in valid_devices:
                valid_devices.append(device_filename)
            
            ctypes.windll.kernel32.closeHandle(driver_handle)

    return valid_devices

if __name__ == '__main__':
    data = load_data()
    valid_devices = get_valid_devices(data['devices'])
    ioctl_codes = data['ioctl_codes'] # Do we need to validate here? or in IDA?

    assert len(valid_devices) > 0
    assert len(valid_ioctl_codes) > 0

    while True:
        with open('last_fuzzing_info.txt') as f:
            device = random.choice(valid_devices)
            ioctl_code = random.choice(ioctl_codes)

            length = random.randint(0,10000)
            in_buf = [random.randint(0x00, 0xff) for i in xrange(length)]
            out_buf = (c_char * len)()
            bytes_returned = c_ulong(len)

            driver_handle = ctypes.windll.kernel32.CreateFile(device, GENERIC_READ | GENERIC_WRITE, 0, None, OPEN_EXISTING, 0, None)
            ctypes.windll.kernel32.DeviceIoControl(driver_handle, ioctl_code, in_buf, len, byref(out_buf), len, byref(bytes_returned), None)
            ctypes.windll.kernel32.CloseHandle(driver_handle)

            info = dict(device=device, ioctl_code=ioctl_code, in_buf=in_buf)
            f.write(json.dump(info))