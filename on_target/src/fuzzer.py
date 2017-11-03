import os, glob, json
import time, datetime
import random, z3
import ctypes, win32file
import util
import reproducer

LAST_FUZZ_INFO_FILE_NAME = '../config/last_fuzz_info.txt'

# TODO: Do not backup on target. Do backup on host with WinDbg. or pipe?
# TODO: Store the recent 1000 requests in SQLite.
def backup(dir_name):
    if os.path.exists(LAST_FUZZ_INFO_FILE_NAME):
        num_crashes = len(glob.glob('../{}/*'.format(dir_name)))
        os.rename(LAST_FUZZ_INFO_FILE_NAME, '../{}/{}.txt'.format(dir_name, num_crashes))

def backup_error():
    backup('errors')

def backup_crash():
    backup('crashes')

def init():
    global tries, start_time, drv_handles

    tries       = 0
    start_time  = time.time()
    drv_handles	= {}

def get_drv_handle(dev_name):
    global drv_handles

    if dev_name not in drv_handles.keys():
        drv_handles[dev_name] = util.create_drv_handle(dev_name)

    return drv_handles[dev_name]

def get_rand_drv_dict():
    drv_dicts	= glob.glob('../dicts/*')
    drv_dict	= random.choice(drv_dicts)

    with open(drv_dict) as f:
        return json.load(f)
    
def get_rand_buf_size(cond):
    BIT_NUM = 12

    if cond is None:
        return random.randint(0, 2 ** BIT_NUM - 1)

    z3.set_option('smt.phase_selection', 5)
    z3.set_option('smt.random_seed', random.randint(0, ctypes.c_uint(-1).value // 2))

    x = z3.BitVec('x', BIT_NUM)

    s = z3.Solver()
    s.push()
    s.add(eval(cond))
    s.check()

    return s.model()[x].as_long()

def get_fake_buf_size(buf_size):
    return random.randint(-1, 2 * buf_size)

def gen_rand_fuzz_info():
    drv_dict  	= get_rand_drv_dict()

    dev_name	= drv_dict['dev_name']
    ioctl_dict  = drv_dict['ioctl_dict']

    ioctl_code	= random.choice(list(ioctl_dict.keys()))

    buf_sizes		= list(map(get_rand_buf_size, ioctl_dict[ioctl_code]))
    fake_buf_sizes	= list(map(get_fake_buf_size, buf_sizes))

    if fake_buf_sizes[0] == -1:
        in_buf_raw 	= None
    else:
        in_buf_raw	= ''.join([chr(random.randint(0x00, 0xff)) for i in range(fake_buf_sizes[0])])

    return dict(
        dev_name=dev_name,
        ioctl_code=ioctl_code,
        buf_sizes=buf_sizes,
        fake_buf_sizes=fake_buf_sizes,
        in_buf_raw=in_buf_raw,
    )

def callback_err(err_code):
    if err_code == 6:
        util.notify('Cannot get handle for driver...')

    elif err_code == 998:
        if reproducer.reproduce(LAST_FUZZ_INFO_FILE_NAME):
            backup_error()

    else:
        raise NotImplementedError

def print_status():
    global tries, start_time

    STATUS      = 'tries: {:>10}, run time: {}'
    
    run_time	= time.time() - start_time
    
    print(STATUS.format(tries, datetime.timedelta(seconds=run_time)))

if __name__ == '__main__':
    backup_crash()
    init()

    while True:
        os.system('cls')
        print_status()

        fuzz_info	= gen_rand_fuzz_info()
        with open(LAST_FUZZ_INFO_FILE_NAME, 'w') as f:
            f.write(json.dumps(fuzz_info))
        
        drv_handle	= get_drv_handle(fuzz_info['dev_name'])
        ret_val		= util.do_fuzz(drv_handle, fuzz_info)
        if ret_val == 0:
            util.handle_err(callback_err)

        tries += 1