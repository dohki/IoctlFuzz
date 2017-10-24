import os, glob, json
import time, datetime
import random, z3
import ctypes, win32file

# TODO: Do not backup on target. Do backup on host with WinDbg. or pipe?
# TODO: Store the recent 1000 requests in SQLite.
def backup():
	backups = glob.glob('../crashes/*')
	try:
		os.rename('../crashes/last_fuzz_info.txt', 'crashes/{}.txt'.format(len(backups)))
	except FileNotFoundError:
		pass

def init():
	global tries, start_time, drv_handles

	tries       = 0
	start_time  = time.time()
	drv_handles	= {}

def print_status():
	global tries, start_time

	STATUS      = 'tries: {:>10}, run time: {}'
	run_time    = datetime.timedelta(seconds=time.time() - start_time)
	print(STATUS.format(tries, run_time), end='\r')

def print_result(ret_val): 
	if ret_val == 0:
		print('Error Code: {}'.format(ctypes.windll.kernel32.GetLastError()))

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
	return random.randint(buf_size - buf_size // 2, buf_size + buf_size // 2)

# TODO: Optimize
def get_bufs(fake_in_buf_size, fake_out_buf_size):
	corpus	= ''.join([chr(random.randint(0x00, 0xff)) for i in range(fake_in_buf_size)])

	in_buf	= ctypes.create_string_buffer(corpus.encode('utf-8'))
	out_buf = ctypes.create_string_buffer(fake_out_buf_size)

	in_buf	= random.choice([None, in_buf])
	out_buf = random.choice([None, out_buf])

	ret_buf = ctypes.c_ulong(random.randint(0, ctypes.c_ulong(-1).value))
	
	return in_buf, out_buf, ret_buf

def get_drv_handle(dev_name):
	global drv_handles

	if dev_name not in drv_handles.keys():
		drv_handles[dev_name] = ctypes.windll.kernel32.CreateFileW(
			dev_name, 
			win32file.GENERIC_READ | win32file.GENERIC_WRITE,
			0, 
			None, 
			win32file.OPEN_EXISTING, 
			0, 
			None
		)

	return drv_handles[dev_name]

if __name__ == '__main__':
	backup()
	init()

	while True:
		print_status()
		
		drv_dict  	= get_rand_drv_dict()

		dev_name	= drv_dict['dev_name']
		ioctl_dict  = drv_dict['ioctl_dict']

		ioctl_code	= random.choice(list(ioctl_dict.keys()))

		buf_sizes		= map(get_rand_buf_size, ioctl_dict[ioctl_code])
		fake_buf_sizes	= map(get_fake_buf_size, buf_sizes)

		in_buf, out_buf, ret_buf = get_bufs(*fake_buf_sizes)	
		
		info = dict(
			dev_name=dev_name,
			ioctl_code=ioctl_code,
			buf_sizes=buf_sizes,
			fake_buf_sizes=fake_buf_sizes,
			in_buf=in_buf,
		)

		ret_val = ctypes.windll.kernel32.DeviceIoControl(
			get_drv_handle(dev_name),
			ioctl_code,
			in_buf, in_buf_size,
			out_buf, out_buf_size,
			ctypes.byref(ret_buf),
			None
		)

		print_result(ret_val)
		
		tries += 1