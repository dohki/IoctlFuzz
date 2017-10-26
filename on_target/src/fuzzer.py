import os, glob, json
import time, datetime
import random, z3
import ctypes, ctypes.wintypes, win32file

LAST_FUZZ_INFO_FILE_NAME = '../config/last_fuzz_info.txt'

# TODO: Do not backup on target. Do backup on host with WinDbg. or pipe?
# TODO: Store the recent 1000 requests in SQLite.
def backup():
	if os.path.exists(LAST_FUZZ_INFO_FILE_NAME):
		num_crashes = len(glob.glob('../crashes/*'))
		os.rename(LAST_FUZZ_INFO_FILE_NAME, '../crashes/{}.txt'.format(num_crashes))

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

def print_error(): 
	
	def get_fmt_msg_flag():
		FORMAT_MESSAGE_ALLOCATE_BUFFER	= 0x00000100
		FORMAT_MESSAGE_FROM_SYSTEM		= 0x00001000
		FORMAT_MESSAGE_IGNORE_INSERTS	= 0x00000200

		return FORMAT_MESSAGE_ALLOCATE_BUFFER | FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS

	def get_lcid_eng():
		
		def MAKELANGID(primary_lang, sub_lang):
			return (primary_lang & 0xff) | (sub_lang & 0xff) << 10

		LANG_ENGLISH		= 0x09
		SUBLANG_ENGLISH_US	= 0x01
		LCID_ENGLISH		= MAKELANGID(LANG_ENGLISH, SUBLANG_ENGLISH_US)

		return LCID_ENGLISH

	error_code	= ctypes.windll.kernel32.GetLastError()
	if error_code == 0:
		return

	buf = ctypes.wintypes.LPSTR()

	ctypes.windll.kernel32.FormatMessageA(
		get_fmt_msg_flag(),
		None,
		error_code,
		get_lcid_eng(),
		ctypes.byref(buf),
		0,
		None
	)

	error_msg = buf.value.decode('utf-8').strip()

	print('')
	print('Error: {} ({})'.format(error_msg, error_code))
	print('')

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

def save_fuzz_info(info):
	with open(LAST_FUZZ_INFO_FILE_NAME, 'w') as f:
		f.write(json.dumps(info))

def get_drv_handle(dev_name):
	global drv_handles

	if dev_name not in drv_handles.keys():
		drv_handles[dev_name] = ctypes.windll.kernel32.CreateFileW(
			dev_name, 
			win32file.GENERIC_READ | win32file.GENERIC_WRITE,
			0, 
			None, 
			win32file.OPEN_EXISTING, 
			None,
			0, 
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

		buf_sizes		= list(map(get_rand_buf_size, ioctl_dict[ioctl_code]))
		fake_buf_sizes	= list(map(get_fake_buf_size, buf_sizes))

		in_buf_size, out_buf_size	= buf_sizes
		in_buf, out_buf, ret_buf 	= get_bufs(*fake_buf_sizes)	

		in_buf_raw 	= in_buf.raw.decode('utf-8') if in_buf is not None else None
		
		info = dict(
			dev_name=dev_name,
			ioctl_code=ioctl_code,
			buf_sizes=buf_sizes,
			fake_buf_sizes=fake_buf_sizes,
			in_buf_raw=in_buf_raw,
		)
		save_fuzz_info(info)

		ret_val = ctypes.windll.kernel32.DeviceIoControl(
			get_drv_handle(dev_name),
			ioctl_code,
			in_buf, in_buf_size,
			out_buf, out_buf_size,
			ctypes.byref(ret_buf),
			None
		)

		if ret_val == 0:
			print_error()
		
		tries += 1