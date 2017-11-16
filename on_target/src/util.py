import ctypes, ctypes.wintypes
import win32file

def make_line(data):
    return '{}\n'.format(data)

def notify(data):
    print('[*] {}'.format(data))

def print_err(err_code): 
		
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
    
    buf = ctypes.wintypes.LPSTR()

    ctypes.windll.kernel32.FormatMessageA(
        get_fmt_msg_flag(),
        None,
        err_code,
        get_lcid_eng(),
        ctypes.byref(buf),
        0,
        None
    )

    err_msg = buf.value.decode('utf-8').strip()

    notify('Error: {} ({})'.format(err_msg, err_code))

def create_drv_handle(dev_name):
    notify('Creating Driver Handle for {}...'.format(dev_name))
    
    drv_handle = ctypes.windll.kernel32.CreateFileW(
        dev_name, 
        win32file.GENERIC_READ | win32file.GENERIC_WRITE,
        0,
        None,
        win32file.OPEN_EXISTING,
        None,
        0
    )

    notify('Got Driver Handle {}'.format(drv_handle))

    return drv_handle

def get_bufs(in_buf_raw, fake_out_buf_size):
    if in_buf_raw is None:
        in_buf  = None
    else:
	    in_buf	= ctypes.create_string_buffer(in_buf_raw.encode('utf-8'))

    if fake_out_buf_size == -1:
        out_buf = None
    else:
        out_buf = ctypes.create_string_buffer(fake_out_buf_size)
        
    ret_buf = ctypes.c_ulong()

    '''
    def get_addr(buf):
        return '0x{:x}'.format(ctypes.addressof(buf))

    print(list(map(lambda x: get_addr(x), [in_buf])))#, out_buf, ret_buf])))
    '''

    return in_buf, out_buf, ret_buf

def do_fuzz(drv_handle, fuzz_info):
    in_buf, out_buf, ret_buf = get_bufs(fuzz_info['in_buf_raw'], fuzz_info['fake_buf_sizes'][1])

    return ctypes.windll.kernel32.DeviceIoControl(
        drv_handle,
        fuzz_info['ioctl_code'],
        in_buf,
        fuzz_info['buf_sizes'][0],
        out_buf,
        fuzz_info['buf_sizes'][1],
        ctypes.byref(ret_buf),
        None
    )

def handle_err(callback_err):
    err_code = ctypes.windll.kernel32.GetLastError()
    
    assert err_code != 0

    print_err(err_code)

    try:
        if callback_err is not None:
            callback_err(err_code)
        
    except NotImplementedError:
        # TODO: mail
        notify('New Error!')
        input()