import ctypes, ctypes.wintypes

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

		print('')
		print('Error: {} ({})'.format(err_msg, err_code))
		print('')