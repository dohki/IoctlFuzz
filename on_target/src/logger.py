#import threading
import psutil
import pydbg, utils
import ctypes

# TODO: Hook multiple processes with one logger using threads.
class Logger(object):

    def __init__(self):
        self.hooks = utils.hook_container()
        #self.threads    = []

    def add(self, proc_name):
        for proc in psutil.process_iter():
            if proc.name().lower() == proc_name.lower():
                print '[{}] {}'.format(proc.pid, proc.name())

                dbg = pydbg.pydbg()
                dbg.attach(proc.pid)
                hook_addr = dbg.func_resolve_debuggee('kernel32.dll', 'DeviceIoControl')
                self.hooks.add(dbg, hook_addr, 8, self.log, None)
                dbg.run()

                '''
                th = threading.Thread(target=dbg.run)
                self.threads.append(th)
                '''

    def log(self, dbg, args):
        print '-' * 10

        for i in xrange(8):
            print args[i]

        '''
        size    = 100
        buf     = ctypes.create_string_buffer(size)
        ret_val = ctypes.windll.kernel32.GetFinalPathNameByHandleW(args[0], buf, size, 0)

        if ret_val == 0:
            util.handle_err()

        print buf
        print dir(buf)
        '''

        return pydbg.defines.DBG_CONTINUE

    '''
    def start(self):
        for th in self.threads:
            th.start()
    '''

if __name__ == '__main__':
    proc_name = raw_input('Process Name: ')

    logger = Logger()
    logger.add(proc_name)
    #logger.start()