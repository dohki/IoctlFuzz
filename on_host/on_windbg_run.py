import pykd
import os
import re
import sys
import getpass


__author__ = 'illuxic'


def make_line(data):
    return '{}\n'.format(data)


class ExceptionHandler(pykd.eventHandler):

    def __init__(self):
        pykd.eventHandler.__init__(self)

        self.except_info = None

    def is_crash(self, except_info):
        return False if except_info is None else (not except_info.firstChance) # second chance (=crash)

    def is_breakpoint(self, except_info):
        return False if except_info is None else (except_info.exceptionCode == 0x80000003)

    def got_crash(self):
        return self.is_crash(self.except_info)

    def got_breakpoint(self):
        return self.is_breakpoint(self.except_info)

    # override
    def onException(self, new_except_info):
        if self.is_crash(new_except_info) or self.is_breakpoint(new_except_info):
            self.except_info = new_except_info

            return pykd.eventResult.Break
        else:
            return pykd.eventResult.NoChange        


class Debugger:

    def __init__(self):
        self._exception_handler = ExceptionHandler()

    def dbg_cmd(self, cmd):
        try:
            result  = pykd.dbgCommand(cmd)
        except pykd.DbgException as e:
            result  = make_line('[*] Error for [ {} ]:'.format(cmd))
            result += make_line(str(e))
        
        return result 

    def shell(self):
        while True:
            cmd = input('{}@AWDFE:~$ '.format(getpass.getuser()))
            if cmd == 'exit':
                break

            result = self.dbg_cmd(cmd)
            if result is not None:
                print(result)

    def run_until_crash(self):
        while True:
            if self._exception_handler.got_breakpoint():
                self.shell()

            # You can have crash while interacting with shell.
            if self._exception_handler.got_crash():
                break

            pykd.go()

    # TODO: is .dump worth?
    def dump_crash(self):
        exploitable_report = self.dbg_cmd('!exploitable -v')

        # TODO: Do not split. Make it using re.M.
        for line in exploitable_report.split('\n'):
            m = re.match('^Exception Hash.*: (.*)$', line, flags=re.M)
            if m is not None:
                break

        crash_hash = m.group(1)
        # TODO: Is pykd using python interactive? Why not __file__ instead of sys.argv[0]?
        base_path = os.path.abspath(os.path.join(sys.argv[0], os.pardir, os.pardir))  
        crash_path = os.path.join(base_path, 'results', crash_hash)

        if not os.path.exists(crash_path):
            os.mkdir(crash_path)

        with open(os.path.join(crash_path, 'exploitable_report.txt'), 'w') as f:
            f.write(exploitable_report)

        with open(os.path.join(crash_path, 'crash_report.txt'), 'w') as f:
            cmds = ['ub eip', 'r', 'kb']
            crash_report = ''
            for cmd in cmds:
                crash_report += make_line(self.dbg_cmd(cmd))
            f.write(crash_report)
            
            
if __name__ == '__main__':
    dbg = Debugger()
    dbg.run_until_crash()
    dbg.dump_crash()
    dbg.dbg_cmd('.reboot')  # Let WinDbg reboot target OS.
    dbg.dbg_cmd('.restart') # Let WinDbg run this script newly.