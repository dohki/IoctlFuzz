# IoctlFuzz
IoctlFuzz, facilitates setting kernel-level-fuzzing-environment. IoctlFuzz works exactly like this.  

![](https://github.com/dohki/IoctlFuzz/blob/master/images/modern_software_development.gif?raw=true)

## Prerequisites
- Windows SDK
- Python 3.x
- VMware and target OS
- VirtualKD
- WinDbg extension: !exploitable, pykd

## Get Started
### on host OS
1. `pip install pykd pypiwin32 winshell`
1. `cd on_host`
1. `python setup.py` as admin.
1. `python start_fuzzing.py` as admin.
### on target OS
1. `pip install pypiwin32 winshell`
1. `cd on_target`
1. `python setup.py`

## Tested On
\# | host OS | target OS
-- | --------------- | ----------------
0 | Windows 10 x64 | Windows 7 x64

## Working On
- [x] coverage-guided fuzzing
- [x] SQLite-based corpus management
- [ ] automated ioctl dict parsing
- [ ] distributed system
- [ ] web interface
