# AWDFE
AWDFE, which stands for Automated Windows Driver Fuzzing Environment, facilitate Windows driver fuzzing as its name indicates. AWDFE works exactly like below.  

## Prerequisites
- Visual Studio 2015 (**NOT** 2017)
- Windows SDK
- WDK
- Python 3.x
- git
- VMware and target OS
- VirtualKD
- !exploitable (WinDbg extension)

## Get Started
### on host OS
1. Issue `python setup.py` as admin.
2. Issue `python start_fuzzing.py` as admin.
3. Copy `AWDFE/on_target` to target OS.
### on target OS
1. `python setup.py`
2. `python ioctl_fuzzer.py`

## Tested On
\# | host OS | target OS
-- | --------------- | ----------------
0 | Windows 10 x64 | Windows 7 x64

## Further Improvement
- to validate and automate `IDA` ioctl script `win_driver_plugin`
- master/slave task management
- web interface
- fuzzer logic