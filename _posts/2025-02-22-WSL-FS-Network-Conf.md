---
layout: post
title:  "WSL -- File System, Networking, Configuration"
categories: [OS]
description: My story with Linux subsystem.
tags: [OS]
---
## Background

I’m a Windows user, and Windows Subsystem Linux (WSL) is the most frequent tool I need to use. 
I use WSL primarily for coding and dev, while Windows for entertaining.
My goal is **not installing anything related to coding in Windows**.
However, I find that I have little knowledge about how it works.
It sometimes makes me confused. 
So I decided to spend sometime and take a note about it.

## Overview

WSL 2 uses virtualization to run a Linux kernel inside a VM.
WSL 2 features
- Faster File IO
- Full System Call Compatibility
		This allows full access to Linux apps like Docker (why) 

Architecture Change from WSL 1
- WSLv1 uses a translation-based approach, which translates a Linux system call to Windows kernel. 
		This approach can be less compatible because system calls in win and Linux can have different semantics. 
		It also slows down the IO speed somehow.
- WSLv2 is VM-based approach. It has a full Linux kernel. 

## Working with File System

You can run Linux tools from a Windows Command Line

```bash
#powershell
wsl ls -la
wsl ls -la "/mnt/c/Program Files" # note that you need to use linux file path  
```

You can also run Windows tools in WSL by `[tool-name].exe` 

```shell
#bash
ipconfig.exe | grep IPv4 | cut -d: -f2
```

## Configuration

WSL allows user providing a configuration file `%UserProfile%/.wslconfig`. 
See [Main WSL Settings](https://learn.microsoft.com/en-us/windows/wsl/wsl-config#main-wsl-settings) for the full configuration table.

By the way, I prefer using WSL setting app for config. 

## Networking Consideration

Currently, WSL2 offers two modes of networking: NAT and Mirrored.

### NAT Mode

NAT Mode means that WSL is running in a **virtualized network environment** where it is assigned with a **private IP address**, and Windows serves as the adapter. 

**Accessing Internet from WSL**

WSL runs on NAT mode implies that Windows serves as the adapter, rewriting request from WSL with its IP. 

Try this:
```
> wsl curl 'https://api.ipify.org?format=json'
> curl 'https://api.ipify.org?format=json'
```

The API simply returns the IP of the client. 
You can see that both are identical and is the IP address of the Windows.

Another experiment is that, you can trace network packets:
```bash
traceroute google.com # On wsl
```

```bash
tracert google.com # On wsl
```

You will find that both are identical **except there is one more jump from WSL to Windows** 

**Accessing WSL from Windows**

On Windows, you can access networking apps in WSL using localhost. There is an auto-forwarding feature working: 
![Experiment: Accessing WSL Networking application ](/assets/images/Pasted%20image%2020250222170500.png)

You can also access networking apps by using the assigned IP address of WSL. 

The Windows host can use this command to query the IP address 
```powershell
> wsl -d <DistributionName> hostname -I
```

**Accessing WSL from LAN**

To enable devices on your LAN to access WSL, it needs proper proxy setup. See [Accessing a WSL 2 distribution from your local area network (LAN)](https://learn.microsoft.com/en-us/windows/wsl/networking#accessing-a-wsl-2-distribution-from-your-local-area-network-lan)

### Mirrored Networking Mode

In mirrored mode, WSL works as **if they are the same machine in network**. Benefits are:
- IPv6 Support
- Connect to Windows servers from within Linux using the localhost address `127.0.0.1`.
- Improved networking compatibility for VPNs
- Connect to WSL directly from your local area network (LAN)

It implies that both Windows and WSL Apps connect to the same physical network of the Windows host. 

The VM “mirrors” all network settings from Windows. 

This can be validate by tracing network parcels:

```
# on WSL
traceroute google.com
```

You will find there is not a jump to Windows host. 

The only thing we know about the implementation is that it utilizes Hyper-V virtual switch feature. 
MS do not share more detailed information about it.

# References
1. MS WSL Doc https://learn.microsoft.com/en-us/windows/wsl/about
2. Intro to WSL2 Video https://youtu.be/MrZolfGm8Zk?si=pRhVjzF84i49Zoqi