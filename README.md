
<h1 align="center">
Plan
<br/></h1>

<p align="center">
Platform-agnostic operating system building blocks in Rust.
</p>

<div align="center">
    <a href="../../actions"><img src="../../workflows/CI/badge.svg" alt="CI Status" style="max-width:100%;"></a>
    <a href="../../actions"><img src="../../workflows/Deploy/badge.svg" alt="Deploy Status" style="max-width:100%;"></a>
    <a href="LICENSE"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="License" style="max-width:100%;"></a>
</div>

<br/><br/>

## Introduction

Plan is a set of operating system building blocks, focusing on correctness, efficiency and maintainability. It contains practical and common modules to facilitate the construction of operating systems, but can also be used for other infrastructure software where fallible allocation is required, such as databases.

## Goals and Non-Goals

Our primary goal is to provide a correct library. When we talk about the correctness of a system, we are actually discussing both of safety and liveness. With the help of Rust's ownership model, safety can be guaranteed by carefully reasoning about unsafe code. Undefined behavior is forbidden in Plan. As for liveness, Plan is required to be starvation-free. Any operation in Plan must return in bounded time if called properly and all the hardwares involved work normally. Note that starvation-free implies panic-free, so even panic is not allowed.

Besides, efficiency and maintainability are taken into account due to the characteristic of infrastructure software.

Other objectives include

- Less is more, salute to minimalism.
- The ability to compatible with POSIX.


And the following ones are intentionally listed for non-goals.

- Not ISA or SoC specific, as the name suggests.
- No need to compatible with other file systems.
- No network socket, network must be abstract as file system or device.

## Features

- Memory management
  - [x] Multi buddy system
  - [x] Cached allocator
  - [ ] Customized data structures with allocator to support multi-tenant
- Scheduler and synchronization primitives
  - [x] Fair-share scheduling by DWRR<sup>[1]</sup> algorithm
  - [x] Fixed priority pre-emptive scheduling for real-time systems
  - [x] Mutex/Condvar/Rwlock
  - [ ] Timer
  - [ ] RT-Mutex
- Core structures and isolation
  - [x] VFS layer supporting namespace
  - [ ] Virtual memory with on-demand paging
  - [ ] Pager daemon
- Device drivers and file systems
  - [ ] Transaction service with serializable isolation
  - [ ] Log layer
  - [x] Transaction-safe FAT32
  - [x] Root/block/pipe device
  - [ ] Get directory entry
  - [ ] Temporary file system
  - [ ] More FS

## Project Status

This project is still under heavy development.

## References

[1] Li, Tong, Dan Baumberger, and Scott Hahn. "Efficient and scalable multiprocessor fair scheduling using distributed weighted round-robin." ACM Sigplan Notices 44.4 (2009): 65-74.
