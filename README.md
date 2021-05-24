
<h1 align="center">
Plan
<br/></h1>

<p align="center">
Platform-agnostic operating system building blocks in Rust, inspired by <a href="https://9p.io/plan9/">Plan 9</a>.
</p>

<div align="center">
    <a href="../../actions"><img src="../../workflows/CI/badge.svg" alt="CI Status" style="max-width:100%;"></a>
    <a href="../../actions"><img src="../../workflows/Deploy/badge.svg" alt="Deploy Status" style="max-width:100%;"></a>
    <a href="LICENSE"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="License" style="max-width:100%;"></a>
</div>

<br/><br/>

- [x] Memory management
  - [x] Multi buddy system
  - [x] Cached allocator(like slab)
  - [ ] Control with memory limit
- [ ] Task management
  - [x] Basic async scheduler and yield
  - [ ] Timer and sleep
  - [x] O(1) priority scheduler: in fact, it's O(logP), where P is the maximum priority level. Inspired by [RT-Thread](https://github.com/RT-Thread/rt-thread)
  - [x] Mutex/Condvar/Rwlock: doc-test ported from [async-std](https://github.com/async-rs/async-std)
  - [x] IPC: mpsc, can be used to eliminate recusive await
  - [x] Test Mutex/Condvar/RwLock/mpsc
  - [ ] RT-Mutex
  - [ ] Online deadlock detection by wait-for graph: inspired by [parking-lot](https://github.com/Amanieu/parking_lot)
- [x] Address space: inspired by [plan9](https://github.com/0intro/plan9)
- [x] Namespace: inspired by [plan9](https://github.com/0intro/plan9)
- [ ] File system
  - [x] O(1) generic LRU cache
  - [x] Log with read-committed isolation level
  - [x] Transaction-safe FAT32
  - [ ] More FS

## Project structure

```
.
├── kalloc: Buddy system allocator and basic data structures
├── ksched: Async scheduler and synchronization primitives
├── kcore: Address space, namespace and device model
├── kdevice: Device driver such as file system
└── ktest: Common test utils and cases
```
