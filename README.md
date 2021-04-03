
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


- [ ] Memory management
  - [x] Multi buddy system
  - [ ] Cached allocator(like slab)
  - [ ] Testing
  - [ ] Benchmark
- [ ] Async scheduler: port [async-std](https://github.com/async-rs/async-std)
  - [x] Basic scheduler and yield
  - [x] Mutex/Condvar
  - [ ] RT-Mutex
  - [ ] Benchmark
- [x] Address space: used for mmap
- [ ] Namespace: port [plan9](https://github.com/0intro/plan9)
- [ ] Device model
- [ ] IPC
- [ ] Timer and clock

## Project structure

```
.
├── kmalloc: Buddy system allocator
├── ksched: Async scheduler and synchronization primitives
└── kcore: Address space, namespace and device model
```
