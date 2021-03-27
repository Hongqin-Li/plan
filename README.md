
<h1 align="center">
SeRT
<br/></h1>

<p align="center">
A Secure Fork of RT-Thread Nano in Rust
</p>

<div align="center">
    <a href="../../actions"><img src="../../workflows/CI/badge.svg" alt="CI Status" style="max-width:100%;"></a>
    <a href="../../actions"><img src="../../workflows/Deploy/badge.svg" alt="Deploy Status" style="max-width:100%;"></a>
    <a href="LICENSE"><img src="https://img.shields.io/badge/license-MIT-blue.svg" alt="License" style="max-width:100%;"></a>
</div>

<br/><br/>


- [x] Github CI and doc.
- [ ] Memory management.
  - [x] Multi buddy system.
  - [ ] Cached allocator.(like slab)
  - [ ] Testing.
  - [ ] Benchmark.
- [ ] Async scheduler: port [async-std](https://github.com/async-rs/async-std)
  - [x] Basic scheduler and yield.
  - [x] Mutex/Condvar.
  - [ ] RT-Mutex.
  - [ ] Benchmark.
- [ ] IPC
- [ ] Timer and clock.

This is a Rust port of [RT-Thread Nano](https://github.com/RT-Thread/rtthread-nano) focusing on correctness and efficiency.

## Project structure


