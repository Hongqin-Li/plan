(function() {var implementors = {};
implementors["kcore"] = [{"text":"impl&lt;P&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"kcore/vm/struct.Page.html\" title=\"struct kcore::vm::Page\">Page</a>&lt;P&gt;","synthetic":true,"types":["kcore::vm::Page"]},{"text":"impl&lt;P&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"kcore/vm/struct.SegmentInner.html\" title=\"struct kcore::vm::SegmentInner\">SegmentInner</a>&lt;P&gt;","synthetic":true,"types":["kcore::vm::SegmentInner"]},{"text":"impl&lt;P&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"enum\" href=\"kcore/vm/enum.Segment.html\" title=\"enum kcore::vm::Segment\">Segment</a>&lt;P&gt;","synthetic":true,"types":["kcore::vm::Segment"]},{"text":"impl&lt;P&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"kcore/vm/struct.AddressSpace.html\" title=\"struct kcore::vm::AddressSpace\">AddressSpace</a>&lt;P&gt;","synthetic":true,"types":["kcore::vm::AddressSpace"]}];
implementors["kmalloc"] = [{"text":"impl&lt;P&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"kmalloc/buddy/struct.BuddySystem.html\" title=\"struct kmalloc::buddy::BuddySystem\">BuddySystem</a>&lt;P&gt;","synthetic":true,"types":["kmalloc::buddy::BuddySystem"]},{"text":"impl&lt;P&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"kmalloc/buddy/struct.MultiBuddySystem.html\" title=\"struct kmalloc::buddy::MultiBuddySystem\">MultiBuddySystem</a>&lt;P&gt;","synthetic":true,"types":["kmalloc::buddy::MultiBuddySystem"]},{"text":"impl&lt;P&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"kmalloc/buddy/struct.Allocator.html\" title=\"struct kmalloc::buddy::Allocator\">Allocator</a>&lt;P&gt;","synthetic":true,"types":["kmalloc::buddy::Allocator"]},{"text":"impl&lt;T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"kmalloc/cached/struct.Cached.html\" title=\"struct kmalloc::cached::Cached\">Cached</a>&lt;T&gt;","synthetic":true,"types":["kmalloc::cached::Cached"]},{"text":"impl&lt;P&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"kmalloc/cached/struct.Allocator.html\" title=\"struct kmalloc::cached::Allocator\">Allocator</a>&lt;P&gt;","synthetic":true,"types":["kmalloc::cached::Allocator"]}];
implementors["ksched"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"ksched/condvar/struct.Condvar.html\" title=\"struct ksched::condvar::Condvar\">Condvar</a>","synthetic":true,"types":["ksched::condvar::Condvar"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"ksched/slpque/struct.SleepQueue.html\" title=\"struct ksched::slpque::SleepQueue\">SleepQueue</a>","synthetic":true,"types":["ksched::slpque::SleepQueue"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"ksched/task/struct.Executor.html\" title=\"struct ksched::task::Executor\">Executor</a>","synthetic":true,"types":["ksched::task::Executor"]},{"text":"impl&lt;T:&nbsp;<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"ksched/mutex/struct.Mutex.html\" title=\"struct ksched::mutex::Mutex\">Mutex</a>&lt;T&gt;","synthetic":false,"types":["ksched::mutex::Mutex"]},{"text":"impl&lt;T:&nbsp;<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Send.html\" title=\"trait core::marker::Send\">Send</a> for <a class=\"struct\" href=\"ksched/mutex/struct.MutexGuard.html\" title=\"struct ksched::mutex::MutexGuard\">MutexGuard</a>&lt;'_, T&gt;","synthetic":false,"types":["ksched::mutex::MutexGuard"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()