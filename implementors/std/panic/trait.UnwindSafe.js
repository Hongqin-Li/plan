(function() {var implementors = {};
implementors["ksched"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/panic/trait.UnwindSafe.html\" title=\"trait std::panic::UnwindSafe\">UnwindSafe</a> for <a class=\"struct\" href=\"ksched/condvar/struct.Condvar.html\" title=\"struct ksched::condvar::Condvar\">Condvar</a>","synthetic":true,"types":["ksched::condvar::Condvar"]},{"text":"impl&lt;T:&nbsp;?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/panic/trait.UnwindSafe.html\" title=\"trait std::panic::UnwindSafe\">UnwindSafe</a> for <a class=\"struct\" href=\"ksched/mutex/struct.Mutex.html\" title=\"struct ksched::mutex::Mutex\">Mutex</a>&lt;T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/panic/trait.UnwindSafe.html\" title=\"trait std::panic::UnwindSafe\">UnwindSafe</a>,&nbsp;</span>","synthetic":true,"types":["ksched::mutex::Mutex"]},{"text":"impl&lt;'a, T&gt; !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/panic/trait.UnwindSafe.html\" title=\"trait std::panic::UnwindSafe\">UnwindSafe</a> for <a class=\"struct\" href=\"ksched/mutex/struct.MutexGuard.html\" title=\"struct ksched::mutex::MutexGuard\">MutexGuard</a>&lt;'a, T&gt;","synthetic":true,"types":["ksched::mutex::MutexGuard"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/panic/trait.UnwindSafe.html\" title=\"trait std::panic::UnwindSafe\">UnwindSafe</a> for <a class=\"struct\" href=\"ksched/slpque/struct.SleepQueue.html\" title=\"struct ksched::slpque::SleepQueue\">SleepQueue</a>","synthetic":true,"types":["ksched::slpque::SleepQueue"]},{"text":"impl !<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/panic/trait.UnwindSafe.html\" title=\"trait std::panic::UnwindSafe\">UnwindSafe</a> for <a class=\"struct\" href=\"ksched/task/struct.Executor.html\" title=\"struct ksched::task::Executor\">Executor</a>","synthetic":true,"types":["ksched::task::Executor"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()