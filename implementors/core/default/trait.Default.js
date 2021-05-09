(function() {var implementors = {};
implementors["kalloc"] = [{"text":"impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"kalloc/list/struct.List.html\" title=\"struct kalloc::list::List\">List</a>&lt;T&gt;","synthetic":false,"types":["kalloc::list::List"]},{"text":"impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"kalloc/vecque/struct.Vecque.html\" title=\"struct kalloc::vecque::Vecque\">Vecque</a>&lt;T&gt;","synthetic":false,"types":["kalloc::vecque::Vecque"]}];
implementors["kcore"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"kcore/chan/struct.QType.html\" title=\"struct kcore::chan::QType\">QType</a>","synthetic":false,"types":["kcore::chan::QType"]}];
implementors["ksched"] = [{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"ksched/task/struct.Executor.html\" title=\"struct ksched::task::Executor\">Executor</a>","synthetic":false,"types":["ksched::task::Executor"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"ksched/task/struct.TaskAdapter.html\" title=\"struct ksched::task::TaskAdapter\">TaskAdapter</a>","synthetic":false,"types":["ksched::task::TaskAdapter"]},{"text":"impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"ksched/sync/struct.Condvar.html\" title=\"struct ksched::sync::Condvar\">Condvar</a>","synthetic":false,"types":["ksched::condvar::Condvar"]},{"text":"impl&lt;T:&nbsp;<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"ksched/sync/struct.Mutex.html\" title=\"struct ksched::sync::Mutex\">Mutex</a>&lt;T&gt;","synthetic":false,"types":["ksched::mutex::Mutex"]},{"text":"impl&lt;T:&nbsp;<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> + ?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"ksched/sync/struct.RwLock.html\" title=\"struct ksched::sync::RwLock\">RwLock</a>&lt;T&gt;","synthetic":false,"types":["ksched::rwlock::RwLock"]},{"text":"impl&lt;T:&nbsp;?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a> + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"ksched/sync/struct.Spinlock.html\" title=\"struct ksched::sync::Spinlock\">Spinlock</a>&lt;T&gt;","synthetic":false,"types":["ksched::spinlock::Spinlock"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()