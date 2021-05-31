(function() {var implementors = {};
implementors["kdevice"] = [{"text":"impl&lt;T&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/deref/trait.DerefMut.html\" title=\"trait core::ops::deref::DerefMut\">DerefMut</a> for <a class=\"struct\" href=\"kdevice/cache/struct.CGuard.html\" title=\"struct kdevice::cache::CGuard\">CGuard</a>&lt;'_, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: <a class=\"trait\" href=\"kdevice/cache/trait.Cache.html\" title=\"trait kdevice::cache::Cache\">Cache</a>,&nbsp;</span>","synthetic":false,"types":["kdevice::cache::CGuard"]}];
implementors["ksched"] = [{"text":"impl&lt;T:&nbsp;?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/deref/trait.DerefMut.html\" title=\"trait core::ops::deref::DerefMut\">DerefMut</a> for <a class=\"struct\" href=\"ksched/sync/struct.MutexGuard.html\" title=\"struct ksched::sync::MutexGuard\">MutexGuard</a>&lt;'_, T&gt;","synthetic":false,"types":["ksched::mutex::MutexGuard"]},{"text":"impl&lt;T:&nbsp;?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/deref/trait.DerefMut.html\" title=\"trait core::ops::deref::DerefMut\">DerefMut</a> for <a class=\"struct\" href=\"ksched/sync/struct.RwLockWriteGuard.html\" title=\"struct ksched::sync::RwLockWriteGuard\">RwLockWriteGuard</a>&lt;'_, T&gt;","synthetic":false,"types":["ksched::rwlock::RwLockWriteGuard"]},{"text":"impl&lt;'a, T:&nbsp;?<a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/marker/trait.Sized.html\" title=\"trait core::marker::Sized\">Sized</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/ops/deref/trait.DerefMut.html\" title=\"trait core::ops::deref::DerefMut\">DerefMut</a> for <a class=\"struct\" href=\"ksched/sync/struct.SpinlockGuard.html\" title=\"struct ksched::sync::SpinlockGuard\">SpinlockGuard</a>&lt;'a, T&gt;","synthetic":false,"types":["ksched::spinlock::SpinlockGuard"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()