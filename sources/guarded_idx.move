module flow::guarded_idx {
    use std::option::{Self, Option};

    friend flow::splay_tree;
    friend flow::queue;

    const ENO_MESSAGE: u64 = 0;

    // invalid argument provided
    const EINVALID_ARGUMENT: u64 = 1;

    const SENTINEL_VALUE: u64 = 0xffffffffffffffff;

    struct GuardedIdx has store, drop, copy {
        value: u64
    }

    public(friend) fun guard(value: u64): GuardedIdx {
        assert!(value != SENTINEL_VALUE, EINVALID_ARGUMENT);
        GuardedIdx {
            value
        }
    }

    public(friend) fun unguard(guard: GuardedIdx): u64 {
        assert!(!is_sentinel(guard), EINVALID_ARGUMENT);
        guard.value
    }

    public(friend) fun try_guard(value: Option<u64>): GuardedIdx {
        let v = option::destroy_with_default(value, SENTINEL_VALUE);
        if (v != SENTINEL_VALUE) {
            guard(v)
        } else {
            sentinel()
        }
    }

    public(friend) fun try_unguard(guard: GuardedIdx): Option<u64> {
        if (guard.value == SENTINEL_VALUE) {
            option::none()
        } else {
            option::some(guard.value)
        }
    }

    public(friend) fun sentinel(): GuardedIdx {
        GuardedIdx {
            value: SENTINEL_VALUE
        }
    }

    public(friend) fun is_sentinel(guard: GuardedIdx): bool {
        guard.value == SENTINEL_VALUE
    }

    #[test]
    fun test_guard_value() {
        let value = 1;
        guard(value);
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_guard_max_u64_fails() {
        let value = SENTINEL_VALUE;
        guard(value);
    }

    #[test]
    fun test_unguard_value() {
        let value = 1;
        unguard(guard(value));
    }

    #[test]
    #[expected_failure(abort_code = 1)]
    fun test_unguard_sentinel_fails() {
        unguard(sentinel());
    }

    #[test]
    fun test_is_sentinel() {
        assert!(is_sentinel(sentinel()), ENO_MESSAGE);
    }

    #[test]
    fun test_is_not_sentinel() {
        let value = 1;
        assert!(!is_sentinel(guard(value)), ENO_MESSAGE);
    }

    #[test]
    fun test_try_guard_some() {
        let guarded = try_guard(option::some(1));
        assert!(unguard(guarded) == 1, ENO_MESSAGE);
    }

    #[test]
    fun test_try_guard_none() {
        let guarded = try_guard(option::none<u64>());
        assert!(is_sentinel(guarded), ENO_MESSAGE);
    }

    #[test]
    fun test_try_unguard_some() {
        let value = 1;
        let option = try_unguard(guard(value));
        assert!(option::is_some(&option), ENO_MESSAGE);
    }

    #[test]
    fun test_try_unguard_none() {
        let option = try_unguard(sentinel());
        assert!(option::is_none(&option), ENO_MESSAGE);
    }
}
