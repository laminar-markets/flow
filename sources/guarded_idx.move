module flow::guarded_idx {
    use std::option::{Self, Option};

    const ENO_MESSAGE: u64 = 0;

    // invalid argument provided
    const EINVALID_ARGUMENT: u64 = 1;

    const SENTINEL_VALUE: u64 = 0xffffffffffffffff;

    struct GuardedIdx has store, drop, copy {
        value: u64
    }

    public fun guard(value: u64): GuardedIdx {
        assert!(value != SENTINEL_VALUE, EINVALID_ARGUMENT);
        GuardedIdx {
            value
        }
    }

    public fun unguard(guard: GuardedIdx): u64 {
        assert!(!is_sentinel(guard), EINVALID_ARGUMENT);
        guard.value
    }

    public fun try_guard(value: Option<u64>): GuardedIdx {
        guard(option::destroy_with_default(value, SENTINEL_VALUE))
    }

    public fun try_unguard(guard: GuardedIdx): Option<u64> {
        if (guard.value == SENTINEL_VALUE) {
            option::none()
        } else {
            option::some(guard.value)
        }
    }

    public fun sentinel(): GuardedIdx {
        GuardedIdx {
            value: SENTINEL_VALUE
        }
    }

    public fun is_sentinel(guard: GuardedIdx): bool {
        guard.value == SENTINEL_VALUE
    }
}