module flow::vector_utils {
    use std::vector;

    friend flow::splay_tree;

    // vector is empty
    const EVECTOR_EMPTY: u64 = 1;

    public(friend) fun top<T: copy>(v: &vector<T>): T {
        let len = vector::length(v);
        if (len <= 0) {
            abort EVECTOR_EMPTY
        };
        *vector::borrow(v, len - 1)
    }
}