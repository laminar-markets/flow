module flow::splay_tree {
    use std::vector;
    use std::option::{Self, Option};

    const ENO_MESSAGE: u64 = 0;
    const EKEY_NOT_FOUND: u64 = 1;
    const EPARENT_CHILD_MISMATCH: u64 = 2;
    const EITER_DONE: u64 = 3;

    const SENTINEL_VALUE: u64 = 0xffffffffffffffff;

    struct GuardedIdx has store, drop, copy {
        value: u64
    }

    fun guard(value: u64): GuardedIdx {
        GuardedIdx {
            value
        }
    }

    fun unguard(guard: GuardedIdx): u64 {
        assert!(!is_sentinel(guard), EKEY_NOT_FOUND);
        guard.value
    }

    fun try_guard(value: Option<u64>): GuardedIdx {
        guard(option::destroy_with_default(value, SENTINEL_VALUE))
    }

    fun try_unguard(guard: GuardedIdx): Option<u64> {
        if (guard.value == SENTINEL_VALUE) {
            option::none()
        } else {
            option::some(guard.value)
        }
    }

    fun sentinel(): GuardedIdx {
        GuardedIdx {
            value: SENTINEL_VALUE
        }
    }

    fun is_sentinel(guard: GuardedIdx): bool {
        guard.value == SENTINEL_VALUE
    }


    struct Node<V: store + drop> has store, drop {
        key: u64,
        value: V,
        left: GuardedIdx,
        right: GuardedIdx,
    }

    struct SplayTree<V: store + drop> has store, drop {
        root: GuardedIdx,
        nodes: vector<Node<V>>,
        single_splay: bool,
        removed_nodes: vector<u64>,
        min: GuardedIdx,
        max: GuardedIdx,
    }

    struct Iterator has drop {
        stack: vector<u64>,
        reverse: bool,
        is_done: bool,
    }

    public fun init_tree<V: store + drop>(single_splay: bool): SplayTree<V> {
        SplayTree {
            root: sentinel(),
            nodes: vector::empty<Node<V>>(),
            single_splay,
            removed_nodes: vector::empty<u64>(),
            min: sentinel(),
            max: sentinel(),
        }
    }

    fun init_node<V: store + drop>(key: u64, value: V): Node<V> {
        Node {
            key,
            value,
            left: sentinel(),
            right: sentinel(),
        }
    }

    public fun init_iterator(reverse: bool): Iterator {
        Iterator {
            stack: vector::empty(),
            reverse,
            is_done: false,
        }
    }

    public fun iterator_is_done(iter: &Iterator): bool {
        iter.is_done
    }

    fun get_left<V: store + drop>(tree: &SplayTree<V>, idx: u64): GuardedIdx {
        vector::borrow(&tree.nodes, idx).left
    }

    fun get_right<V: store + drop>(tree: &SplayTree<V>, idx: u64): GuardedIdx {
        vector::borrow(&tree.nodes, idx).right
    }

    fun set_left<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, update_to: GuardedIdx) {
        vector::borrow_mut(&mut tree.nodes, idx).left = update_to;
    }

    fun set_right<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, update_to: GuardedIdx) {
        vector::borrow_mut(&mut tree.nodes, idx).right = update_to;
    }

    fun get_root<V: store + drop>(tree: &SplayTree<V>): GuardedIdx {
        tree.root
    }

    fun set_root<V: store + drop>(tree: &mut SplayTree<V>, update_to: GuardedIdx) {
        tree.root = update_to;
    }

    fun get_node_by_index<V: store + drop>(tree: &SplayTree<V>, idx: u64): &Node<V> {
        vector::borrow(&tree.nodes, idx)
    }

    fun get_mut_node_by_index<V: store + drop>(tree: &mut SplayTree<V>, idx: u64): &mut Node<V> {
        vector::borrow_mut(&mut tree.nodes, idx)
    }

    fun remove_node_by_index<V: store + drop>(tree: &mut SplayTree<V>, idx: u64) {
        // do not actually remove node from the nodes vector in tree, as that would require shifting every index
        // stored within a node struct in the tree.
        vector::push_back(&mut tree.removed_nodes, idx);
    }

    public fun size<V: store + drop>(tree: &SplayTree<V>): u64 {
        vector::length(&tree.nodes) - vector::length(&tree.removed_nodes)
    }

    fun get_idx_subtree<V: store + drop>(tree: &SplayTree<V>, idx: u64, key: u64): u64 {
        let node = get_node_by_index(tree, idx);

        if (key == node.key) {
            idx
        } else if (key < node.key && !is_sentinel(node.left)) {
            let left = unguard(node.left);
            get_idx_subtree(tree, left, key)
        } else if (key > node.key && !is_sentinel(node.right)) {
            let right = unguard(node.right);
            get_idx_subtree(tree, right, key)
        } else {
            abort EKEY_NOT_FOUND
        }
    }

    public fun get<V: store + drop>(tree: &SplayTree<V>, key: u64): &V {
        let root = get_root(tree);
        assert!(!is_sentinel(root), ENO_MESSAGE);

        let idx = get_idx_subtree(tree, unguard(root), key);
        let node = get_node_by_index(tree, idx);
        &node.value
    }

    public fun get_mut<V: store + drop>(tree: &mut SplayTree<V>, key: u64): &mut V {
        let root = get_root(tree);
        assert!(!is_sentinel(root), ENO_MESSAGE);

        let idx = get_idx_subtree(tree, unguard(root), key);
        let node = get_mut_node_by_index(tree, idx);
        &mut node.value
    }

    fun contains_node_subtree<V: store + drop>(tree: &SplayTree<V>, idx: u64, key: u64): bool {
        let node = get_node_by_index(tree, idx);

        if (key == node.key) {
            true
        } else if (key < node.key && !is_sentinel(node.left)) {
            let left = unguard(node.left);
            contains_node_subtree(tree, left, key)
        } else if (key > node.key && !is_sentinel(node.right)) {
            let right = unguard(node.right);
            contains_node_subtree(tree, right, key)
        } else {
            false
        }
    }

    public fun contains<V: store + drop>(tree: &SplayTree<V>, key: u64): bool {
        let root = get_root(tree);
        if (is_sentinel(root)) {
            false
        } else {
            contains_node_subtree(tree, unguard(root), key)
        }
    }

    fun move_parent_pointer<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, parent_idx: Option<u64>, move_to: GuardedIdx) {
        if (option::is_some(&parent_idx)) {
            let parent_idx = *option::borrow(&parent_idx);
            let parent_node = get_mut_node_by_index(tree, parent_idx);

            assert!(is_sentinel(move_to) || parent_idx != unguard(move_to), ENO_MESSAGE);

            if (!is_sentinel(parent_node.left) && unguard(parent_node.left) == idx) {
                parent_node.left = move_to;
            } else if (!is_sentinel(parent_node.right) && unguard(parent_node.right) == idx) {
                parent_node.right = move_to;
            } else {
                abort EPARENT_CHILD_MISMATCH
            }
        } else {
            set_root(tree, move_to);
        };
    }

    fun remove_node<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, parent_idx: Option<u64>) {
        let (maybe_left, maybe_right) = {
            let node = get_node_by_index(tree, idx);
            (node.left, node.right)
        };

        if (!is_sentinel(maybe_left) && !is_sentinel(maybe_right)) {
            let right = unguard(maybe_right);
            let maybe_right_leftmost = get_left(tree, right);
            if (!is_sentinel(maybe_right_leftmost)) {
                let right_leftmost = unguard(maybe_right_leftmost);
                let right_leftmost_parent = right;
                while (!is_sentinel(get_left(tree, right_leftmost))) {
                    right_leftmost_parent = right_leftmost;
                    right_leftmost = unguard(get_left(tree, right_leftmost));
                };

                move_parent_pointer(tree, idx, parent_idx, guard(right_leftmost));

                let right_leftmost_node = get_mut_node_by_index(tree, right_leftmost);
                right_leftmost_node.left = maybe_left;
                right_leftmost_node.right = maybe_right;

                let right_leftmost_parent_node = get_mut_node_by_index(tree, right_leftmost_parent);
                right_leftmost_parent_node.left = sentinel();
            } else {
                move_parent_pointer(tree, idx, parent_idx, guard(right));

                let right_node = get_mut_node_by_index(tree, right);
                right_node.left = maybe_left;
            };
        } else if (!is_sentinel(maybe_left) && is_sentinel(maybe_right)) {
            move_parent_pointer(tree, idx, parent_idx, maybe_left);
        } else if (is_sentinel(maybe_left) && !is_sentinel(maybe_right)) {
            move_parent_pointer(tree, idx, parent_idx, maybe_right);
        } else {
            move_parent_pointer(tree, idx, parent_idx, sentinel());
        };
        remove_node_by_index(tree, idx);
    }

    fun remove_from_subtree<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, parent_idx: Option<u64>, key: u64) {
        let node = get_node_by_index(tree, idx);
        if (key == node.key) {
            remove_node(tree, idx, parent_idx);
        } else if (key < node.key && !is_sentinel(node.left)) {
            remove_from_subtree(tree, unguard(node.left), option::some(idx), key);
        } else if (key > node.key && !is_sentinel(node.right)) {
            remove_from_subtree(tree, unguard(node.right), option::some(idx), key);
        } else {
            abort EKEY_NOT_FOUND
        }
    }

    public fun remove<V: store + drop>(tree: &mut SplayTree<V>, key: u64) {
        let maybe_root = get_root(tree);
        assert!(!is_sentinel(maybe_root), ENO_MESSAGE);

        let root = unguard(maybe_root);
        remove_from_subtree(tree, root, option::none<u64>(), key);
    }

    fun pop<T: copy + drop>(v: &mut vector<T>): T {
        assert!(!vector::is_empty(v), ENO_MESSAGE);
        let first = *vector::borrow(v, 0);
        vector::remove(v, 0);
        first
    }

    fun insert_child<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, gp_idx: Option<u64>, idx: u64, key: u64, value: V) {
        let parent_node = get_node_by_index(tree, parent_idx);

        if (key < parent_node.key) {
            if (is_sentinel(parent_node.left)) {
                if (idx >= vector::length(&tree.nodes)) {
                    let node = init_node(key, value);
                    vector::push_back(&mut tree.nodes, node);
                } else {
                    let prev_node = vector::borrow_mut(&mut tree.nodes, idx);
                    prev_node.key = key;
                    prev_node.value = value;
                    prev_node.left = sentinel();
                    prev_node.right = sentinel();
                };
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.left = guard(idx);
                rotate_right(tree, parent_idx, gp_idx, idx);
            } else {
                insert_child(tree, unguard(parent_node.left), option::some(parent_idx), idx, key, value);
            }
        } else if (key > parent_node.key) {
            if (is_sentinel(parent_node.right)) {
                if (idx >= vector::length(&tree.nodes)) {
                    let node = init_node(key, value);
                    vector::push_back(&mut tree.nodes, node);
                } else {
                    let prev_node = vector::borrow_mut(&mut tree.nodes, idx);
                    prev_node.key = key;
                    prev_node.value = value;
                    prev_node.left = sentinel();
                    prev_node.right = sentinel();
                };
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.right = guard(idx);
                rotate_left(tree, parent_idx, gp_idx, idx);
            } else {
                insert_child(tree, unguard(parent_node.right), option::some(parent_idx), idx, key, value);
            }
        }
    }

    public fun insert<V: store + drop>(tree: &mut SplayTree<V>, key: u64, value: V) {
        let maybe_root = get_root(tree);
        if (is_sentinel(maybe_root)) {
            assert!(vector::length(&tree.nodes) - vector::length(&tree.removed_nodes) == 0, ENO_MESSAGE);
            let node = init_node(key, value);
            vector::push_back(&mut tree.nodes, node);
            set_root(tree, guard(0));
            update_min(tree, key, 0);
            update_max(tree, key, 0);
        } else {
            assert!(!is_sentinel(maybe_root), ENO_MESSAGE);
            assert!(!is_sentinel(tree.min), ENO_MESSAGE);
            assert!(!is_sentinel(tree.max), ENO_MESSAGE);

            let root = unguard(maybe_root);

            let idx;
            if (vector::is_empty(&tree.removed_nodes)) {
                idx = vector::length(&tree.nodes);
            } else {
                idx = pop<u64>(&mut tree.removed_nodes);
            };

            update_min(tree, key, idx);
            update_max(tree, key, idx);

            insert_child(tree, root, option::none<u64>(), idx, key, value);
        }
    }

    fun update_min<V: store + drop>(tree: &mut SplayTree<V>, key: u64, idx: u64) {
        if (is_sentinel(tree.min)) {
            tree.min = guard(idx);
        } else {
            let min = unguard(tree.min);
            let min_node = get_node_by_index(tree, min);

            if (key < min_node.key) {
                tree.min = guard(idx);
            };
        }
    }

    fun update_max<V: store + drop>(tree: &mut SplayTree<V>, key: u64, idx: u64) {
        if (is_sentinel(tree.max)) {
            tree.max = guard(idx);
        } else {
            let max = unguard(tree.max);
            let max_node = get_node_by_index(tree, max);

            if (key > max_node.key) {
                tree.max = guard(idx);
            };
        }
    }

    fun rotate_left<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, gp_idx: Option<u64>, child_idx: u64) {
        let child_left = get_left(tree, child_idx);
        set_right(tree, parent_idx, child_left);
        set_left(tree, child_idx, guard(parent_idx));

        if (option::is_some(&gp_idx)) {
            let gp_idx = *option::borrow(&gp_idx);
            let gp_left = get_left(tree, gp_idx);
            let gp_right = get_right(tree, gp_idx);

            if (!is_sentinel(gp_left) && unguard(gp_left) == parent_idx) {
                set_left(tree, gp_idx, guard(child_idx));
            } else if (!is_sentinel(gp_right) && unguard(gp_right) == parent_idx) {
                set_right(tree, gp_idx, guard(child_idx));
            } else {
                abort EPARENT_CHILD_MISMATCH
            }
        } else {
            assert!(!is_sentinel(tree.root), ENO_MESSAGE);
            let root = unguard(tree.root);
            assert!(root == parent_idx, ENO_MESSAGE);
            set_root(tree, guard(child_idx));
        }
    }

    fun rotate_right<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, gp_idx: Option<u64>, child_idx: u64) {
        let child_right = get_right(tree, child_idx);
        set_left(tree, parent_idx, child_right);
        set_right(tree, child_idx, guard(parent_idx));

        if (option::is_some(&gp_idx)) {
            let gp_idx = *option::borrow(&gp_idx);
            let gp_left = get_left(tree, gp_idx);
            let gp_right = get_right(tree, gp_idx);

            if (!is_sentinel(gp_left) && unguard(gp_left) == parent_idx) {
                set_left(tree, gp_idx, guard(child_idx));
            } else if (!is_sentinel(gp_right) && unguard(gp_right) == parent_idx) {
                set_right(tree, gp_idx, guard(child_idx));
            } else {
                abort EPARENT_CHILD_MISMATCH
            }
        } else {
            assert!(!is_sentinel(tree.root), ENO_MESSAGE);
            let root = unguard(tree.root);
            assert!(root == parent_idx, ENO_MESSAGE);
            set_root(tree, guard(child_idx));
        }
    }

    public fun min<V: store + drop>(tree: &SplayTree<V>): &V {
        assert!(!is_sentinel(tree.min), ENO_MESSAGE);
        let min_idx = unguard(tree.min);
        &get_node_by_index(tree, min_idx).value
    }

    public fun max<V: store + drop>(tree: &SplayTree<V>): &V {
        assert!(!is_sentinel(tree.max), ENO_MESSAGE);
        let max_idx = unguard(tree.max);
        &get_node_by_index(tree, max_idx).value
    }

    fun splay_child<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, parent_idx: u64, gp_idx: Option<u64>, is_left_child: bool, key: u64) {
        let node = get_node_by_index(tree, idx);

        if (key == node.key) {
            if (is_left_child) {
                rotate_right(tree, parent_idx, gp_idx, idx);
            } else {
                rotate_left(tree, parent_idx, gp_idx, idx);
            }
        } else if (key < node.key && !is_sentinel(node.left)) {
            splay_child(tree, unguard(node.left), idx, option::some(parent_idx), true, key);
        } else if (key > node.key && !is_sentinel(node.right)) {
            splay_child(tree, unguard(node.right), idx, option::some(parent_idx), false, key);
        } else {
            abort EKEY_NOT_FOUND
        }
    }

    public fun splay<V: store + drop>(tree: &mut SplayTree<V>, key: u64) {
        let maybe_root = get_root(tree);
        assert!(!is_sentinel(maybe_root), ENO_MESSAGE);

        let root = unguard(maybe_root);
        assert!(root != key, ENO_MESSAGE);

        let root_node = get_node_by_index(tree, root);

        if (key < root_node.key && !is_sentinel(root_node.left)) {
            let root_left = unguard(root_node.left);
            splay_child(tree, root_left, root, option::none<u64>(), true, key);
        } else if (key > root_node.key && !is_sentinel(root_node.right)) {
            let root_right = unguard(root_node.right);
            splay_child(tree, root_right, root, option::none<u64>(), false, key);
        } else {
            abort EKEY_NOT_FOUND
        }
    }

    fun top<T: copy>(v: &vector<T>): T {
        *vector::borrow(v, vector::length(v) - 1)
    }

    fun traverse_left<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator, parent_idx: u64) {
        let maybe_left = guard(parent_idx);
        while (!is_sentinel(maybe_left)) {
            let current = unguard(maybe_left);
            maybe_left = get_left(tree, current);
            vector::push_back(&mut iter.stack, current);
        };
    }

    fun traverse_right<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator, parent_idx: u64) {
        let maybe_right = guard(parent_idx);
        while (!is_sentinel(maybe_right)) {
            let current = unguard(maybe_right);
            maybe_right = get_right(tree, current);
            vector::push_back(&mut iter.stack, current);
        };
    }

    fun next_check_return<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator, idx: u64): &V {
        assert!(!is_sentinel(tree.max), ENO_MESSAGE);

        let max = unguard(tree.max);
        let max_node = get_node_by_index(tree, max);
        let node = get_node_by_index(tree, idx);

        if (node.key == max_node.key) {
            iter.is_done = true;
        };
        &node.value
    }

    public fun next<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator): &V {
        let maybe_root = get_root(tree);

        assert!(!iter.is_done, EITER_DONE);
        assert!(!iter.reverse, ENO_MESSAGE);
        assert!(!is_sentinel(maybe_root), ENO_MESSAGE);

        let root = unguard(maybe_root);
        if (vector::is_empty(&iter.stack)) {
            let current = root;
            traverse_left(tree, iter, current);

            let idx = top(&iter.stack);
            return next_check_return(tree, iter, idx)
        };
        let current = top(&iter.stack);
        let maybe_right = get_right(tree, current);
        if (!is_sentinel(maybe_right)) {
            current = unguard(maybe_right);
            traverse_left(tree, iter, current);

            let idx = top(&iter.stack);
            return next_check_return(tree, iter, idx)
        } else {
            let current = vector::pop_back(&mut iter.stack);
            let parent = top(&iter.stack);

            while (current != root) {
                let maybe_parent_left = get_left(tree, parent);
                let maybe_parent_right = get_right(tree, parent);

                if (!is_sentinel(maybe_parent_left) && unguard(maybe_parent_left) == current) {
                    return next_check_return(tree, iter, parent)
                } else if (!is_sentinel(maybe_parent_right) && unguard(maybe_parent_right) == current) {
                    current = vector::pop_back(&mut iter.stack);
                    parent = top(&iter.stack);
                } else {
                    abort EPARENT_CHILD_MISMATCH
                };
            };
            abort EITER_DONE
        }
    }

    fun prev_check_return<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator, idx: u64): &V {
        assert!(!is_sentinel(tree.min), ENO_MESSAGE);

        let min = unguard(tree.min);
        let min_node = get_node_by_index(tree, min);
        let node = get_node_by_index(tree, idx);

        if (node.key == min_node.key) {
            iter.is_done = true;
        };
        &node.value
    }

    public fun prev<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator): &V {
        let root = get_root(tree);

        assert!(!iter.is_done, EITER_DONE);
        assert!(iter.reverse, ENO_MESSAGE);
        assert!(!is_sentinel(root), ENO_MESSAGE);

        if (vector::is_empty(&iter.stack)) {
            let current = unguard(root);
            traverse_right(tree, iter, current);
            let idx = top(&iter.stack);
            return prev_check_return(tree, iter, idx)
        };
        let current = top(&iter.stack);
        let maybe_left = get_left(tree, current);
        if (!is_sentinel(maybe_left)) {
            current = unguard(maybe_left);
            traverse_right(tree, iter, current);
            let idx = top(&iter.stack);
            return prev_check_return(tree, iter, idx)
        } else {
            let current = vector::pop_back(&mut iter.stack);
            let parent = top(&iter.stack);

            while (current != unguard(root)) {
                let maybe_parent_left = get_left(tree, parent);
                let maybe_parent_right = get_right(tree, parent);

                if (!is_sentinel(maybe_parent_right) && unguard(maybe_parent_right) == current) {
                    return prev_check_return(tree, iter, parent)
                } else if (!is_sentinel(maybe_parent_left) && unguard(maybe_parent_right) == current) {
                    current = vector::pop_back(&mut iter.stack);
                    parent = top(&iter.stack);
                } else {
                    abort EPARENT_CHILD_MISMATCH
                };
            };
            abort EITER_DONE
        }
    }

    public fun has_next(iter: &Iterator): bool {
        !iter.is_done
    }

    #[test]
    fun test_init_tree() {
        let tree = init_tree<u64>(true);

        assert!(is_sentinel(tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_init_node() {
        let node = init_node<u64>(0, 0);

        assert!(node.key == 0, ENO_MESSAGE);
        assert!(node.value == 0, ENO_MESSAGE);
        assert!(is_sentinel(node.left), ENO_MESSAGE);
        assert!(is_sentinel(node.right), ENO_MESSAGE);
    }

    #[test]
    fun test_add_node() {
        let tree = init_tree<u64>(true);

        assert!(is_sentinel(tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 0, ENO_MESSAGE);

        insert(&mut tree, 0, 0);

        assert!(!is_sentinel(tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 1, ENO_MESSAGE);
    }

     #[test]
     fun test_add_two_nodes() {
         let tree = init_tree<u64>(true);

         let key0: u64 = 0;
         let key1: u64 = 1;

         insert(&mut tree, key0, 0);
         insert(&mut tree, key1, 1);

         let maybe_root = get_root(&tree);
         assert!(!is_sentinel(maybe_root), ENO_MESSAGE);

         let root = unguard(maybe_root);
         let root_node = vector::borrow(&tree.nodes, root);

         assert!(vector::length(&tree.nodes) == 2, ENO_MESSAGE);
         assert!(root_node.key == key1, ENO_MESSAGE);
         assert!(unguard(get_left(&tree, root)) == key0, ENO_MESSAGE);
         assert!(is_sentinel(get_right(&tree, root)), ENO_MESSAGE);
     }

    #[test]
    fun test_add_three_nodes() {
        let tree = init_tree<u64>(true);

        let key0: u64 = 0;
        let key1: u64 = 1;
        let key2: u64 = 2;

        insert(&mut tree, key0, 0);
        insert(&mut tree, key1, 1);
        insert(&mut tree, key2, 2);

        let maybe_root = get_root(&tree);
        assert!(!is_sentinel(maybe_root), ENO_MESSAGE);

        let root = unguard(maybe_root);
        let root_node = vector::borrow(&tree.nodes, root);

        assert!(size(&tree) == 3, ENO_MESSAGE);
        assert!(root_node.key == key2, ENO_MESSAGE);
        assert!(unguard(get_left(&tree, root)) == key1, ENO_MESSAGE);
        assert!(is_sentinel(get_right(&tree, root)), ENO_MESSAGE);

        let maybe_root_left = get_left(&tree, root);
        assert!(!is_sentinel(maybe_root_left), ENO_MESSAGE);
        let root_left = unguard(maybe_root_left);

        assert!(get_node_by_index(&tree, root_left).key == key1, ENO_MESSAGE);
        assert!(get_node_by_index(&tree, unguard(get_node_by_index(&tree, root_left).left)).key == key0, ENO_MESSAGE);

        assert!(*get(&tree, key0) == 0, ENO_MESSAGE);
        assert!(*get(&tree, key1) == 1, ENO_MESSAGE);
        assert!(*get(&tree, key2) == 2, ENO_MESSAGE);
    }

    #[test]
    fun test_min() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 1, 1);

        let min = min(&tree);
        assert!(*min == 1, ENO_MESSAGE);
    }

    #[test]
    fun test_max() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 1, 1);

        let max = max(&tree);
        assert!(*max == 5, ENO_MESSAGE);
    }

    #[test]
    fun test_contains() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 1, 1);

        assert!(contains(&tree, 1), ENO_MESSAGE);
        assert!(contains(&tree, 2), ENO_MESSAGE);
        assert!(contains(&tree, 3), ENO_MESSAGE);
        assert!(contains(&tree, 4), ENO_MESSAGE);
        assert!(contains(&tree, 5), ENO_MESSAGE);
        assert!(!contains(&tree, 6), ENO_MESSAGE);
    }

    #[test]
    fun test_add_remove_node() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        assert!(contains(&tree, 0), ENO_MESSAGE);
        assert!(size(&tree) == 1, ENO_MESSAGE);

        remove(&mut tree, 0);
        assert!(!contains(&tree, 0), ENO_MESSAGE);
        assert!(size(&tree) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_add_remove_two_nodes() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        assert!(contains(&tree, 0), ENO_MESSAGE);
        assert!(contains(&tree, 1), ENO_MESSAGE);
        assert!(size(&tree) == 2, ENO_MESSAGE);

        remove(&mut tree, 0);
        remove(&mut tree, 1);
        assert!(!contains(&tree, 0), ENO_MESSAGE);
        assert!(!contains(&tree, 1), ENO_MESSAGE);
        assert!(size(&tree) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_add_remove_nodes1() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        assert!(contains(&tree, 0), ENO_MESSAGE);
        assert!(contains(&tree, 1), ENO_MESSAGE);
        assert!(contains(&tree, 2), ENO_MESSAGE);
        assert!(contains(&tree, 3), ENO_MESSAGE);
        assert!(contains(&tree, 4), ENO_MESSAGE);
        assert!(contains(&tree, 5), ENO_MESSAGE);
        assert!(size(&tree) == 6, ENO_MESSAGE);

        remove(&mut tree, 0);
        remove(&mut tree, 1);
        remove(&mut tree, 2);
        remove(&mut tree, 3);
        remove(&mut tree, 4);
        remove(&mut tree, 5);

        assert!(!contains(&tree, 0), ENO_MESSAGE);
        assert!(!contains(&tree, 1), ENO_MESSAGE);
        assert!(!contains(&tree, 2), ENO_MESSAGE);
        assert!(!contains(&tree, 3), ENO_MESSAGE);
        assert!(!contains(&tree, 4), ENO_MESSAGE);
        assert!(!contains(&tree, 5), ENO_MESSAGE);
        assert!(size(&tree) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_add_remove_nodes2() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 3, 3);

        assert!(contains(&tree, 0), ENO_MESSAGE);
        assert!(contains(&tree, 1), ENO_MESSAGE);
        assert!(contains(&tree, 2), ENO_MESSAGE);
        assert!(contains(&tree, 3), ENO_MESSAGE);
        assert!(contains(&tree, 4), ENO_MESSAGE);
        assert!(contains(&tree, 5), ENO_MESSAGE);
        assert!(size(&tree) == 6, ENO_MESSAGE);

        remove(&mut tree, 0);
        remove(&mut tree, 1);
        remove(&mut tree, 2);
        remove(&mut tree, 3);
        remove(&mut tree, 4);
        remove(&mut tree, 5);

        assert!(!contains(&tree, 0), ENO_MESSAGE);
        assert!(!contains(&tree, 1), ENO_MESSAGE);
        assert!(!contains(&tree, 2), ENO_MESSAGE);
        assert!(!contains(&tree, 3), ENO_MESSAGE);
        assert!(!contains(&tree, 4), ENO_MESSAGE);
        assert!(!contains(&tree, 5), ENO_MESSAGE);
        assert!(size(&tree) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_add_remove_nodes3() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 1, 1);

        assert!(contains(&tree, 0), ENO_MESSAGE);
        assert!(contains(&tree, 1), ENO_MESSAGE);
        assert!(contains(&tree, 2), ENO_MESSAGE);
        assert!(contains(&tree, 3), ENO_MESSAGE);
        assert!(contains(&tree, 4), ENO_MESSAGE);
        assert!(contains(&tree, 5), ENO_MESSAGE);
        assert!(size(&tree) == 6, ENO_MESSAGE);

        remove(&mut tree, 0);
        remove(&mut tree, 1);
        remove(&mut tree, 2);
        remove(&mut tree, 3);
        remove(&mut tree, 4);
        remove(&mut tree, 5);

        assert!(!contains(&tree, 0), ENO_MESSAGE);
        assert!(!contains(&tree, 1), ENO_MESSAGE);
        assert!(!contains(&tree, 2), ENO_MESSAGE);
        assert!(!contains(&tree, 3), ENO_MESSAGE);
        assert!(!contains(&tree, 4), ENO_MESSAGE);
        assert!(!contains(&tree, 5), ENO_MESSAGE);
        assert!(size(&tree) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_get_mut() {
        let tree = init_tree<u64>(true);
        insert(&mut tree, 2, 2);
        let mutable_node = get_mut(&mut tree, 2);
        assert!(*mutable_node == 2, ENO_MESSAGE);
        *mutable_node = 3;
        let node = get(&tree, 2);
        assert!(*node == 3, ENO_MESSAGE);
    }

    #[test]
    fun test_splay() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 1, 1);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);

        let root = unguard(get_root(&tree));
        let root_node = get_node_by_index(&tree, root);
        assert!(root_node.key == 5, ENO_MESSAGE);

        splay(&mut tree, 0);
        splay(&mut tree, 1);
        splay(&mut tree, 2);
        splay(&mut tree, 3);
        splay(&mut tree, 4);
    }

    #[test]
    fun test_init_iter() {
        let iter = init_iterator(false);

        assert!(vector::is_empty(&iter.stack), ENO_MESSAGE);
        assert!(!iter.reverse, ENO_MESSAGE);
    }

    #[test]
    fun test_iter_traversal1() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        let iter = init_iterator(false);

        let i = 0;
        while (i < 5) {
            let next = next(&tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i + 1;
        };
        let next = next(&tree, &mut iter);
        assert!(*next == i, ENO_MESSAGE);
        assert!(!has_next(&iter), ENO_MESSAGE);
    }

    #[test]
    fun test_iter_traversal2() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 1, 1);

        let iter = init_iterator(false);

        let i = 0;
        while (i < 5) {
            let next = next(&tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i + 1;
        };
        let next = next(&tree, &mut iter);
        assert!(*next == i, ENO_MESSAGE);
        assert!(!has_next(&iter), ENO_MESSAGE);
    }

    #[test]
    fun test_iter_traversal3() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 3, 3);

        let iter = init_iterator(false);

        let i = 0;
        while (i < 5) {
            let next = next(&tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i + 1;
        };
        let next = next(&tree, &mut iter);
        assert!(*next == i, ENO_MESSAGE);
        assert!(!has_next(&iter), ENO_MESSAGE);
    }

    #[test]
    fun test_iter_reverse_traversal1() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        let iter = init_iterator(true);

        let i = 5;
        while (i > 0) {
            let prev = prev(&tree, &mut iter);
            assert!(*prev == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i - 1;
        };
        let prev = prev(&tree, &mut iter);
        assert!(*prev == i, ENO_MESSAGE);
        assert!(!has_next(&iter), ENO_MESSAGE);
    }

    #[test]
    fun test_iter_reverse_traversal2() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 1, 1);

        let iter = init_iterator(true);

        let i = 5;
        while (i > 0) {
            let prev = prev(&tree, &mut iter);
            assert!(*prev == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i - 1;
        };
        let prev = prev(&tree, &mut iter);
        assert!(*prev == i, ENO_MESSAGE);
        assert!(!has_next(&iter), ENO_MESSAGE);
    }

    #[test]
    fun test_iter_reverse_traversal3() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 3, 3);

        let iter = init_iterator(true);

        let i = 5;
        while (i > 0) {
            let prev = prev(&tree, &mut iter);
            assert!(*prev == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i - 1;
        };
        let prev = prev(&tree, &mut iter);
        assert!(*prev == i, ENO_MESSAGE);
        assert!(!has_next(&iter), ENO_MESSAGE);
    }

    #[test]
    fun test_size_after_insert_remove1() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        assert!(size(&tree) == 1, ENO_MESSAGE);

        insert(&mut tree, 1, 1);
        assert!(size(&tree) == 2, ENO_MESSAGE);

        remove(&mut tree, 0);
        assert!(size(&tree) == 1, ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 2, ENO_MESSAGE);
        assert!(vector::length(&tree.removed_nodes) == 1, ENO_MESSAGE);

        insert(&mut tree, 0, 0);
        assert!(size(&tree) == 2, ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 2, ENO_MESSAGE);
        assert!(vector::length(&tree.removed_nodes) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_size_after_insert_remove2() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 3, 3);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 1, 1);
        assert!(size(&tree) == 3, ENO_MESSAGE);

        insert(&mut tree, 4, 4);
        insert(&mut tree, 0, 0);
        assert!(size(&tree) == 5, ENO_MESSAGE);

        remove(&mut tree, 0);
        remove(&mut tree, 1);
        assert!(size(&tree) == 3, ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 5, ENO_MESSAGE);
        assert!(vector::length(&tree.removed_nodes) == 2, ENO_MESSAGE);

        insert(&mut tree, 0, 0);
        assert!(size(&tree) == 4, ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 5, ENO_MESSAGE);
        assert!(vector::length(&tree.removed_nodes) == 1, ENO_MESSAGE);
    }
}
