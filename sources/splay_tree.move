module flow::splay_tree {
    use std::vector;
    use std::option::{Self, Option};
    use flow::guarded_idx::{GuardedIdx, guard, unguard, sentinel, is_sentinel};
    use flow::vector_utils::{top, pop};

    // *************************************************************************
    // * Error codes                                                           *
    // *************************************************************************

    const ENO_MESSAGE: u64 = 0;
    // invalid argument provided
    const EINVALID_ARGUMENT: u64 = 1;
    // key not found in the splay tree
    const EKEY_NOT_FOUND: u64 = 2;
    // provided nodes were not a parent-child pair
    const EPARENT_CHILD_MISMATCH: u64 = 3;
    // tree has zero nodes
    const ETREE_IS_EMPTY: u64 = 4;
    // tree is in invalid state
    const EINVALID_STATE: u64 = 5;
    // iterator already completed
    const EITER_ALREADY_DONE: u64 = 6;

    // *************************************************************************
    // * Structs                                                               *
    // *************************************************************************

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

    // *************************************************************************
    // * Public functions                                                      *
    // *************************************************************************

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

    public fun init_iterator(reverse: bool): Iterator {
        Iterator {
            stack: vector::empty(),
            reverse,
            is_done: false,
        }
    }

    public fun size<V: store + drop>(tree: &SplayTree<V>): u64 {
        vector::length(&tree.nodes) - vector::length(&tree.removed_nodes)
    }

    public fun is_empty<V: store + drop>(tree: &SplayTree<V>): bool {
        size(tree) == 0
    }

    public fun get<V: store + drop>(tree: &SplayTree<V>, key: u64): &V {
        let root = get_root(tree);
        assert!(!is_sentinel(root), ETREE_IS_EMPTY);

        let idx = get_idx_subtree(tree, unguard(root), key);
        let node = get_node_by_index(tree, idx);
        &node.value
    }

    public fun get_mut<V: store + drop>(tree: &mut SplayTree<V>, key: u64): &mut V {
        let root = get_root(tree);
        assert!(!is_sentinel(root), ETREE_IS_EMPTY);

        let idx = get_idx_subtree(tree, unguard(root), key);
        let node = get_mut_node_by_index(tree, idx);
        &mut node.value
    }

    public fun contains<V: store + drop>(tree: &SplayTree<V>, key: u64): bool {
        let root = get_root(tree);
        if (is_sentinel(root)) {
            false
        } else {
            contains_node_subtree(tree, unguard(root), key)
        }
    }

    public fun remove<V: store + drop>(tree: &mut SplayTree<V>, key: u64) {
        let maybe_root = get_root(tree);
        assert!(!is_sentinel(maybe_root), ETREE_IS_EMPTY);

        let root = unguard(maybe_root);
        remove_from_subtree(tree, root, option::none<u64>(), key);
    }

    public fun insert<V: store + drop>(tree: &mut SplayTree<V>, key: u64, value: V) {
        let maybe_root = get_root(tree);
        if (is_sentinel(maybe_root)) {
            assert!(size(tree) == 0, EINVALID_STATE);
            let node = init_node(key, value);
            vector::push_back(&mut tree.nodes, node);
            let root_idx = vector::length(&tree.nodes) - 1;

            set_root(tree, guard(root_idx));
            update_min(tree, key, root_idx);
            update_max(tree, key, root_idx);
        } else {
            assert!(!is_sentinel(maybe_root), ETREE_IS_EMPTY);
            assert!(!is_sentinel(tree.min), EINVALID_STATE);
            assert!(!is_sentinel(tree.max), EINVALID_STATE);

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

    public fun min<V: store + drop>(tree: &SplayTree<V>): &V {
        assert!(!is_sentinel(tree.root), ETREE_IS_EMPTY);
        assert!(!is_sentinel(tree.min), EINVALID_STATE);
        let min_idx = unguard(tree.min);
        &get_node_by_index(tree, min_idx).value
    }

    public fun max<V: store + drop>(tree: &SplayTree<V>): &V {
        assert!(!is_sentinel(tree.root), ETREE_IS_EMPTY);
        assert!(!is_sentinel(tree.max), EINVALID_STATE);
        let max_idx = unguard(tree.max);
        &get_node_by_index(tree, max_idx).value
    }

    public fun splay<V: store + drop>(tree: &mut SplayTree<V>, key: u64) {
        let maybe_root = get_root(tree);
        assert!(!is_sentinel(maybe_root), ETREE_IS_EMPTY);

        let root = unguard(maybe_root);
        let root_node = get_node_by_index(tree, root);

        // splay operation cannot be performed on root node
        if (key == root_node.key) {
            return
        };

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

    public fun next<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator): (u64, &V) {
        if (!iter.reverse) {
            let idx = next_node_idx(tree, iter);
            check_is_done(tree, iter, idx);
            let node = get_node_by_index(tree, idx);
            return (node.key, &node.value)
        } else {
            let idx = prev_node_idx(tree, iter);
            check_is_done(tree, iter, idx);
            let node = get_node_by_index(tree, idx);
            return (node.key, &node.value)
        }
    }

    public fun next_mut<V: store + drop>(tree: &mut SplayTree<V>, iter: &mut Iterator): (u64, &mut V) {
        if (!iter.reverse) {
            let idx = next_node_idx(tree, iter);
            check_is_done(tree, iter, idx);
            let node = get_mut_node_by_index(tree, idx);
            return (node.key, &mut node.value)
        } else {
            let idx = prev_node_idx(tree, iter);
            check_is_done(tree, iter, idx);
            let node = get_mut_node_by_index(tree, idx);
            return (node.key, &mut node.value)
        }
    }

    public fun has_next(iter: &Iterator): bool {
        !iter.is_done
    }

    public fun remove_nodes_less_than<V: store + drop>(tree: &mut SplayTree<V>, key: u64) {
        let iter = init_iterator(false);
        let nodes_to_remove = vector::empty<u64>();

        while (has_next(&iter)) {
            let idx = next_node_idx(tree, &mut iter);
            let node = get_node_by_index(tree, idx);

            if (key > node.key) {
                vector::push_back(&mut nodes_to_remove, idx);
            } else {
                let current = vector::pop_back(&mut iter.stack);
                assert!(current == idx, EINVALID_STATE);

                let child = current;
                set_left(tree, idx, sentinel());

                while (!vector::is_empty(&iter.stack)) {
                    let parent = top(&iter.stack);
                    let maybe_left = get_left(tree, parent);
                    let maybe_right = get_right(tree, parent);

                    if (!is_sentinel(maybe_left) && unguard(maybe_left) == current) {
                        set_left(tree, parent, guard(child));
                        current = vector::pop_back(&mut iter.stack);
                        child = current;
                    } else if (!is_sentinel(maybe_right) && unguard(maybe_right) == current) {
                        current = vector::pop_back(&mut iter.stack);
                    } else {
                        abort EPARENT_CHILD_MISMATCH
                    };
                };
                vector::append(&mut tree.removed_nodes, nodes_to_remove);
                set_root(tree, guard(child));
                return
            };
            check_is_done(tree, &mut iter, idx);
        }
    }

    public fun remove_nodes_greater_than<V: store + drop>(tree: &mut SplayTree<V>, key: u64) {
        let iter = init_iterator(true);
        let nodes_to_remove = vector::empty<u64>();

        while (has_next(&iter)) {
            let idx = prev_node_idx(tree, &mut iter);
            let node = get_node_by_index(tree, idx);

            if (key < node.key) {
                vector::push_back(&mut nodes_to_remove, idx);
            } else {
                let current = vector::pop_back(&mut iter.stack);
                assert!(current == idx, EINVALID_STATE);

                let child = current;
                set_right(tree, idx, sentinel());

                while (!vector::is_empty(&iter.stack)) {
                    let parent = top(&iter.stack);
                    let maybe_left = get_left(tree, parent);
                    let maybe_right = get_right(tree, parent);

                    if (!is_sentinel(maybe_left) && unguard(maybe_left) == current) {
                        current = vector::pop_back(&mut iter.stack);
                    } else if (!is_sentinel(maybe_right) && unguard(maybe_right) == current) {
                        set_right(tree, parent, guard(child));
                        current = vector::pop_back(&mut iter.stack);
                        child = current;
                    } else {
                        abort EPARENT_CHILD_MISMATCH
                    };
                };
                vector::append(&mut tree.removed_nodes, nodes_to_remove);
                set_root(tree, guard(child));
                return
            };
            check_is_done(tree, &mut iter, idx);
        }
    }

    // *************************************************************************
    // * Private functions                                                     *
    // *************************************************************************

    fun init_node<V: store + drop>(key: u64, value: V): Node<V> {
        Node {
            key,
            value,
            left: sentinel(),
            right: sentinel(),
        }
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

    fun move_parent_pointer<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, parent_idx: Option<u64>, move_to: GuardedIdx) {
        if (option::is_some(&parent_idx)) {
            let parent_idx = *option::borrow(&parent_idx);
            let parent_node = get_mut_node_by_index(tree, parent_idx);

            assert!(is_sentinel(move_to) || parent_idx != unguard(move_to), EINVALID_ARGUMENT);

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
            assert!(!is_sentinel(tree.root), ETREE_IS_EMPTY);
            let root = unguard(tree.root);
            assert!(root == parent_idx, EPARENT_CHILD_MISMATCH);
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
            assert!(!is_sentinel(tree.root), ETREE_IS_EMPTY);
            let root = unguard(tree.root);
            assert!(root == parent_idx, EPARENT_CHILD_MISMATCH);
            set_root(tree, guard(child_idx));
        }
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

    fun check_is_done<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator, idx: u64) {
        assert!(!is_sentinel(tree.min), EINVALID_STATE);
        assert!(!is_sentinel(tree.max), EINVALID_STATE);

        if (!iter.reverse) {
            let max = unguard(tree.max);
            let max_node_key = get_node_by_index(tree, max).key;
            let node = get_node_by_index(tree, idx);

            if (node.key == max_node_key) {
                iter.is_done = true;
            };
        } else {
            let min = unguard(tree.min);
            let min_node_key = get_node_by_index(tree, min).key;
            let node = get_node_by_index(tree, idx);

            if (node.key == min_node_key) {
                iter.is_done = true;
            };
        }
    }

    fun next_node_idx<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator): u64 {
        let maybe_root = get_root(tree);

        assert!(!iter.is_done, EITER_ALREADY_DONE);
        assert!(!is_sentinel(maybe_root), ETREE_IS_EMPTY);

        let root = unguard(maybe_root);

        if (vector::is_empty(&iter.stack)) {
            let current = root;
            traverse_left(tree, iter, current);
            let idx = top(&iter.stack);
            return idx
        };
        let current = top(&iter.stack);
        let maybe_right = get_right(tree, current);
        if (!is_sentinel(maybe_right)) {
            current = unguard(maybe_right);
            traverse_left(tree, iter, current);

            let idx = top(&iter.stack);
            return idx
        } else {
            let current = vector::pop_back(&mut iter.stack);
            let parent = top(&iter.stack);

            while (current != root) {
                let maybe_parent_left = get_left(tree, parent);
                let maybe_parent_right = get_right(tree, parent);

                if (!is_sentinel(maybe_parent_left) && unguard(maybe_parent_left) == current) {
                    return parent
                } else if (!is_sentinel(maybe_parent_right) && unguard(maybe_parent_right) == current) {
                    current = vector::pop_back(&mut iter.stack);
                    parent = top(&iter.stack);
                } else {
                    abort EPARENT_CHILD_MISMATCH
                };
            };
            abort EITER_ALREADY_DONE
        }
    }

    fun prev_node_idx<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator): u64 {
        let maybe_root = get_root(tree);

        assert!(!iter.is_done, EITER_ALREADY_DONE);
        assert!(!is_sentinel(maybe_root), ETREE_IS_EMPTY);

        let root = unguard(maybe_root);

        if (vector::is_empty(&iter.stack)) {
            let current = root;
            traverse_right(tree, iter, current);
            let idx = top(&iter.stack);
            return idx
        };
        let current = top(&iter.stack);
        let maybe_left = get_left(tree, current);
        if (!is_sentinel(maybe_left)) {
            current = unguard(maybe_left);
            traverse_right(tree, iter, current);
            let idx = top(&iter.stack);
            return idx
        } else {
            let current = vector::pop_back(&mut iter.stack);
            let parent = top(&iter.stack);

            while (current != root) {
                let maybe_parent_left = get_left(tree, parent);
                let maybe_parent_right = get_right(tree, parent);

                if (!is_sentinel(maybe_parent_right) && unguard(maybe_parent_right) == current) {
                    return parent
                } else if (!is_sentinel(maybe_parent_left) && unguard(maybe_parent_right) == current) {
                    current = vector::pop_back(&mut iter.stack);
                    parent = top(&iter.stack);
                } else {
                    abort EPARENT_CHILD_MISMATCH
                };
            };
            abort EITER_ALREADY_DONE
        }
    }

    // *************************************************************************
    // * Unit tests                                                            *
    // *************************************************************************

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
    #[expected_failure(abort_code = 4)]
    fun test_min_empty() {
        let tree = init_tree<u64>(true);
        let _min = min(&tree);
    }

    #[test]
    #[expected_failure(abort_code = 4)]
    fun test_max_empty() {
        let tree = init_tree<u64>(true);
        let _max = max(&tree);
    }

    #[test]
    fun test_equal_min_max() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 2, 2);

        let min = min(&tree);
        let max = max(&tree);

        assert!(*min == 2, ENO_MESSAGE);
        assert!(*max == 2, ENO_MESSAGE);
    }

    #[test]
    fun test_size() {
        let tree = init_tree<u64>(true);
        
        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);
        
        assert!(size(&tree) == 6, ENO_MESSAGE);
    }

    #[test]
    fun test_size_empty() {
        let tree = init_tree<u64>(true);
        assert!(size(&tree) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_is_empty() {
        let tree = init_tree<u64>(true);
        assert!(is_empty(&tree), ENO_MESSAGE);
    }

    #[test]
    fun test_is_not_empty() {
        let tree = init_tree<u64>(true);
        insert(&mut tree, 0, 0);
        assert!(!is_empty(&tree), ENO_MESSAGE);
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
    }

    #[test]
    fun test_does_not_contain() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);

        assert!(contains(&tree, 0), ENO_MESSAGE);
        assert!(contains(&tree, 1), ENO_MESSAGE);
        assert!(contains(&tree, 2), ENO_MESSAGE);
        assert!(!contains(&tree, 3), ENO_MESSAGE);
        assert!(!contains(&tree, 4), ENO_MESSAGE);
        assert!(!contains(&tree, 5), ENO_MESSAGE);
    }

    #[test]
    fun test_contains_empty_tree() {
        let tree = init_tree<u64>(true);
        assert!(!contains(&tree, 0), ENO_MESSAGE);
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
    fun test_splay_root() {
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

        // nothing should happen
        splay(&mut tree, 5);

        let root = unguard(get_root(&tree));
        let root_node = get_node_by_index(&tree, root);
        assert!(root_node.key == 5, ENO_MESSAGE);
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
            let (_, next) = next(&tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i + 1;
        };
        let (_, next) = next(&tree, &mut iter);
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
            let (_, next) = next(&tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i + 1;
        };
        let (_, next) = next(&tree, &mut iter);
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
            let (_, next) = next(&tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i + 1;
        };
        let (_, next) = next(&tree, &mut iter);
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
            let (_, next) = next(&tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i - 1;
        };
        let (_, next) = next(&tree, &mut iter);
        assert!(*next == i, ENO_MESSAGE);
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
            let (_, next) = next(&tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i - 1;
        };
        let (_, next) = next(&tree, &mut iter);
        assert!(*next == i, ENO_MESSAGE);
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
            let (_, next) = next(&tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);
            assert!(has_next(&iter), ENO_MESSAGE);
            i = i - 1;
        };
        let (_, next) = next(&tree, &mut iter);
        assert!(*next == i, ENO_MESSAGE);
        assert!(!has_next(&iter), ENO_MESSAGE);
    }

    #[test]
    #[expected_failure(abort_code = 6)]
    fun test_iterator_next_after_done() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        let iter = init_iterator(false);

        while (has_next(&iter)) {
            let (_key, _next) = next(&tree, &mut iter);
        };
        next(&tree, &mut iter);
    }

    #[test]
    #[expected_failure(abort_code = 6)]
    fun test_reverse_iterator_next_after_done() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        let iter = init_iterator(true);

        while (has_next(&iter)) {
            let (_key, _next) = next(&tree, &mut iter);
        };
        next(&tree, &mut iter);
    }

    #[test]
    fun test_iter_traversal_mut() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        assert!(*min(&tree) == 0, ENO_MESSAGE);
        assert!(*max(&tree) == 5, ENO_MESSAGE);

        let iter = init_iterator(false);

        let i = 0;
        while (i < 5) {
            let (_, next) = next_mut(&mut tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);

            *next = *next + 1;
            assert!(*next == i + 1, ENO_MESSAGE);

            assert!(has_next(&iter), ENO_MESSAGE);
            i = i + 1;
        };
        let (_, next) = next_mut(&mut tree, &mut iter);
        assert!(*next == i, ENO_MESSAGE);

        *next = *next + 1;
        assert!(*next == i + 1, ENO_MESSAGE);

        assert!(!has_next(&iter), ENO_MESSAGE);

        assert!(*min(&tree) == 1, ENO_MESSAGE);
        assert!(*max(&tree) == 6, ENO_MESSAGE);
    }

    #[test]
    fun test_iter_reverse_traversal_mut() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        assert!(*min(&tree) == 0, ENO_MESSAGE);
        assert!(*max(&tree) == 5, ENO_MESSAGE);

        let iter = init_iterator(true);

        let i = 5;
        while (i > 0) {
            let (_, next) = next_mut(&mut tree, &mut iter);
            assert!(*next == i, ENO_MESSAGE);

            *next = *next + 1;
            assert!(*next == i + 1, ENO_MESSAGE);

            assert!(has_next(&iter), ENO_MESSAGE);
            i = i - 1;
        };
        let (_, next) = next_mut(&mut tree, &mut iter);
        assert!(*next == i, ENO_MESSAGE);

        *next = *next + 1;
        assert!(*next == i + 1, ENO_MESSAGE);

        assert!(!has_next(&iter), ENO_MESSAGE);

        assert!(*min(&tree) == 1, ENO_MESSAGE);
        assert!(*max(&tree) == 6, ENO_MESSAGE);
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

    #[test]
    fun test_remove_nodes_less_than_1() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        remove_nodes_less_than(&mut tree, 3);

        assert!(!contains(&tree, 0), ENO_MESSAGE);
        assert!(!contains(&tree, 1), ENO_MESSAGE);
        assert!(!contains(&tree, 2), ENO_MESSAGE);
        assert!(contains(&tree, 3), ENO_MESSAGE);
        assert!(contains(&tree, 4), ENO_MESSAGE);
        assert!(contains(&tree, 5), ENO_MESSAGE);
    }

    #[test]
    fun test_remove_nodes_less_than_2() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 1, 1);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 0, 0);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 2, 2);

        remove_nodes_less_than(&mut tree, 3);

        assert!(!contains(&tree, 0), ENO_MESSAGE);
        assert!(!contains(&tree, 1), ENO_MESSAGE);
        assert!(!contains(&tree, 2), ENO_MESSAGE);
        assert!(contains(&tree, 3), ENO_MESSAGE);
        assert!(contains(&tree, 4), ENO_MESSAGE);
        assert!(contains(&tree, 5), ENO_MESSAGE);
    }

    #[test]
    fun test_remove_nodes_less_than_3() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 3, 3);

        remove_nodes_less_than(&mut tree, 3);

        assert!(!contains(&tree, 0), ENO_MESSAGE);
        assert!(!contains(&tree, 1), ENO_MESSAGE);
        assert!(!contains(&tree, 2), ENO_MESSAGE);
        assert!(contains(&tree, 3), ENO_MESSAGE);
        assert!(contains(&tree, 4), ENO_MESSAGE);
        assert!(contains(&tree, 5), ENO_MESSAGE);
    }

    #[test]
    fun test_remove_nodes_greater_than_1() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        remove_nodes_greater_than(&mut tree, 2);

        assert!(contains(&tree, 0), ENO_MESSAGE);
        assert!(contains(&tree, 1), ENO_MESSAGE);
        assert!(contains(&tree, 2), ENO_MESSAGE);
        assert!(!contains(&tree, 3), ENO_MESSAGE);
        assert!(!contains(&tree, 4), ENO_MESSAGE);
        assert!(!contains(&tree, 5), ENO_MESSAGE);
    }

    #[test]
    fun test_remove_nodes_greater_than_2() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 1, 1);

        remove_nodes_greater_than(&mut tree, 2);

        assert!(contains(&tree, 0), ENO_MESSAGE);
        assert!(contains(&tree, 1), ENO_MESSAGE);
        assert!(contains(&tree, 2), ENO_MESSAGE);
        assert!(!contains(&tree, 3), ENO_MESSAGE);
        assert!(!contains(&tree, 4), ENO_MESSAGE);
        assert!(!contains(&tree, 5), ENO_MESSAGE);
    }

    #[test]
    fun test_remove_nodes_greater_than_3() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 3, 3);

        remove_nodes_greater_than(&mut tree, 2);

        assert!(contains(&tree, 0), ENO_MESSAGE);
        assert!(contains(&tree, 1), ENO_MESSAGE);
        assert!(contains(&tree, 2), ENO_MESSAGE);
        assert!(!contains(&tree, 3), ENO_MESSAGE);
        assert!(!contains(&tree, 4), ENO_MESSAGE);
        assert!(!contains(&tree, 5), ENO_MESSAGE);
    }
}
