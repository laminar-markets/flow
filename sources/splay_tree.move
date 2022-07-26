module flow::splay_tree {
    use std::vector;
    use std::option::{Self, Option};

    const ENO_MESSAGE: u64 = 0;
    const EKEY_NOT_FOUND: u64 = 1;
    const EPARENT_CHILD_MISMATCH: u64 = 2;
    const EITER_DONE: u64 = 3;

    struct Node<V: store + drop> has store, drop {
        key: u64,
        value: V,
        left: Option<u64>,
        right: Option<u64>
    }

    struct SplayTree<V: store + drop> has store, drop {
        root: Option<u64>,
        nodes: vector<Node<V>>,
        single_splay: bool,
    }

    struct Iterator has drop {
        current_node: Option<u64>,
        stack: vector<u64>,
        reverse: bool,
        is_done: bool,
    }

    public fun init_tree<V: store + drop>(single_splay: bool): SplayTree<V> {
        SplayTree {
            root: option::none(),
            nodes: vector::empty<Node<V>>(),
            single_splay,
        }
    }

    fun init_node<V: store + drop>(key: u64, value: V): Node<V> {
        Node {
            key,
            value,
            left: option::none<u64>(),
            right: option::none<u64>(),
        }
    }

    public fun init_iterator(reverse: bool): Iterator {
        Iterator {
            current_node: option::none<u64>(),
            stack: vector::empty(),
            reverse,
            is_done: false,
        }
    }

    fun get_left<V: store + drop>(tree: &SplayTree<V>, idx: u64): Option<u64> {
        vector::borrow(&tree.nodes, idx).left
    }

    fun get_right<V: store + drop>(tree: &SplayTree<V>, idx: u64): Option<u64> {
        vector::borrow(&tree.nodes, idx).right
    }

    fun set_left<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, update_to: Option<u64>) {
        vector::borrow_mut(&mut tree.nodes, idx).left = update_to;
    }

    fun set_right<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, update_to: Option<u64>) {
        vector::borrow_mut(&mut tree.nodes, idx).right = update_to;
    }

    fun get_root<V: store + drop>(tree: &SplayTree<V>): Option<u64> {
        tree.root
    }

    fun set_root<V: store + drop>(tree: &mut SplayTree<V>, update_to: u64) {
        tree.root = option::some(update_to);
    }

    fun get_node_by_index<V: store + drop>(tree: &SplayTree<V>, idx: u64): &Node<V> {
        vector::borrow(&tree.nodes, idx)
    }

    fun get_node_subtree<V: store + drop>(tree: &SplayTree<V>, parent_idx: u64, key: u64): &V {
        let parent_node = vector::borrow(&tree.nodes, parent_idx);
        if (key == parent_node.key) {
            &parent_node.value
        } else if (key < parent_node.key) {
            assert!(option::is_some(&parent_node.left), EKEY_NOT_FOUND);
            get_node_subtree(tree, *option::borrow(&parent_node.left), key)
        } else {
            assert!(option::is_some(&parent_node.right), EKEY_NOT_FOUND);
            get_node_subtree(tree, *option::borrow(&parent_node.right), key)
        }
    }

    fun get_mut_node_subtree<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, key: u64): &mut V {
        let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
        if (key == parent_node.key) {
            &mut parent_node.value
        } else if (key < parent_node.key) {
            assert!(option::is_some(&parent_node.left), EKEY_NOT_FOUND);
            get_mut_node_subtree(tree, *option::borrow(&parent_node.left), key)
        } else {
            assert!(option::is_some(&parent_node.right), EKEY_NOT_FOUND);
            get_mut_node_subtree(tree, *option::borrow(&parent_node.right), key)
        }
    }

    public fun size<V: store + drop>(tree: &SplayTree<V>): u64 {
        // TODO deal with deleted nodes
        vector::length(&tree.nodes)
    }

    public fun get<V: store + drop>(tree: &SplayTree<V>, key: u64): &V {
        let root = get_root(tree);
        assert!(option::is_some(&root), ENO_MESSAGE);
        get_node_subtree(tree, *option::borrow(&root), key)
    }

    public fun get_mut<V: store + drop>(tree: &mut SplayTree<V>, key: u64): &mut V {
        let root = get_root(tree);
        assert!(option::is_some(&root), ENO_MESSAGE);
        get_mut_node_subtree(tree, *option::borrow(&root), key)
    }

    fun contains_node_subtree<V: store + drop>(tree: &SplayTree<V>, parent_idx: u64, key: u64): bool {
        let parent_node = vector::borrow(&tree.nodes, parent_idx);
        if (key == parent_node.key) {
            true
        } else if (key < parent_node.key && option::is_some(&parent_node.left)) {
            contains_node_subtree(tree, *option::borrow(&parent_node.left), key)
        } else if (key > parent_node.key && option::is_some(&parent_node.right)) {
            contains_node_subtree(tree, *option::borrow(&parent_node.right), key)
        } else {
            false
        }
    }

    public fun contains<V: store + drop>(tree: &SplayTree<V>, key: u64): bool {
        let root = get_root(tree);
        if (option::is_none(&root)) {
            false
        } else {
            contains_node_subtree(tree, *option::borrow(&root), key)
        }
    }

    fun insert_child<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, grandparent_idx: Option<u64>, node: Node<V>) {
        let parent_node = vector::borrow(&tree.nodes, parent_idx);
        let new_node_idx = vector::length(&tree.nodes);

        if (node.key < parent_node.key) {
            if (option::is_none(&parent_node.left)) {
                vector::push_back(&mut tree.nodes, node);
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.left = option::some(new_node_idx);
                rotate_right(tree, parent_idx, grandparent_idx, new_node_idx);
            } else {
                insert_child(tree, *option::borrow(&parent_node.left), option::some(parent_idx), node);
                if (!tree.single_splay) {
                    rotate_right(tree, parent_idx, grandparent_idx, new_node_idx);
                }
            }
        } else if (node.key > parent_node.key) {
            if (option::is_none(&parent_node.right)) {
                vector::push_back(&mut tree.nodes, node);
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.right = option::some(new_node_idx);
                rotate_left(tree, parent_idx, grandparent_idx, new_node_idx);
            } else {
                insert_child(tree, *option::borrow(&parent_node.right), option::some(parent_idx), node);
                if (!tree.single_splay) {
                    rotate_left(tree, parent_idx, grandparent_idx, new_node_idx);
                }
            }
        }
    }
    
    public fun insert<V: store + drop>(tree: &mut SplayTree<V>, key: u64, value: V) {
        let node = init_node(key, value);
        if (option::is_none(&tree.root)) {
            vector::push_back(&mut tree.nodes, node);
            set_root(tree, 0);
        } else {
            let root = get_root(tree);
            assert!(option::is_some(&root), ENO_MESSAGE);
            insert_child(tree, *option::borrow(&root), option::none<u64>(), node);
        }
    }

    fun rotate_left<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, grandparent_idx: Option<u64>, child_idx: u64) {
        let child_left = get_left(tree, child_idx);
        set_right(tree, parent_idx, child_left);
        set_left(tree, child_idx, option::some(parent_idx));

        if (option::is_some(&grandparent_idx)) {
            let grandparent_idx = *option::borrow(&grandparent_idx);
            if (get_left(tree, grandparent_idx) == option::some(parent_idx)) {
                set_left(tree, grandparent_idx, option::some(child_idx));
            } else if (get_right(tree, grandparent_idx) == option::some(parent_idx)) {
                set_right(tree, grandparent_idx, option::some(child_idx));
            } else {
                abort EPARENT_CHILD_MISMATCH
            }
        } else {
            let root = get_root(tree);
            assert!(option::is_some(&root), ENO_MESSAGE);
            assert!(*option::borrow(&root) == parent_idx, ENO_MESSAGE);
            set_root(tree, child_idx);
        }
    }

    fun rotate_right<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, grandparent_idx: Option<u64>, child_idx: u64) {
        let child_right = get_right(tree, child_idx);
        set_left(tree, parent_idx, child_right);
        set_right(tree, child_idx, option::some(parent_idx));

        if (option::is_some(&grandparent_idx)) {
            let grandparent_idx = *option::borrow(&grandparent_idx);
            if (get_left(tree, grandparent_idx) == option::some(parent_idx)) {
                set_left(tree, grandparent_idx, option::some(child_idx));
            } else if (get_right(tree, grandparent_idx) == option::some(parent_idx)) {
                set_right(tree, grandparent_idx, option::some(child_idx));
            } else {
                abort EPARENT_CHILD_MISMATCH
            }
        } else {
            let root = get_root(tree);
            assert!(option::is_some(&root), ENO_MESSAGE);
            assert!(*option::borrow(&root) == parent_idx, ENO_MESSAGE);
            set_root(tree, child_idx);
        }
    }

    fun min_subtree<V: store + drop>(tree: &SplayTree<V>, idx: u64): u64 {
        let maybe_left = get_left(tree, idx);
        if (option::is_none(&maybe_left)) {
            idx
        } else {
            min_subtree(tree, *option::borrow(&maybe_left))
        }
    }

    public fun min<V: store + drop>(tree: &SplayTree<V>): &Node<V> {
        assert!(option::is_some(&get_root(tree)), ENO_MESSAGE);
        let min_idx = min_subtree(tree, *option::borrow(&get_root(tree)));
        get_node_by_index(tree, min_idx)
    }

    fun max_subtree<V: store + drop>(tree: &SplayTree<V>, idx: u64): u64 {
        let maybe_right = get_right(tree, idx);
        if (option::is_none(&maybe_right)) {
            idx
        } else {
            max_subtree(tree, *option::borrow(&maybe_right))
        }
    }

    public fun max<V: store + drop>(tree: &SplayTree<V>): &Node<V> {
        assert!(option::is_some(&get_root(tree)), ENO_MESSAGE);
        let max_idx = max_subtree(tree, *option::borrow(&get_root(tree)));
        get_node_by_index(tree, max_idx)
    }

    fun stack_left<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator, parent_idx: u64) {
        let maybe_left = option::some(parent_idx);
        while (option::is_some(&maybe_left)) {
            let current = *option::borrow(&maybe_left);
            maybe_left = get_left(tree, current);
            vector::push_back(&mut iter.stack, current);
        };
    }

    fun top<T: copy>(v: &vector<T>): T {
        *vector::borrow(v, vector::length(v) - 1)
    }

    public fun next<V: store + drop>(tree: &SplayTree<V>, iter: &mut Iterator): &Node<V> {
        assert!(!iter.is_done, EITER_DONE);
        assert!(!iter.reverse, ENO_MESSAGE);
        assert!(option::is_some(&get_root(tree)), ENO_MESSAGE);

        if (option::is_none(&iter.current_node)) {
            let current = *option::borrow(&get_root(tree));
            let maybe_left = get_left(tree, current);
            if (option::is_some(&maybe_left)) {
                stack_left(tree, iter, current);
                let res = top(&iter.stack);
                iter.current_node = option::some(res);
                return get_node_by_index(tree, res)
            }
        };
        let current = *option::borrow(&iter.current_node);
        let maybe_right = get_right(tree, current);
        if (option::is_some(&maybe_right)) {
            current = *option::borrow(&maybe_right);
            stack_left(tree, iter, current);
            let res = top(&iter.stack);
            iter.current_node = option::some(res);
            return get_node_by_index(tree, res)
        } else {
            let current = vector::pop_back(&mut iter.stack);
            let parent = top(&iter.stack);

            while (current != *option::borrow(&get_root(tree))) {
                let maybe_parent_left = get_left(tree, parent);
                let maybe_parent_right = get_right(tree, parent);

                if (option::is_some(&maybe_parent_left) && *option::borrow(&maybe_parent_left) == current) {
                    iter.current_node = option::some(parent);
                    if (vector::length(&iter.stack) == 1) {
                        iter.is_done = true;
                    };
                    return get_node_by_index(tree, parent)
                } else if (option::is_some(&maybe_parent_right) && *option::borrow(&maybe_parent_right) == current) {
                    current = vector::pop_back(&mut iter.stack);
                    parent = top(&iter.stack);
                } else {
                    abort EPARENT_CHILD_MISMATCH
                };
            };
            abort EITER_DONE
        }
    }

    #[test]
    fun test_init_tree() {
        let tree = init_tree<u64>(true);

        assert!(option::is_none(&tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_init_node() {
        let node = init_node<u64>(0, 0);

        assert!(node.key == 0, ENO_MESSAGE);
        assert!(node.value == 0, ENO_MESSAGE);
        assert!(option::is_none(&node.left), ENO_MESSAGE);
        assert!(option::is_none(&node.right), ENO_MESSAGE);
    }

    #[test]
    fun test_add_node() {
        let tree = init_tree<u64>(true);

        assert!(option::is_none(&tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 0, ENO_MESSAGE);

        insert(&mut tree, 0, 0);

        assert!(option::is_some(&tree.root), ENO_MESSAGE);
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
         assert!(option::is_some(&maybe_root), ENO_MESSAGE);

         let root = *option::borrow(&maybe_root);
         let root_node = vector::borrow(&tree.nodes, root);

         assert!(vector::length(&tree.nodes) == 2, ENO_MESSAGE);
         assert!(root_node.key == key1, ENO_MESSAGE);
         assert!(*option::borrow(&get_left(&tree, root)) == key0, ENO_MESSAGE);
         assert!(option::is_none(&get_right(&tree, root)), ENO_MESSAGE);
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
        assert!(option::is_some(&maybe_root), ENO_MESSAGE);

        let root = *option::borrow(&maybe_root);
        let root_node = vector::borrow(&tree.nodes, root);

        assert!(size(&tree) == 3, ENO_MESSAGE);
        assert!(root_node.key == key2, ENO_MESSAGE);
        assert!(*option::borrow(&get_left(&tree, root)) == key1, ENO_MESSAGE);
        assert!(option::is_none(&get_right(&tree, root)), ENO_MESSAGE);

        let maybe_root_left = get_left(&tree, root);
        assert!(option::is_some(&maybe_root_left), ENO_MESSAGE);
        let root_left = *option::borrow(&maybe_root_left);

        assert!(get_node_by_index(&tree, root_left).key == key1, ENO_MESSAGE);
        assert!(get_node_by_index(&tree, *option::borrow(&get_node_by_index(&tree, root_left).left)).key == key0, ENO_MESSAGE);

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
        assert!(min.key == 1, ENO_MESSAGE);
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
        assert!(max.key == 5, ENO_MESSAGE);
    }

     #[test]
     fun test_get_by_key() {
         let tree = init_tree<u64>(true);

         insert(&mut tree, 1, 1);
         insert(&mut tree, 0, 0);

         // Tree should look like
         //  0
         //   \
         //    1

         let root = *option::borrow(&get_root(&tree));
         let root_node = get_node_by_index(&tree, root);
         assert!(root_node.key == 0, ENO_MESSAGE);

         let maybe_root_right = root_node.right;
         let root_right = *option::borrow(&maybe_root_right);
         let root_right_node = get_node_by_index(&tree, root_right);
         assert!(root_right_node.key == 1, ENO_MESSAGE);

         insert(&mut tree, 2, 2);
         // Tree should look like
         //  0
         //   \
         //    2
         //   /
         //  1

         let root = *option::borrow(&get_root(&tree));
         let root_node = get_node_by_index(&tree, root);

         let maybe_root_right = root_node.right;

         assert!(option::is_some(&maybe_root_right), ENO_MESSAGE);

         let root_right = *option::borrow(&maybe_root_right);
         let root_right_node = get_node_by_index(&tree, root_right);
         assert!(root_right_node.key == 2, ENO_MESSAGE);

         let child = *option::borrow(&root_right_node.left);
         let child_node = get_node_by_index(&tree, child);

         assert!(child_node.key == 1, ENO_MESSAGE);

         assert!(*get(&tree, 0) == 0, ENO_MESSAGE);
         assert!(*get(&tree, 1) == 1, ENO_MESSAGE);
         assert!(*get(&tree, 2) == 2, ENO_MESSAGE);
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
    fun test_get_mut() {
        let tree = init_tree<u64>(true);
        insert(&mut tree, 2, 2);
        let mutable_node = get_mut(&mut tree, 2);
        assert!(*mutable_node == 2, ENO_MESSAGE);
        *mutable_node = 3;
        let node = get(&mut tree, 2);
        assert!(*node == 3, ENO_MESSAGE);
    }

    #[test]
    fun test_init_iter() {
        let iter = init_iterator(false);

        assert!(iter.current_node == option::none(), ENO_MESSAGE);
        assert!(vector::is_empty(&iter.stack), ENO_MESSAGE);
        assert!(!iter.reverse, ENO_MESSAGE);
    }

    #[test]
    fun test_iter_traversal() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);

        let iter = init_iterator(false);

        let i = 0;
        while (i < 6) {
            let next = next(&tree, &mut iter);
            assert!(next.value == i, ENO_MESSAGE);
            i = i + 1;
        };

        assert!(iter.is_done, ENO_MESSAGE);
    }
}
