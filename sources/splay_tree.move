module flow::splay_tree {
    use std::vector;
    use std::option::{Self, Option};

    const NULL_PTR: u64 = 0xffffffffffffffff;

    // TODO error codes
    const ENO_MESSAGE: u64 = 0;

    struct Node<V: store + drop> has store, drop {
        key: u64,
        value: V,
        left: u64,
        right: u64
    }

    struct SplayTree<V: store + drop> has store, drop {
        root: Option<u64>,
        nodes: vector<Node<V>>,
    }

    public fun init_tree<V: store + drop>(): SplayTree<V> {
        SplayTree {
            root: option::none(),
            nodes: vector::empty<Node<V>>(),
        }
    }

    fun init_node<V: store + drop>(key: u64, value: V): Node<V> {
        Node {
            key,
            value,
            left: NULL_PTR,
            right: NULL_PTR
        }
    }

    fun get_left<V: store + drop>(tree: &SplayTree<V>, idx: u64): u64 {
        vector::borrow(&tree.nodes, idx).left
    }

    fun get_right<V: store + drop>(tree: &SplayTree<V>, idx: u64): u64 {
        vector::borrow(&tree.nodes, idx).right
    }

    fun set_left<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, update_to: u64) {
        vector::borrow_mut(&mut tree.nodes, idx).left = update_to;
    }

    fun set_right<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, update_to: u64) {
        vector::borrow_mut(&mut tree.nodes, idx).right = update_to;
    }

    fun get_root<V: store + drop>(tree: &SplayTree<V>): Option<u64> {
        tree.root
    }

    fun set_root<V: store + drop>(tree: &mut SplayTree<V>, update_to: u64) {
        tree.root = option::some(update_to);
    }

//    fun get_root_node<V: store + drop>(tree: &SplayTree<V>): Option<Node<V>> {
//        if (option::is_none(&tree.root)) {
//            option::none<&Node<V>>()
//        };
//        *option::some(vector::borrow(&tree.nodes, *option::borrow(&tree.root)))
//    }

    fun get_node_by_index<V: store + drop>(tree: &SplayTree<V>, idx: u64): &Node<V> {
        vector::borrow(&tree.nodes, idx)
    }

    fun get_node_by_key_internal<V: store + drop>(tree: &SplayTree<V>, parent_idx: u64, key: u64): &Node<V> {
        assert!(parent_idx != NULL_PTR, ENO_MESSAGE);
        let parent_node = vector::borrow(&tree.nodes, parent_idx);
        if (key == parent_node.key) {
            parent_node
        } else if (key < parent_node.key) {
            get_node_by_key_internal(tree, parent_node.left, key)
        } else {
            get_node_by_key_internal(tree, parent_node.right, key)
        }
    }

    fun get_node_by_key<V: store + drop>(tree: &SplayTree<V>, key: u64): &Node<V> {
        let root = get_root(tree);
        assert!(option::is_some(&root), ENO_MESSAGE);
        get_node_by_key_internal(tree, *option::borrow(&root), key)
    }

    fun insert_internal<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, node: Node<V>) {
        let parent_node = vector::borrow(&tree.nodes, parent_idx);
        let node_count = vector::length(&tree.nodes);

        if (node.key < parent_node.key) {
            if (parent_node.left == NULL_PTR) {
                vector::push_back(&mut tree.nodes, node);
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.left = node_count;
            } else {
                insert_internal(tree, parent_node.left, node);
            }
        } else if (node.key > parent_node.key) {
            if (parent_node.right == NULL_PTR) {
                vector::push_back(&mut tree.nodes, node);
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.right = node_count;
            } else {
                insert_internal(tree, parent_node.right, node);
            }
        }
    }

    public fun insert<V: store + drop>(tree: &mut SplayTree<V>, node: Node<V>) {
        if (option::is_none(&tree.root)) {
            vector::push_back(&mut tree.nodes, node);
            set_root(tree, 0);
        } else {
            let root = get_root(tree);
            assert!(option::is_some(&root), ENO_MESSAGE);
            insert_internal(tree, *option::borrow(&root), node);
        }
    }
    
    fun insert_child_and_splay_once<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, node: Node<V>) {
        let parent_node = vector::borrow(&tree.nodes, parent_idx);
        let node_count = vector::length(&tree.nodes);

        if (node.key < parent_node.key) {
            if (parent_node.left == NULL_PTR) {
                vector::push_back(&mut tree.nodes, node);
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.left = node_count;
                // one splay step
                rotate_right(tree, parent_idx, node_count);
            } else {
                insert_internal(tree, parent_node.left, node);
            }
        } else if (node.key > parent_node.key) {
            if (parent_node.right == NULL_PTR) {
                vector::push_back(&mut tree.nodes, node);
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.right = node_count;
                // one splay step
                rotate_left(tree, parent_idx, node_count);
            } else {
                insert_internal(tree, parent_node.right, node);
            }
        }
    }
    
    public fun insert_and_splay_once<V: store + drop>(tree: &mut SplayTree<V>, node: Node<V>) {
        if (option::is_none(&tree.root)) {
            vector::push_back(&mut tree.nodes, node);
            set_root(tree, 0);
        } else {
            let root = get_root(tree);
            assert!(option::is_some(&root), ENO_MESSAGE);
            insert_child_and_splay_once(tree, *option::borrow(&root), node);
        }
    }

    fun rotate_left<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, child_idx: u64) {
        let child_left = get_left(tree, child_idx);
        set_right(tree, parent_idx, child_left);
        set_left(tree, child_idx, parent_idx);
        
        let root = get_root(tree);
        assert!(option::is_some(&root), ENO_MESSAGE);

        if (*option::borrow(&root) == parent_idx) {
            set_root(tree, child_idx);
        }
    }

    fun rotate_right<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, child_idx: u64) {
        let child_right = get_right(tree, child_idx);
        set_left(tree, parent_idx, child_right);
        set_right(tree, child_idx, parent_idx);
        
        let root = get_root(tree);
        assert!(option::is_some(&root), ENO_MESSAGE);

        if (*option::borrow(&root) == parent_idx) {
            set_root(tree, child_idx);
        }
    }

    #[test]
    fun test_init_tree() {
        let tree = init_tree<u64>();

        assert!(option::is_none(&tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_init_node() {
        let node = init_node<u64>(0, 0);

        assert!(node.key == 0, ENO_MESSAGE);
        assert!(node.value == 0, ENO_MESSAGE);
        assert!(node.left == NULL_PTR, ENO_MESSAGE);
        assert!(node.right == NULL_PTR, ENO_MESSAGE);
    }

    #[test]
    fun test_add_node() {
        let tree = init_tree<u64>();
        let node = init_node<u64>(0, 0);

        assert!(option::is_none(&tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 0, ENO_MESSAGE);

        insert(&mut tree, node);

        assert!(option::is_some(&tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 1, ENO_MESSAGE);
    }

    // #[test]
    // fun test_add_two_nodes() {
    //     let tree = init_tree<u64>();

    //     let key0: u64 = 0;
    //     let key1: u64 = 1;

    //     let node0 = init_node<u64>(key0, 0);
    //     let node1 = init_node<u64>(key1, 1);

    //     insert(&mut tree, node0);
    //     insert(&mut tree, node1);

    //     assert!(tree.root == key0, ENO_MESSAGE);
    //     assert!(vector::length(&tree.nodes) == 2, ENO_MESSAGE);

    //     let maybe_root = get_root(&tree);
    //     let maybe_root_node = get_root_node(&tree);
    //     assert!(option::is_some(&maybe_root), ENO_MESSAGE);
    //     assert!(option::is_some(&maybe_root_node), ENO_MESSAGE);

    //     let root = *option::borrow(&maybe_root);
    //     let root_node = *option::borrow(&maybe_root_node);

    //     assert!(root_node.key == key0, ENO_MESSAGE);
    //     assert!(get_left(&tree, root) == NULL_PTR, ENO_MESSAGE);
    //     assert!(get_right(&tree, root) == key1, ENO_MESSAGE);
    // }

    // #[test]
    // fun test_get_by_key() {
    //     let tree = init_tree<u64>();

    //     let node0 = init_node<u64>(0, 0);
    //     let node1 = init_node<u64>(1, 1);
    //     let node2 = init_node<u64>(2, 2);
    //     let node3 = init_node<u64>(3, 3);

    //     insert(&mut tree, node1);
    //     insert(&mut tree, node0);
    //     insert(&mut tree, node3);
    //     insert(&mut tree, node2);

    //     assert!(get_node_by_key(&tree, 0).value == 0, ENO_MESSAGE);
    //     assert!(get_node_by_key(&tree, 1).value == 1, ENO_MESSAGE);
    //     assert!(get_node_by_key(&tree, 2).value == 2, ENO_MESSAGE);
    //     assert!(get_node_by_key(&tree, 3).value == 3, ENO_MESSAGE);
    // }

    // #[test]
    // fun test_left_rotate() {
    //     let tree = init_tree<u64>();

    //     let node0 = init_node<u64>(0, 0);
    //     let node1 = init_node<u64>(1, 1);
    //     let node2 = init_node<u64>(2, 2);
    //     let node3 = init_node<u64>(3, 3);
    //     let node4 = init_node<u64>(4, 4);

    //     insert(&mut tree, node1);
    //     insert(&mut tree, node0);
    //     insert(&mut tree, node3);
    //     insert(&mut tree, node2);
    //     insert(&mut tree, node4);

    //     // tree should initially look like
    //     //    1
    //     //   / \
    //     //  0   3
    //     //     / \
    //     //    2   4

    //     let maybe_root = get_root(&tree);
    //     let maybe_root_node = get_root_node(&tree);
    //     assert!(option::is_some(&maybe_root), ENO_MESSAGE);
    //     assert!(option::is_some(&maybe_root_node), ENO_MESSAGE);

    //     let root = *option::borrow(&maybe_root);
    //     let root_node = option::borrow(&maybe_root_node);
    //     let root_right_node = get_node_by_index(&tree, root_node.right);

    //     assert!(root_node.key == 1, ENO_MESSAGE);
    //     assert!(root_right_node.key == 3, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_node.left).key == 0, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_right_node.left).key == 2, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_right_node.right).key == 4, ENO_MESSAGE);

    //     rotate_left(&mut tree, root, root_node.right);

    //     // tree should now look like
    //     //      3
    //     //     / \
    //     //    1   4
    //     //   / \
    //     //  0   2

    //     let maybe_root_node = get_root_node(&tree);
    //     assert!(option::is_some(&maybe_root_node), ENO_MESSAGE);

    //     let root_node = *option::borrow(&maybe_root_node);
    //     let root_left_node = get_node_by_index(&tree, root_node.left);

    //     assert!(root_node.key == 3, ENO_MESSAGE);
    //     assert!(root_left_node.key == 1, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_node.right).key == 4, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_left_node.left).key == 0, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_left_node.right).key == 2, ENO_MESSAGE);
    // }

    // #[test]
    // fun test_right_rotate() {
    //     let tree = init_tree<u64>();

    //     let node0 = init_node<u64>(0, 0);
    //     let node1 = init_node<u64>(1, 1);
    //     let node2 = init_node<u64>(2, 2);
    //     let node3 = init_node<u64>(3, 3);
    //     let node4 = init_node<u64>(4, 4);

    //     insert(&mut tree, node3);
    //     insert(&mut tree, node1);
    //     insert(&mut tree, node0);
    //     insert(&mut tree, node2);
    //     insert(&mut tree, node4);

    //     // tree should initially look like
    //     //      3
    //     //     / \
    //     //    1   4
    //     //   / \
    //     //  0   2

    //     let maybe_root = get_root(&tree);
    //     let maybe_root_node = get_root_node(&tree);
    //     assert!(option::is_some(&maybe_root), ENO_MESSAGE);
    //     assert!(option::is_some(&maybe_root_node), ENO_MESSAGE);

    //     let root = *option::borrow(&maybe_root);
    //     let root_node = option::borrow(&maybe_root_node);
    //     let root_left_node = get_node_by_index(&tree, root_node.left);

    //     assert!(root_node.key == 3, ENO_MESSAGE);
    //     assert!(root_left_node.key == 1, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_node.right).key == 4, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_left_node.left).key == 0, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_left_node.right).key == 2, ENO_MESSAGE);

    //     let root_idx = get_root(&tree);
    //     rotate_right(&mut tree, root, root_node.left);

    //     // tree should now look like
    //     //    1
    //     //   / \
    //     //  0   3
    //     //     / \
    //     //    2   4

    //     let maybe_root_node = get_root_node(&tree);
    //     assert!(option::is_some(&maybe_root_node), ENO_MESSAGE);

    //     let root_node = option::borrow(&maybe_root_node);
    //     let root_right_node = get_node_by_index(&tree, root_node.right);

    //     assert!(root_node.key == 1, ENO_MESSAGE);
    //     assert!(root_right_node.key == 3, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_node.left).key == 0, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_right_node.left).key == 2, ENO_MESSAGE);
    //     assert!(get_node_by_index(&tree, root_right_node.right).key == 4, ENO_MESSAGE);
    // }
}
