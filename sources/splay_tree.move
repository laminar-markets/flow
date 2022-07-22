module flow::splay_tree {
    use std::vector;
    use std::option::{Self, Option};
    #[test_only]
    use std::debug;

    const ENO_MESSAGE: u64 = 0;
    const EKEY_NOT_FOUND: u64 = 1;

    struct Node<V: store + drop> has store, drop {
        key: u64,
        value: V,
        left: Option<u64>,
        right: Option<u64>
    }

    struct SplayTree<V: store + drop> has store, drop {
        root: Option<u64>,
        nodes: vector<Node<V>>,
        splay: bool
    }

    public fun init_tree<V: store + drop>(splay: bool): SplayTree<V> {
        SplayTree {
            root: option::none(),
            nodes: vector::empty<Node<V>>(),
            splay
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

    fun get_left<V: store + drop>(tree: &SplayTree<V>, idx: u64): &Option<u64> {
        &vector::borrow(&tree.nodes, idx).left
    }

    fun get_right<V: store + drop>(tree: &SplayTree<V>, idx: u64): &Option<u64> {
        &vector::borrow(&tree.nodes, idx).right
    }

    fun set_left<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, update_to: Option<u64>) {
        vector::borrow_mut(&mut tree.nodes, idx).left = update_to;
    }

    fun set_right<V: store + drop>(tree: &mut SplayTree<V>, idx: u64, update_to: Option<u64>) {
        vector::borrow_mut(&mut tree.nodes, idx).right = update_to;
    }

    fun get_root<V: store + drop>(tree: &SplayTree<V>): &Option<u64> {
        &tree.root
    }

    fun set_root<V: store + drop>(tree: &mut SplayTree<V>, update_to: u64) {
        tree.root = option::some(update_to);
    }

    fun get_node_by_index<V: store + drop>(tree: &SplayTree<V>, idx: u64): &Node<V> {
        vector::borrow(&tree.nodes, idx)
    }

    fun contains_internal<V: store + drop>(tree: &mut SplayTree<V>, grandparent_idx: Option<u64>, parent_idx: u64, key: u64): bool {
        let parent_node = vector::borrow(&tree.nodes, parent_idx);
        if (key == parent_node.key) {
            if (option::is_none(&grandparent_idx)) {
                return true
            };

            let grandparent_idx = *option::borrow(&grandparent_idx);
            let grandparent_node = vector::borrow(&tree.nodes, grandparent_idx);
            if (option::is_some(&grandparent_node.left) && *option::borrow(&grandparent_node.left) == parent_idx) {
                splay_right(tree, grandparent_idx, parent_idx);
            } else if (option::is_some(&grandparent_node.right) && *option::borrow(&grandparent_node.right) == parent_idx) {
                splay_left(tree, grandparent_idx, parent_idx);
            };

            true
        } else if (key < parent_node.key && option::is_some(&parent_node.left)) {
            contains_internal(tree, option::some(parent_idx), *option::borrow(&parent_node.left), key)
        } else if (key > parent_node.key && option::is_some(&parent_node.right)) {
            contains_internal(tree, option::some(parent_idx), *option::borrow(&parent_node.right), key)
        } else {
            false
        }
    }

    public fun contains<V: store + drop>(tree: &mut SplayTree<V>, key: u64): bool {
        let root = get_root(tree);
        if (option::is_none(root)) {
            false
        } else {
            contains_internal(tree, option::none(), *option::borrow(root), key)
        }
    }

    fun get_internal<V: store + drop>(tree: &mut SplayTree<V>, grandparent_idx: Option<u64>, parent_idx: u64, key: u64): &Node<V> {
        let parent_node = vector::borrow(&tree.nodes, parent_idx);
        if (key == parent_node.key) {
            if (option::is_none(&grandparent_idx)) {
                return parent_node
            };

            let grandparent_idx = *option::borrow(&grandparent_idx);
            let grandparent_node = vector::borrow(&tree.nodes, grandparent_idx);
            if (option::is_some(&grandparent_node.left) && *option::borrow(&grandparent_node.left) == parent_idx) {
                splay_right(tree, grandparent_idx, parent_idx);
            } else if (option::is_some(&grandparent_node.right) && *option::borrow(&grandparent_node.right) == parent_idx) {
                splay_left(tree, grandparent_idx, parent_idx);
            };

            let parent_node = vector::borrow(&tree.nodes, parent_idx);
            parent_node
        } else if (key < parent_node.key) {
            assert!(option::is_some(&parent_node.left), EKEY_NOT_FOUND);
            get_internal(tree, option::some(parent_idx), *option::borrow(&parent_node.left), key)
        } else {
            assert!(option::is_some(&parent_node.right), EKEY_NOT_FOUND);
            get_internal(tree, option::some(parent_idx), *option::borrow(&parent_node.right), key)
        }
    }

    public fun get<V: store + drop>(tree: &mut SplayTree<V>, key: u64): &Node<V> {
        let root = get_root(tree);
        assert!(option::is_some(root), ENO_MESSAGE);
        get_internal(tree, option::none(), *option::borrow(root), key)
    }

    fun insert_internal<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, node: Node<V>) {
        let parent_node = vector::borrow(&tree.nodes, parent_idx);
        let node_count = vector::length(&tree.nodes);

        if (node.key < parent_node.key) {
            if (option::is_none(&parent_node.left)) {
                vector::push_back(&mut tree.nodes, node);
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.left = option::some(node_count);
                splay_right(tree, parent_idx, node_count);
            } else {
                insert_internal(tree, *option::borrow(&parent_node.left), node);
            }
        } else if (node.key > parent_node.key) {
            if (option::is_none(&parent_node.right)) {
                vector::push_back(&mut tree.nodes, node);
                let parent_node = vector::borrow_mut(&mut tree.nodes, parent_idx);
                parent_node.right = option::some(node_count);
                splay_left(tree, parent_idx, node_count);
            } else {
                insert_internal(tree, *option::borrow(&parent_node.right), node);
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
            assert!(option::is_some(root), ENO_MESSAGE);
            insert_internal(tree, *option::borrow(root), node);
        }
    }

    fun rotate_left<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, child_idx: u64) {
        let child_left = get_left(tree, child_idx);
        set_right(tree, parent_idx, *child_left);
        set_left(tree, child_idx, option::some(parent_idx));

        let root = get_root(tree);
        assert!(option::is_some(root), ENO_MESSAGE);

        if (*option::borrow(root) == parent_idx) {
            set_root(tree, child_idx);
        }
    }

    fun splay_left<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, child_idx: u64) {
        if (tree.splay) {
            rotate_left(tree, parent_idx, child_idx)
        }
    }

    fun rotate_right<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, child_idx: u64) {
        let child_right = get_right(tree, child_idx);
        set_left(tree, parent_idx, *child_right);
        set_right(tree, child_idx, option::some(parent_idx));
        
        let root = get_root(tree);
        assert!(option::is_some(root), ENO_MESSAGE);

        if (*option::borrow(root) == parent_idx) {
            set_root(tree, child_idx);
        }
    }

    fun splay_right<V: store + drop>(tree: &mut SplayTree<V>, parent_idx: u64, child_idx: u64) {
        if (tree.splay) {
            rotate_right(tree, parent_idx, child_idx)
        }
    }

    fun inorder_traversal_internal<V: store + drop>(tree: &SplayTree<V>, idx: &Option<u64>, indices: &mut vector<u64>) {
        if (option::is_none(idx)) {
            return
        };

        let node = vector::borrow(&tree.nodes, *option::borrow(idx));
        inorder_traversal_internal(tree, &node.left, indices);
        vector::push_back(indices, *option::borrow(idx));
        inorder_traversal_internal(tree, &node.right, indices);
    }

    public fun inorder_traversal<V: store + drop>(tree: &SplayTree<V>): vector<u64> {
        let indices = vector::empty<u64>();
        inorder_traversal_internal(tree, &tree.root, &mut indices);
        indices
    }

    fun minimum_internal<V: store + drop>(tree: &SplayTree<V>, current: &Option<u64>): &Node<V> {
        let node = vector::borrow(&tree.nodes, *option::borrow(current));
        if (option::is_none(&node.left)) {
            node
        } else {
            minimum_internal(tree, &node.left)
        }
    }

    public fun minimum<V: store + drop>(tree: &SplayTree<V>): &Node<V> {
        assert!(option::is_some(&tree.root), ENO_MESSAGE);
        minimum_internal(tree, &tree.root)
    }

    #[test]
    fun test_init_tree() {
        let tree = init_tree<u64>(false);

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
        let tree = init_tree<u64>(false);

        assert!(option::is_none(&tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 0, ENO_MESSAGE);

        insert(&mut tree, 0, 0);

        assert!(option::is_some(&tree.root), ENO_MESSAGE);
        assert!(vector::length(&tree.nodes) == 1, ENO_MESSAGE);
    }

     #[test]
     fun test_add_two_nodes() {
         let tree = init_tree<u64>(false);

         let key0: u64 = 0;
         let key1: u64 = 1;

         insert(&mut tree, key0, 0);
         insert(&mut tree, key1, 1);

         let maybe_root = get_root(&tree);
         assert!(option::is_some(maybe_root), ENO_MESSAGE);

         let root = *option::borrow(maybe_root);
         let root_node = vector::borrow(&tree.nodes, root);

         assert!(vector::length(&tree.nodes) == 2, ENO_MESSAGE);
         assert!(root_node.key == key0, ENO_MESSAGE);
         assert!(option::is_none(get_left(&tree, root)), ENO_MESSAGE);
         assert!(*option::borrow(get_right(&tree, root)) == key1, ENO_MESSAGE);
     }

    #[test]
    fun test_add_two_nodes_splay() {
        let tree = init_tree<u64>(true);

        let key0: u64 = 0;
        let key1: u64 = 1;

        insert(&mut tree, key0, 0);
        insert(&mut tree, key1, 1);

        let maybe_root = get_root(&tree);
        assert!(option::is_some(maybe_root), ENO_MESSAGE);

        let root = *option::borrow(maybe_root);
        let root_node = vector::borrow(&tree.nodes, root);

        assert!(vector::length(&tree.nodes) == 2, ENO_MESSAGE);
        assert!(root_node.key == key1, ENO_MESSAGE);
        assert!(*option::borrow(get_left(&tree, root)) == key0, ENO_MESSAGE);
        assert!(option::is_none(get_right(&tree, root)), ENO_MESSAGE);
    }

    #[test]
    fun test_contains() {
        let tree = init_tree<u64>(false);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);

        assert!(contains(&mut tree, 0), ENO_MESSAGE);
        assert!(contains(&mut tree, 1), ENO_MESSAGE);
        assert!(contains(&mut tree, 2), ENO_MESSAGE);
        assert!(contains(&mut tree, 3), ENO_MESSAGE);
        assert!(!contains(&mut tree, 4), ENO_MESSAGE);
    }

    #[test]
    fun test_get() {
         let tree = init_tree<u64>(false);

         insert(&mut tree, 0, 0);
         insert(&mut tree, 1, 1);
         insert(&mut tree, 2, 2);
         insert(&mut tree, 3, 3);

         assert!(get(&mut tree, 0).value == 0, ENO_MESSAGE);
         assert!(get(&mut tree, 1).value == 1, ENO_MESSAGE);
         assert!(get(&mut tree, 2).value == 2, ENO_MESSAGE);
         assert!(get(&mut tree, 3).value == 3, ENO_MESSAGE);
     }

     #[test]
     fun test_left_rotate() {
         let tree = init_tree<u64>(false);

         insert(&mut tree, 1, 1);
         insert(&mut tree, 0, 0);
         insert(&mut tree, 3, 3);
         insert(&mut tree, 2, 2);
         insert(&mut tree, 4, 4);

         // tree should initially look like
         //    1
         //   / \
         //  0   3
         //     / \
         //    2   4

         let maybe_root = get_root(&tree);
         assert!(option::is_some(maybe_root), ENO_MESSAGE);

         let root = *option::borrow(maybe_root);
         let root_node = vector::borrow(&tree.nodes, root);

         let maybe_right = root_node.right;
         assert!(option::is_some(&maybe_right), ENO_MESSAGE);

         let right = *option::borrow(&maybe_right);
         let root_right_node = get_node_by_index(&tree, right);

         assert!(option::is_some(&root_node.left), ENO_MESSAGE);
         assert!(option::is_some(&root_right_node.left), ENO_MESSAGE);
         assert!(option::is_some(&root_right_node.right), ENO_MESSAGE);

         assert!(root_node.key == 1, ENO_MESSAGE);
         assert!(root_right_node.key == 3, ENO_MESSAGE);
         assert!(get_node_by_index(&tree, *option::borrow(&root_node.left)).key == 0, ENO_MESSAGE);
         assert!(get_node_by_index(&tree, *option::borrow(&root_right_node.left)).key == 2, ENO_MESSAGE);
         assert!(get_node_by_index(&tree, *option::borrow(&root_right_node.right)).key == 4, ENO_MESSAGE);

         rotate_left(&mut tree, root, *option::borrow(&root_node.right));

         // tree should now look like
         //      3
         //     / \
         //    1   4
         //   / \
         //  0   2

         let maybe_root = get_root(&tree);
         assert!(option::is_some(maybe_root), ENO_MESSAGE);

         let root = *option::borrow(maybe_root);
         let root_node = vector::borrow(&tree.nodes, root);

         assert!(option::is_some(&root_node.left), ENO_MESSAGE);
         let root_left_node = get_node_by_index(&tree, *option::borrow(&root_node.left));

         assert!(option::is_some(&root_left_node.left), ENO_MESSAGE);
         assert!(option::is_some(&root_left_node.right), ENO_MESSAGE);

         assert!(root_node.key == 3, ENO_MESSAGE);
         assert!(root_left_node.key == 1, ENO_MESSAGE);
         assert!(get_node_by_index(&tree, *option::borrow(&root_node.right)).key == 4, ENO_MESSAGE);
         assert!(get_node_by_index(&tree, *option::borrow(&root_left_node.left)).key == 0, ENO_MESSAGE);
         assert!(get_node_by_index(&tree, *option::borrow(&root_left_node.right)).key == 2, ENO_MESSAGE);
     }

     #[test]
     fun test_right_rotate() {
         let tree = init_tree<u64>(false);

         insert(&mut tree, 3, 3);
         insert(&mut tree, 1, 1);
         insert(&mut tree, 4, 4);
         insert(&mut tree, 0, 0);
         insert(&mut tree, 2, 2);

         // tree should initially look like
         //      3
         //     / \
         //    1   4
         //   / \
         //  0   2

         let maybe_root = get_root(&tree);
         assert!(option::is_some(maybe_root), ENO_MESSAGE);

         let root = *option::borrow(maybe_root);
         let root_node = vector::borrow(&tree.nodes, root);

         let maybe_left = root_node.left;
         assert!(option::is_some(&maybe_left), ENO_MESSAGE);

         let left = *option::borrow(&maybe_left);
         let root_left_node = get_node_by_index(&tree, left);

         assert!(root_node.key == 3, ENO_MESSAGE);
         assert!(root_left_node.key == 1, ENO_MESSAGE);
         assert!(get_node_by_index(&tree, *option::borrow(&root_node.left)).key == 1, ENO_MESSAGE);
         assert!(get_node_by_index(&tree, *option::borrow(&root_left_node.left)).key == 0, ENO_MESSAGE);
         assert!(get_node_by_index(&tree, *option::borrow(&root_left_node.right)).key == 2, ENO_MESSAGE);

         rotate_right(&mut tree, root, *option::borrow(&root_node.left));

         // tree should now look like
         //    1
         //   / \
         //  0   3
         //     / \
         //    2   4

         let maybe_root = get_root(&tree);
         assert!(option::is_some(maybe_root), ENO_MESSAGE);

         let root = *option::borrow(maybe_root);
         let root_node = vector::borrow(&tree.nodes, root);

         assert!(option::is_some(&root_node.left), ENO_MESSAGE);
         let root_right_node = get_node_by_index(&tree, *option::borrow(&root_node.right));

         assert!(root_node.key == 1, ENO_MESSAGE);
         assert!(root_right_node.key == 3, ENO_MESSAGE);
         assert!(get_node_by_index(&tree,*option::borrow(&root_node.left)).key == 0, ENO_MESSAGE);
         assert!(get_node_by_index(&tree,*option::borrow(&root_right_node.left)).key == 2, ENO_MESSAGE);
         assert!(get_node_by_index(&tree,*option::borrow(&root_right_node.right)).key == 4, ENO_MESSAGE);
     }

    #[test]
    fun test_inorder_traversal_no_splay() {
        let tree = init_tree<u64>(false);

        insert(&mut tree, 0, 0);
        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);

        let indices = inorder_traversal(&tree);
        assert!(*vector::borrow(&indices, 0) == 0, ENO_MESSAGE);
        assert!(*vector::borrow(&indices, 1) == 1, ENO_MESSAGE);
        assert!(*vector::borrow(&indices, 2) == 2, ENO_MESSAGE);
        assert!(*vector::borrow(&indices, 3) == 3, ENO_MESSAGE);
        assert!(*vector::borrow(&indices, 4) == 4, ENO_MESSAGE);
    }

    #[test]
    fun test_inorder_traversal_splay() {
        let tree = init_tree<u64>(false);

        insert(&mut tree, 1, 1);
        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 0, 0);
        insert(&mut tree, 5, 5);

        let indices = inorder_traversal(&tree);
        debug::print(&indices);
//        assert!(*vector::borrow(&indices, 0) == 0, ENO_MESSAGE);
//        assert!(*vector::borrow(&indices, 1) == 1, ENO_MESSAGE);
//        assert!(*vector::borrow(&indices, 2) == 2, ENO_MESSAGE);
//        assert!(*vector::borrow(&indices, 3) == 3, ENO_MESSAGE);
//        assert!(*vector::borrow(&indices, 4) == 4, ENO_MESSAGE);
    }

    #[test]
    fun test_minimum_without_splay() {
        let tree = init_tree<u64>(false);

        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 1, 1);

        let min = minimum(&tree);
//        debug::print(&tree.root);
//        debug::print(&tree.nodes);
//        debug::print(&min.key);
        assert!(min.key == 1, ENO_MESSAGE);
    }

    #[test]
    fun test_minimum_with_splay() {
        let tree = init_tree<u64>(true);

        insert(&mut tree, 2, 2);
        insert(&mut tree, 3, 3);
        insert(&mut tree, 4, 4);
        insert(&mut tree, 5, 5);
        insert(&mut tree, 1, 1);

        let min = minimum(&tree);
        debug::print(&tree.root);
        debug::print(&tree.nodes);
        debug::print(&min.key);
//      assert!(min.key == 1, ENO_MESSAGE);
    }
}
