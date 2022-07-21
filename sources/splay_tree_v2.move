module flow::splay_tree_v2 {
    use std::option;
    use std::vector;

    const ENO_MESSAGE: u64 = 0;

    struct Node<V: drop> has store, drop {
        key: u64,
        value: V,
        parent: option::Option<u64>,
        left: option::Option<u64>,
        right: option::Option<u64>
    }

    struct SplayTree<V: drop> has store, drop {
        nodes: vector<Node<V>>,
    }

    public fun init_tree<V: store + drop>(): SplayTree<V> {
        SplayTree {
            nodes: vector::empty<Node<V>>(),
        }
    }

    fun init_node<V: store + drop>(key: u64, value: V, parent: option::Option<u64>): Node<V> {
        Node {
            key,
            value,
            parent,
            left: option::none(),
            right: option::none()
        }
    }

    fun insert_child<V: store + drop>(nodes: &mut vector<Node<V>>, child: Node<V>, parent_idx: u64) {
        let parent = vector::borrow(nodes, parent_idx);
        let node_count = vector::length(nodes);
        if (child.key < parent.key) {
            if (option::is_none(&parent.left)) {
                child.parent = option::some(parent_idx);
                vector::push_back(nodes, child);
                let parent = vector::borrow_mut(nodes, parent_idx);
                parent.left = option::some(node_count);
                // TODO splay here
            } else {
                insert_child(nodes, child, *option::borrow(&parent.left))
            }
        } else if (child.key > parent.key) {
            if (option::is_none(&parent.right)) {
                child.parent = option::some(parent_idx);
                vector::push_back(nodes, child);
                let parent = vector::borrow_mut(nodes, parent_idx);
                parent.right = option::some(node_count);
                // TODO splay here
            } else {
                insert_child(nodes, child, *option::borrow(&parent.right))
            }
        }
    }

    public fun insert<V: store + drop>(tree: &mut SplayTree<V>, key: u64, value: V) {
        let node = init_node(key, value, option::none());
        if (vector::is_empty(&tree.nodes)) {
            vector::push_back(&mut tree.nodes, node)
        } else {
            insert_child(&mut tree.nodes, node, 0)
        }
    }

    fun contains_key_internal<V: store + drop>(nodes: &vector<Node<V>>, current: &Node<V>, key: u64): bool {
        if (current.key == key) {
            // TODO splay here
            true
        } else if (key < current.key && option::is_some(&current.left)) {
            let left_node = vector::borrow(nodes, *option::borrow(&current.left));
            contains_key_internal(nodes, left_node, key)
        } else if (key > current.key && option::is_some(&current.right)) {
            let right_node = vector::borrow(nodes, *option::borrow(&current.right));
            contains_key_internal(nodes, right_node, key)
        } else {
            false
        }
    }

    public fun contains_key<V: store + drop>(tree: &SplayTree<V>, key: u64): bool {
        if (vector::length(&tree.nodes) == 0) {
            true
        } else {
            contains_key_internal(&tree.nodes, vector::borrow(&tree.nodes, 0), key)
        }
    }

    fun get_internal<V: store + drop>(nodes: &vector<Node<V>>, current: &Node<V>, key: u64): &Node<V> {
        if (current.key == key) {
            // TODO splay here
            current
        } else if (key < current.key && option::is_some(&current.left)) {
            let left_node = vector::borrow(nodes, *option::borrow(&current.left));
            get_internal(nodes, left_node, key)
        } else if (key > current.key && option::is_some(&current.right)) {
            let right_node = vector::borrow(nodes, *option::borrow(&current.right));
            get_internal(nodes, right_node, key)
        } else {
            abort(ENO_MESSAGE)
        }
    }

    public fun get<V: store + drop>(tree: &SplayTree<V>, key: u64): &Node<V> {
        assert!(vector::length(&tree.nodes) > 0, ENO_MESSAGE);
        get_internal(&tree.nodes, vector::borrow(&tree.nodes, 0), key)
    }

    #[test]
    fun test_init_tree() {
        let tree = init_tree<u64>();
        assert!(vector::length(&tree.nodes) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_init_node() {
        let node = init_node<u64>(0, 0, option::none());
        assert!(node.key == 0, ENO_MESSAGE);
        assert!(node.value == 0, ENO_MESSAGE);
        assert!(option::is_none(&node.left), ENO_MESSAGE);
        assert!(option::is_none(&node.right), ENO_MESSAGE);
    }

    #[test]
    fun test_insert_one() {
        let tree = init_tree<u64>();
        insert(&mut tree, 5, 1);
        assert!(vector::length(&tree.nodes) == 1, ENO_MESSAGE);
        assert!(vector::borrow(&tree.nodes, 0).key == 5, ENO_MESSAGE);
        assert!(vector::borrow(&tree.nodes, 0).value == 1, ENO_MESSAGE);
        assert!(option::is_none(&vector::borrow(&tree.nodes, 0).parent) , ENO_MESSAGE);
        assert!(option::is_none(&vector::borrow(&tree.nodes, 0).left) , ENO_MESSAGE);
        assert!(option::is_none(&vector::borrow(&tree.nodes, 0).right) , ENO_MESSAGE);
    }

    #[test]
    fun test_insert_two() {
        let tree = init_tree<u64>();
        insert(&mut tree, 5, 1);
        insert(&mut tree, 3, 1);

        let first = vector::borrow(&tree.nodes, 0);
        let second = vector::borrow(&tree.nodes, 1);

        assert!(vector::length(&tree.nodes) == 2, ENO_MESSAGE);
        assert!(first.key == 5, ENO_MESSAGE);
        assert!(first.value == 1, ENO_MESSAGE);
        assert!(option::is_some(&first.left), ENO_MESSAGE);
        assert!(option::is_none(&first.right), ENO_MESSAGE);
        assert!(*option::borrow(&first.left) == 1, ENO_MESSAGE);

        assert!(second.key == 3, ENO_MESSAGE);
        assert!(second.value == 1, ENO_MESSAGE);
        assert!(option::is_none(&second.left), ENO_MESSAGE);
        assert!(option::is_none(&second.right), ENO_MESSAGE);
        assert!(option::is_some(&second.parent), ENO_MESSAGE);
        assert!(*option::borrow(&second.parent) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_insert_four() {
        let tree = init_tree<u64>();
        insert(&mut tree, 5, 1);
        insert(&mut tree, 3, 2);
        insert(&mut tree, 4, 3);
        insert(&mut tree, 6, 4);

        let first = vector::borrow(&tree.nodes, 0);
        let second = vector::borrow(&tree.nodes, 1);
        let third = vector::borrow(&tree.nodes, 2);
        let fourth = vector::borrow(&tree.nodes, 3);

        assert!(vector::length(&tree.nodes) == 4, ENO_MESSAGE);
        assert!(first.key == 5, ENO_MESSAGE);
        assert!(first.value == 1, ENO_MESSAGE);
        assert!(option::is_some(&first.left), ENO_MESSAGE);
        assert!(option::is_some(&first.right), ENO_MESSAGE);
        assert!(*option::borrow(&first.right) == 3, ENO_MESSAGE);

        assert!(second.key == 3, ENO_MESSAGE);
        assert!(second.value == 2, ENO_MESSAGE);
        assert!(option::is_none(&second.left), ENO_MESSAGE);
        assert!(option::is_some(&second.right), ENO_MESSAGE);
        assert!(option::is_some(&second.parent), ENO_MESSAGE);
        assert!(*option::borrow(&second.parent) == 0, ENO_MESSAGE);

        assert!(third.key == 4, ENO_MESSAGE);
        assert!(third.value == 3, ENO_MESSAGE);
        assert!(option::is_none(&third.left), ENO_MESSAGE);
        assert!(option::is_none(&third.right), ENO_MESSAGE);
        assert!(option::is_some(&third.parent), ENO_MESSAGE);
        assert!(*option::borrow(&third.parent) == 1, ENO_MESSAGE);

        assert!(fourth.key == 6, ENO_MESSAGE);
        assert!(fourth.value == 4, ENO_MESSAGE);
        assert!(option::is_none(&fourth.left), ENO_MESSAGE);
        assert!(option::is_none(&fourth.right), ENO_MESSAGE);
        assert!(option::is_some(&fourth.parent), ENO_MESSAGE);
        assert!(*option::borrow(&fourth.parent) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_contains_key() {
        let tree = init_tree<u64>();
        insert(&mut tree, 5, 1);
        insert(&mut tree, 3, 2);
        assert!(contains_key(&tree, 5), ENO_MESSAGE);
        assert!(contains_key(&tree, 3), ENO_MESSAGE);
        assert!(!contains_key(&tree, 4), ENO_MESSAGE);
    }

    #[test]
    fun test_get() {
        let tree = init_tree<u64>();
        insert(&mut tree, 5, 1);
        insert(&mut tree, 3, 2);
        let five = get(&tree, 5);
        assert!(five.key == 5, ENO_MESSAGE);
        assert!(five.value == 1, ENO_MESSAGE);
        let three = get(&tree, 3);
        assert!(three.key == 3, ENO_MESSAGE);
        assert!(three.value == 2, ENO_MESSAGE);
    }
}