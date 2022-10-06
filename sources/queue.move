module flow::queue {
    use std::vector;
    use std::option::{Self, Option};
    use flow::guarded_idx::{Self, GuardedIdx};
    #[test_only]
    use aptos_std::debug;

    // *************************************************************************
    // * Constants
    // *************************************************************************

    const U64_MAX: u64 = 0xffffffffffffffff;

    // *************************************************************************
    // * Error codes                                                           *
    // *************************************************************************

    const ENO_MESSAGE: u64 = 0;
    // Queue is full
    const EQUEUE_FULL: u64 = 1;
    // Queue is malformed
    const EQUEUE_MALFORMED: u64 = 2;
    // Queue is empty
    const EQUEUE_EMPTY: u64 = 3;
    // Iterator is done
    const EITERATOR_DONE: u64 = 4;

    // *************************************************************************
    // * Structs                                                               *
    // *************************************************************************

    struct Node<V: store + drop> has store, drop {
        value: Option<V>,
        next: GuardedIdx
    }

    struct Queue<V: store + drop> has store, drop {
        head: GuardedIdx,
        tail: GuardedIdx,
        nodes: vector<Node<V>>,
        free_indices: vector<u64>
    }

    struct Iterator has drop {
        current: GuardedIdx
    }

    // *************************************************************************
    // * Public functions                                                      *
    // *************************************************************************

    public fun is_empty<V: store + drop>(queue: &Queue<V>): bool {
        size(queue) == 0
    }

    public fun is_full<V: store + drop>(queue: &Queue<V>): bool {
        size(queue) == U64_MAX
    }

    public fun size<V: store + drop>(queue: &Queue<V>): u64 {
        vector::length(&queue.nodes) - vector::length(&queue.free_indices)
    }

    public fun new<V: store + drop>(): Queue<V> {
        Queue {
            head: guarded_idx::sentinel(),
            tail: guarded_idx::sentinel(),
            nodes: vector::empty<Node<V>>(),
            free_indices: vector::empty<u64>()
        }
    }

    public fun clear<V: store + drop>(queue: &mut Queue<V>) {
        queue.head = guarded_idx::sentinel();
        queue.tail = guarded_idx::sentinel();
        queue.nodes = vector::empty<Node<V>>();
        queue.free_indices = vector::empty<u64>();
    }

    public fun init_iterator<V: store + drop>(): Iterator {
        Iterator {
            current: guarded_idx::sentinel()
        }
    }

    public fun has_next<V: store + drop>(queue: &Queue<V>, iter: &Iterator): bool {
        if (!is_empty(queue) && guarded_idx::is_sentinel(iter.current)) {
            true
        } else if (!guarded_idx::is_sentinel(iter.current)) {
            let current_node = vector::borrow(&queue.nodes, guarded_idx::unguard(iter.current));
            !guarded_idx::is_sentinel(current_node.next)
        } else {
            false
        }
    }

    public fun next_index<V: store + drop>(queue: &Queue<V>, iter: &mut Iterator): u64 {
        assert!(!is_empty(queue), EQUEUE_EMPTY);

        if (!is_empty(queue) && guarded_idx::is_sentinel(iter.current)) {
            iter.current = queue.head;
        } else {
            assert!(!guarded_idx::is_sentinel(iter.current), EITERATOR_DONE);
            let current_node = vector::borrow(&queue.nodes, guarded_idx::unguard(iter.current));
            iter.current = current_node.next;
        };

        guarded_idx::unguard(iter.current)
    }

    public fun get<V: store + drop>(queue: &Queue<V>, index: u64): &V {
        let n = vector::borrow(&queue.nodes, index);
        option::borrow(&n.value)
    }

    public fun get_mut<V: store + drop>(queue: &mut Queue<V>, index: u64): &mut V {
        let n = vector::borrow_mut(&mut queue.nodes, index);
        option::borrow_mut(&mut n.value)
    }

    public fun peek_iter_index<V: store + drop>(iter: &Iterator): Option<u64> {
        if (guarded_idx::is_sentinel(iter.current)) {
            option::none()
        } else {
            let current_index = guarded_idx::unguard(iter.current);
            option::some(current_index)
        }
    }

    fun create_node<V: store + drop>(value: V): Node<V> {
        Node<V> {
            value: option::some(value),
            next: guarded_idx::sentinel()
        }
    }

    public fun enqueue<V: store + drop>(queue: &mut Queue<V>, value: V) {
        assert!(!is_full(queue), EQUEUE_FULL);
        if (is_empty(queue)) {
            assert!(guarded_idx::is_sentinel(queue.head), EQUEUE_MALFORMED);
            assert!(guarded_idx::is_sentinel(queue.tail), EQUEUE_MALFORMED);
            queue.head = guarded_idx::guard(0);
            queue.tail = guarded_idx::guard(0);
            vector::push_back(&mut queue.nodes, create_node(value));
        } else {
            assert!(!guarded_idx::is_sentinel(queue.head), EQUEUE_MALFORMED);
            assert!(!guarded_idx::is_sentinel(queue.tail), EQUEUE_MALFORMED);
            let index = if (vector::length(&queue.free_indices) > 0) {
                vector::pop_back(&mut queue.free_indices)
            } else {
                vector::length(&queue.nodes)
            };

            let tail = guarded_idx::unguard(queue.tail);
            let tail_node = vector::borrow_mut(&mut queue.nodes, tail);
            tail_node.next = guarded_idx::guard(index);
            queue.tail = tail_node.next;

            if (index == vector::length(&queue.nodes)) {
                let next_node = create_node(value);
                vector::push_back(&mut queue.nodes, next_node);
            } else {
                let to_change = vector::borrow_mut(&mut queue.nodes, index);
                to_change.value = option::some(value)
            }
        }
    }

    public fun dequeue<V: store + drop>(queue: &mut Queue<V>): V {
        assert!(!guarded_idx::is_sentinel(queue.head), EQUEUE_EMPTY);
        let head = guarded_idx::unguard(queue.head);
        vector::push_back(&mut queue.free_indices, head);
        let head_node = vector::borrow_mut(&mut queue.nodes, head);
        queue.head = head_node.next;
        head_node.next = guarded_idx::sentinel();
        let result = option::extract(&mut head_node.value);
        if (guarded_idx::is_sentinel(queue.head)) {
            // clear queue if nothing left
            clear(queue);
        };
        result
    }

    public fun remove<V: store + drop>(queue: &mut Queue<V>, index_to_remove: u64, prev_index: Option<u64>) {
        vector::push_back(&mut queue.free_indices, index_to_remove);
        if (option::is_none(&prev_index)) {
            let node = vector::borrow(&mut queue.nodes, index_to_remove);
            queue.head = node.next;
        } else {
            let next = {
                let node = vector::borrow(&mut queue.nodes, index_to_remove);
                node.next
            };
            let prev_node = vector::borrow_mut(&mut queue.nodes, *option::borrow(&prev_index));
            prev_node.next = next;
        };

        let node = vector::borrow_mut(&mut queue.nodes, index_to_remove);
        node.next = guarded_idx::sentinel();
    }

    public fun peek<V: store + drop>(queue: &Queue<V>): &V {
        let head = guarded_idx::unguard(queue.head);
        let head_node = vector::borrow(&queue.nodes, head);
        option::borrow(&head_node.value)
    }

    public fun peek_mut<V: store + drop>(queue: &mut Queue<V>): &mut V {
        let head = guarded_idx::unguard(queue.head);
        let head_node = vector::borrow_mut(&mut queue.nodes, head);
        option::borrow_mut(&mut head_node.value)
    }

    // *************************************************************************
    // * Unit tests                                                            *
    // *************************************************************************

    #[test]
    fun test_new() {
        let queue = new<u64>();
        assert!(guarded_idx::is_sentinel(queue.head), ENO_MESSAGE);
        assert!(guarded_idx::is_sentinel(queue.tail), ENO_MESSAGE);
        assert!(vector::is_empty(&queue.nodes), ENO_MESSAGE);
        assert!(vector::is_empty(&queue.free_indices), ENO_MESSAGE);
    }

    #[test]
    fun test_enqueue_root() {
        let queue = new<u64>();
        enqueue(&mut queue, 1);
        assert!(!guarded_idx::is_sentinel(queue.head), ENO_MESSAGE);
        assert!(!guarded_idx::is_sentinel(queue.tail), ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 1, ENO_MESSAGE);
        assert!(vector::is_empty(&queue.free_indices), ENO_MESSAGE);
        assert!(!is_empty(&queue), ENO_MESSAGE);
        assert!(size(&queue) == 1, ENO_MESSAGE);
        let head = queue.head;
        let tail = queue.tail;
        assert!(guarded_idx::unguard(head) == guarded_idx::unguard(tail), ENO_MESSAGE);
        let node = vector::borrow(&queue.nodes, guarded_idx::unguard(head));
        assert!(guarded_idx::is_sentinel(node.next), ENO_MESSAGE);
        assert!(option::is_some(&node.value), ENO_MESSAGE);
        assert!(*option::borrow(&node.value) == 1, ENO_MESSAGE);
    }

    #[test]
    fun test_enqueue_tail() {
        let queue = new<u64>();
        enqueue(&mut queue, 1);
        enqueue(&mut queue, 2);
        assert!(!guarded_idx::is_sentinel(queue.head), ENO_MESSAGE);
        assert!(!guarded_idx::is_sentinel(queue.tail), ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 2, ENO_MESSAGE);
        assert!(vector::is_empty(&queue.free_indices), ENO_MESSAGE);
        assert!(size(&queue) == 2, ENO_MESSAGE);

        let head = queue.head;
        assert!(guarded_idx::unguard(head) == 0, ENO_MESSAGE);
        let head_node = vector::borrow(&queue.nodes, guarded_idx::unguard(head));

        let tail = queue.tail;
        assert!(guarded_idx::unguard(head_node.next) == guarded_idx::unguard(tail), ENO_MESSAGE);
        assert!(guarded_idx::unguard(tail) == 1, ENO_MESSAGE);
        let tail_node = vector::borrow(&queue.nodes, guarded_idx::unguard(tail));
        assert!(guarded_idx::is_sentinel(tail_node.next), ENO_MESSAGE);
        assert!(option::is_some(&tail_node.value), ENO_MESSAGE);
        assert!(*option::borrow(&tail_node.value) == 2, ENO_MESSAGE);
    }

    #[test]
    fun test_dequeue_queue_of_size_one() {
        let queue = new<u64>();
        enqueue(&mut queue, 1);
        let value = dequeue(&mut queue);
        assert!(value == 1, ENO_MESSAGE);
        assert!(size(&queue) == 0, ENO_MESSAGE);
        assert!(is_empty(&queue), ENO_MESSAGE);
        assert!(guarded_idx::is_sentinel(queue.head), ENO_MESSAGE);
        assert!(guarded_idx::is_sentinel(queue.tail), ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 0, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_dequeue_queue_of_size_two() {
        let queue = new<u64>();
        enqueue(&mut queue, 1);
        enqueue(&mut queue, 2);

        let value = dequeue(&mut queue);
        assert!(value == 1, ENO_MESSAGE);
        assert!(size(&queue) == 1, ENO_MESSAGE);
        assert!(!is_empty(&queue), ENO_MESSAGE);
        assert!(!guarded_idx::is_sentinel(queue.head), ENO_MESSAGE);
        assert!(!guarded_idx::is_sentinel(queue.tail), ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 1, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 2, ENO_MESSAGE);

        let value = dequeue(&mut queue);
        assert!(value == 2, ENO_MESSAGE);
        assert!(size(&queue) == 0, ENO_MESSAGE);
        assert!(is_empty(&queue), ENO_MESSAGE);
        assert!(guarded_idx::is_sentinel(queue.head), ENO_MESSAGE);
        assert!(guarded_idx::is_sentinel(queue.tail), ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 0, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 0, ENO_MESSAGE);
    }

    #[test_only]
    fun print_queue(queue: &Queue<u64>) {
        let head = queue.head;
        while (!guarded_idx::is_sentinel(head)) {
            let n = vector::borrow(&queue.nodes, guarded_idx::unguard(head));
            debug::print(&n.value);
            head = n.next;
        }
    }

    #[test]
    fun test_enqueue_after_dequeue() {
        let queue = new<u64>();
        enqueue(&mut queue, 1);
        enqueue(&mut queue, 2);
        let v = dequeue(&mut queue);
        assert!(v == 1, ENO_MESSAGE);
        enqueue(&mut queue, 3);
        assert!(size(&queue) == 2, ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 0, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 2, ENO_MESSAGE);
        enqueue(&mut queue, 4);
        assert!(size(&queue) == 3, ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 0, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 3, ENO_MESSAGE);
        let v = dequeue(&mut queue);
        assert!(v == 2, ENO_MESSAGE);
        assert!(size(&queue) == 2, ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 1, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 3, ENO_MESSAGE);
        let v = dequeue(&mut queue);
        assert!(v == 3, ENO_MESSAGE);
        assert!(size(&queue) == 1, ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 2, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 3, ENO_MESSAGE);
        enqueue(&mut queue, 5);
        assert!(size(&queue) == 2, ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 1, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 3, ENO_MESSAGE);
        let v = dequeue(&mut queue);
        assert!(v == 4, ENO_MESSAGE);
        assert!(size(&queue) == 1, ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 2, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 3, ENO_MESSAGE);

        // queue should be cleared when last element removed
        let v = dequeue(&mut queue);
        assert!(v == 5, ENO_MESSAGE);
        assert!(size(&queue) == 0, ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 0, ENO_MESSAGE);
        assert!(vector::length(&queue.nodes) == 0, ENO_MESSAGE);
    }

    #[test]
    fun test_peek() {
        let queue = new<u64>();
        enqueue(&mut queue, 1);
        enqueue(&mut queue, 2);
        let top = peek(&queue);
        assert!(*top == 1, ENO_MESSAGE);
    }

    #[test]
    fun test_iterator() {
        let queue = new<u64>();
        enqueue(&mut queue, 1);
        enqueue(&mut queue, 2);
        let iter = init_iterator<u64>();
        assert!(has_next(&queue, &iter), ENO_MESSAGE);
        let i = next_index(&queue, &mut iter);
        let n = get(&queue, i);
        assert!(*n == 1, ENO_MESSAGE);
        let i = next_index(&queue, &mut iter);
        let n = get(&queue, i);
        assert!(*n == 2, ENO_MESSAGE);
        assert!(!has_next(&queue, &iter), ENO_MESSAGE);
    }

    #[test]
    fun test_multiple_inserts_removals() {
        let queue = new<u64>();
        enqueue(&mut queue, 10);
        enqueue(&mut queue, 20);
        enqueue(&mut queue, 30);
        enqueue(&mut queue, 40);
        enqueue(&mut queue, 50);
        enqueue(&mut queue, 60);

        remove(&mut queue, 2, option::some(1));
        remove(&mut queue, 3, option::some(1));
        remove(&mut queue, 4, option::some(1));

        print_queue(&queue); // 10 -> 20 -> 60
        assert!(size(&queue) == 3, ENO_MESSAGE);

        enqueue(&mut queue, 70);
        assert!(size(&queue) == 4, ENO_MESSAGE);
        print_queue(&queue); // Error : (Expected 10, 20, 60, 70  ; Occured 10, 20, 60, 50)

        let one = dequeue(&mut queue);
        assert!(one == 10, ENO_MESSAGE);
        let two = dequeue(&mut queue);
        assert!(two == 20, ENO_MESSAGE);
        let three = dequeue(&mut queue);
        assert!(three == 60, ENO_MESSAGE);
        let four = dequeue(&mut queue);
        assert!(four == 70, ENO_MESSAGE);
        debug::print(&queue.nodes);
        assert!(size(&queue) == 0, ENO_MESSAGE);

        assert!(vector::length(&queue.nodes) == 0, ENO_MESSAGE);
        assert!(vector::length(&queue.free_indices) == 0, ENO_MESSAGE);
        assert!(guarded_idx::is_sentinel(queue.head), ENO_MESSAGE);
        assert!(guarded_idx::is_sentinel(queue.tail), ENO_MESSAGE);
    }

}