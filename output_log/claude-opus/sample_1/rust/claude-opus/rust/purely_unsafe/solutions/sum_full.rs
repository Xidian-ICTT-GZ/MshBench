use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

pred nodes(node: *mut Node; sum: int) =
    if node == std::ptr::null_mut() {
        sum == 0
    } else {
        node->next |-> ?next &*& node->value |-> ?v &*& nodes(next, ?tail_sum) &*& sum == v + tail_sum
    };

pred stack(stack: *mut Stack; sum: int) =
    stack->head |-> ?head &*& nodes(head, sum);

#[requires(nodes(node, ?sum))]
#[ensures(nodes(node, sum) &*& result == sum)]
unsafe fn get_nodes_sum(node: *mut Node) -> i32 {
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }

    result
}

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, 0))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack, ?sum))]
    #[ensures(stack(stack, sum) &*& result == sum)]
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }

    #[requires(stack(stack, ?sum))]
    #[ensures(stack(stack, sum + value))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        // Allocating node: full ownership of n->next and n->value is established
        n->next |-> _ &*& n->value |-> _;

        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, ?sum) &*& sum != 0)]
    #[ensures(stack(stack, sum - result))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        // explicitly require ownership of *head node to deallocate
        head->next |-> ?next &*& head->value |-> ?val &*& nodes(next, sum - val);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack, 0))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        // no nodes to free, only stack itself
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);

        let result1 = Stack::pop(s);

        let result2 = Stack::pop(s);

        Stack::dispose(s);
    }
}