use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

/*@
pred nodes(n: *mut Node; count: i32) =
    if n == std::ptr::null_mut() {
        count == 0
    } else {
        (*n).next |-> ?next &*& (*n).value |-> ?_value &*& 
        alloc_block(n as *mut u8, Layout::new_::<Node>()) &*&
        nodes(next, ?rest_count) &*& count == rest_count + 1
    };

pred stack(s: *mut Stack; count: i32) =
    (*s).head |-> ?head &*& alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*& nodes(head, count);
@*/

#[requires(nodes(n, ?count))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    //@ open nodes(n, count);
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[ensures(stack(result, 0))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut(), 0);
        //@ close stack(stack, 0);
        return stack;
    }

    #[requires(stack(stack, ?count))]
    #[ensures(stack(stack, count))]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        //@ open stack(stack, count);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close stack(stack, count);
        return result;
    }

    #[requires(stack(stack, ?count))]
    #[ensures(stack(stack, count + 1))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack(stack, count);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes(n, count + 1);
        (*stack).head = n;
        //@ close stack(stack, count + 1);
    }

    #[requires(stack(stack, ?count) &*& count > 0)]
    #[ensures(stack(stack, count - 1))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open stack(stack, count);
        let head = (*stack).head;
        //@ open nodes(head, count);
        let result = (*head).value;
        let next = (*head).next;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, count - 1);
        return result;
    }

    #[requires(stack(stack, ?count))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack, count);
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}