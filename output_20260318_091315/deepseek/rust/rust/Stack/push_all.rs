use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(n: *mut Node; value: i32, next: *mut Node) {
    struct_Node!(n => { next: next, value: value }) &*&
    n != 0
}

predicate nodes(n: *mut Node; count: i32) {
    n == 0 ? count == 0 :
    exists_<*mut Node>(next) &*&
    exists_<i32>(value) &*&
    node(n, value, next) &*&
    nodes(next, count - 1) &*&
    count > 0
}

predicate stack(s: *mut Stack; count: i32) {
    struct_Stack!(s => { head: head }) &*&
    nodes(head, count) &*&
    s != 0
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

    #[requires(stack(stack, count))]
    #[ensures(stack(stack, count) &*& result == count)]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        
        #[invariant(nodes(n, remaining) &*& nodes(head, count) &*& remaining == count - i &*& i >= 0)]
        loop {
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
        i
    }

    #[requires(stack(stack, count1) &*& stack(other, count2))]
    #[ensures(stack(stack, count1 + count2))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        
        if !n.is_null() {
            #[invariant(nodes(n, remaining) &*& nodes(head0, count2) &*& remaining > 0)]
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }
            (*n).next = (*stack).head;
            (*stack).head = head0;
        }
    }

    #[requires(stack(stack, count))]
    #[ensures(stack(stack, count + 1))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, count) &*& count > 0)]
    #[ensures(stack(stack, count - 1) &*& result == old((*stack.head).value))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack, 0))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
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