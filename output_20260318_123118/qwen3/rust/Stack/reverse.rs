use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate Nodes(*mut Node n; list<i32> vs) =
    match vs {
        Nil => n == std::ptr::null_mut(),
        Cons(v, vs1) => n != std::ptr::null_mut() && (*n).value |-> v && (*n).next |-> ?n1 && Nodes(n1, vs1)
    };

predicate Stack_own(*mut Stack s; list<i32> vs) =
    s != std::ptr::null_mut() &&
    (*s).head |-> ?h &&
    Nodes(h, vs);

impl Stack {

    #[requires(true)]
    #[ensures(Stack_own(result, Nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(Stack_own(stack, ?vs))]
    #[ensures(Stack_own(stack, Cons(value, vs)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }
    
    #[requires(Stack_own(stack, Cons(?v, ?vs)))]
    #[ensures(Stack_own(stack, vs) && result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }
    
    #[requires(Stack_own(stack, ?vs))]
    #[ensures(Stack_own(stack, reverse(vs)))]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        loop {
            invariant Stack_own(stack, ?prefix) && Nodes(n, ?suffix) && Nodes(m, reverse(prefix)) && append(prefix, suffix) == vs;
            if n.is_null() {
                break;
            }
            let next = (*n).next;
            (*n).next = m;
            m = n;
            n = next;
        }
        (*stack).head = m;
    }

    #[requires(Stack_own(stack, _))]
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
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}