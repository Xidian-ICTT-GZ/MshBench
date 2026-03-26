use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

predicate nodes(struct Node *n; list<int> vs) =
    n == std::ptr::null_mut()
    ?
        vs == []
    :
        n |-> Node{next: *mut Node, value: int} &*&
        nodes((*n).next, ?rest) &*&
        vs == cons((*n).value, rest);

struct Stack {
    head: *mut Node,
}

predicate stack(struct Stack *s; list<int> vs) =
    s |-> Stack{head: *mut Node} &*& nodes((*s).head, vs);

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
    #[requires(nodes(n, ?vs))]
    #[ensures(nodes(n, ?vs2))]
    //@ decreases length(vs)
{
    if !n.is_null() {
        int old_val = (*n).value;
        int y = f(data, old_val);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ assert nodes((*n).next, ?rest);
        //@ close nodes(n, cons(y, rest));
    }
    else {
        //@ close nodes(n, []);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(nodes(n, _))]
    #[ensures(true)]
    //@ decreases nodes_length(n)
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
        #[requires(true)]
        #[ensures(stack(result, []))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes((*stack).head, []);
        //@ close stack(stack, []);
        return stack;
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack(stack, ?vs))]
        #[ensures(stack(stack, cons(value, vs)))]
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n, cons(value, vs));
        //@ close stack(stack, cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires(stack(stack, ?vs)) &*& vs != []]
        #[ensures(stack(stack, tail(vs)) &*& result == head(vs))]
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ open nodes(head, vs);
        //@ open stack(stack, vs);
        //@ close stack(stack, tail(vs));
        return result;
    }
    
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
        #[requires(stack(stack, ?vs))]
        #[ensures(stack(stack, ?vs2))]
        //@ decreases length(vs)
    {
        map_nodes((*stack).head, f, data);
        //@ open stack(stack, vs);
        //@ close stack(stack, vs);
    }
    
    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack(stack, _))]
        #[ensures(true)]
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
    #[requires(true)]
    #[ensures(true)]
{
    let result = x + *(data as *mut i32);
    result
}

unsafe fn read_i32() -> i32
    #[requires(true)]
    #[ensures(true)]
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();

        Stack::map(s, plus_a, &raw mut a as *mut u8);

        Stack::dispose(s);
    }
}

fixpoint int head(list<int> vs) {
    switch(vs) {
        case nil: return 0; 
        case cons(x, _): return x;
    }
}

fixpoint list<int> tail(list<int> vs) {
    switch(vs) {
        case nil: return nil;
        case cons(_, xs): return xs;
    }
}

fixpoint int nodes_length(struct Node *n) {
    return n == std::ptr::null_mut() ? 0 : 1 + nodes_length((*n).next);
}