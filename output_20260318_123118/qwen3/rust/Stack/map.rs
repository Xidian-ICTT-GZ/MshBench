use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node n; *mut Node next, i32 value) =
    n |-> struct Node { next: next, value: value };

predicate stack(*mut Stack s; list<*mut Node> nodes) =
    s |-> struct Stack { head: ?head } &*&
    nodes == match nodes {
        cons(n, ns) => node(n, ?next, ?v) &*& stack_nodes(next, ns),
        nil => emp &*& head == std::ptr::null_mut()
    };

predicate stack_nodes(*mut Node head; list<*mut Node> nodes) =
    match nodes {
        cons(n, ns) => node(n, ?next, ?v) &*& stack_nodes(next, ns),
        nil => emp &*& head == std::ptr::null_mut()
    };

lemma void stack_split(list<*mut Node> nodes)
    requires stack(?s, nodes);
    ensures stack(s, nodes) &*& true;

lemma void stack_join(list<*mut Node> nodes)
    requires stack(?s, nodes) &*& true;
    ensures stack(s, nodes);

#[requires(true)]
#[ensures(node(result, std::ptr::null_mut(), value))]
unsafe fn alloc_node(value: i32) -> *mut Node {
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }
    (*n).next = std::ptr::null_mut();
    (*n).value = value;
    return n;
}

#[requires(node(n, ?next, ?value))]
#[ensures(stack_nodes(next, ?ns) &*& emp)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        open node(n, next, value);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

#[requires(stack(s, ?nodes))]
#[ensures(node(result, ?next, ?value) &*& stack(s, cons(result, nodes)))]
unsafe fn push_node(s: *mut Stack, value: i32) -> *mut Node {
    let n = alloc_node(value);
    open stack(s, nodes);
    (*n).next = (*s).head;
    (*s).head = n;
    close stack(s, cons(n, nodes));
    return n;
}

#[requires(stack(s, cons(?n, ?ns)))]
#[ensures(node(n, ?next, result) &*& stack(s, ns))]
unsafe fn pop_node(s: *mut Stack) -> i32 {
    open stack(s, cons(n, ns));
    let head = (*s).head;
    let result = (*head).value;
    (*s).head = (*head).next;
    close stack(s, ns);
    return result;
}

#[requires(stack_nodes(n, ?nodes))]
#[ensures(stack_nodes(n, nodes))]
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8) {
    if !n.is_null() {
        open stack_nodes(n, nodes);
        open node(n, ?next, ?value);
        let y = f(data, value);
        (*n).value = y;
        close node(n, next, y);
        close stack_nodes(n, nodes);
        map_nodes(next, f, data);
    }
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8) {
    if !n.is_null() {
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
    }
}

unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack(stack, nil);
        return stack;
    }

    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, cons(?n, nodes)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        open stack(stack, nodes);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close stack(stack, cons(n, nodes));
    }

    #[requires(stack(stack, cons(?n, ?ns)))]
    #[ensures(stack(stack, ns))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        open stack(stack, cons(n, ns));
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        close stack(stack, ns);
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    #[requires(stack(stack, ?nodes))]
    #[ensures(stack(stack, nodes))]
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8) {
        open stack(stack, nodes);
        map_nodes((*stack).head, f, data);
        close stack(stack, nodes);
    }

    #[requires(stack(stack, ?nodes))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack(stack, nodes);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(*data |-> ?a)]
#[ensures(*data |-> a)]
unsafe fn plus_a(data: *mut u8, x: i32) -> i32 {
    let result = x + *(data as *mut i32);
    result
}

#[requires(true)]
#[ensures(true)]
unsafe fn read_i32() -> i32 {
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