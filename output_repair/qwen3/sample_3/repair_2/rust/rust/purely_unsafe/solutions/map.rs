use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

predicate node_list(*mut Node n;);

predicate stack_inv(*mut Stack s;) =
    s |-> ?head &*& node_list(head);

predicate i32_at(*mut i32 p;) =
    p |-> ?v;

lemma void node_list_nil()
    requires true;
    ensures node_list(null);
{
    close node_list(null);
}

lemma void node_list_cons(*mut Node n, *mut Node next, i32 value)
    requires n |-> struct Node { next: next, value: value } &*& node_list(next);
    ensures node_list(n);
{
    close node_list(n);
}

lemma void node_list_unfold(*mut Node n)
    requires node_list(n);
    ensures n == null || (n |-> struct Node { next: ?next, value: ?value } &*& node_list(next));
{
    open node_list(n);
    if n != null {
        assert n |-> struct Node { next: _, value: _ };
    }
}

unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
    requires node_list(n) &*& i32_at(data as *mut i32);
    ensures node_list(n) &*& i32_at(data as *mut i32);
{
    if n != null {
        node_list_unfold(n);
        let old_next = (*n).next;
        let old_value = (*n).value;
        let y = f(data, old_value);
        (*n).value = y;
        map_nodes(old_next, f, data);
        node_list_cons(n, old_next, y);
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires node_list(n);
    ensures true;
{
    if n != null {
        node_list_unfold(n);
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires true;
        ensures stack_inv(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack_inv(stack);
        return stack;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack_inv(stack);
        ensures stack_inv(stack);
    {
        open stack_inv(stack);
        let old_head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = old_head;
        (*n).value = value;
        (*stack).head = n;
        node_list_cons(n, old_head, value);
        close stack_inv(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack_inv(stack) &*& (*stack).head != null;
        ensures stack_inv(stack);
    {
        open stack_inv(stack);
        let head = (*stack).head;
        node_list_unfold(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack_inv(stack);
        return result;
    }

    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
        requires stack_inv(stack) &*& i32_at(data as *mut i32);
        ensures stack_inv(stack) &*& i32_at(data as *mut i32);
    {
        open stack_inv(stack);
        let head = (*stack).head;
        map_nodes(head, f, data);
        close stack_inv(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack_inv(stack);
        ensures true;
    {
        open stack_inv(stack);
        let head = (*stack).head;
        dispose_nodes(head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn plus_a(data: *mut u8, x: i32) -> i32
    requires i32_at(data as *mut i32);
    ensures i32_at(data as *mut i32);
{
    let result = x + *(data as *mut i32);
    return result;
}

unsafe fn read_i32() -> i32
    requires true;
    ensures true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
    requires true;
    ensures true;
{
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