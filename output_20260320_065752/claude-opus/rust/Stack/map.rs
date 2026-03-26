use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@ 
  predicate node(struct Node* n; int value, struct Node* next) = 
      n->value |-> value &*& n->next |-> next;
  predicate nodes(struct Node* n; list<int> vs) = 
      n == 0 ? vs == nil : node(n, ?v, ?nx) &*& nodes(nx, ?rest) &*& vs == cons(v, rest);
  predicate stack(struct Stack* s; list<int> vs) = 
      s->head |-> ?h &*& nodes(h, vs);
@*/

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

//@ req nodes(n, ?vs) &*& f != 0;
//@ ensures nodes(n, vs);
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8)
{
    if !n.is_null() {
        //@ open nodes(n, ?vs);
        //@ open node(n, ?v, ?nx);
        let y = f(data, (*n).value);
        (*n).value = y;
        map_nodes((*n).next, f, data);
        //@ close node(n, y, nx);
        //@ close nodes(n, cons(y, ?rest));
    }
    //@ else {}
}

//@ req nodes(n, ?vs);
//@ ensures nodes(n, nil);
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        //@ open nodes(n, ?vs);
        //@ open node(n, ?v, ?nx);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
        //@ close nodes(0, nil);
    }
    //@ else {}
}

//@ req true;
//@ ensures stack(result, nil);
unsafe fn create() -> *mut Stack
{
    let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
    if stack.is_null() {
        handle_alloc_error(Layout::new::<Stack>());
    }
    (*stack).head = std::ptr::null_mut();
    //@ close stack(stack, nil);
    return stack;
}

//@ req stack(stack, ?vs);
//@ ensures stack(stack, cons(value, vs));
unsafe fn push(stack: *mut Stack, value: i32)
{
    //@ open stack(stack, vs);
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }
    (*n).next = (*stack).head;
    (*n).value = value;
    (*stack).head = n;
    //@ close node(n, value, ?nx);
    //@ close nodes(n, cons(value, vs));
    //@ close stack(stack, cons(value, vs));
}

//@ req stack(stack, cons(?v, ?vs));
//@ ensures stack(stack, vs);
unsafe fn pop(stack: *mut Stack) -> i32
{
    //@ open stack(stack, cons(v, vs));
    let head = (*stack).head;
    //@ open nodes(head, cons(v, vs));
    //@ open node(head, v, ?nx);
    let result = (*head).value;
    (*stack).head = (*head).next;
    dealloc(head as *mut u8, Layout::new::<Node>());
    //@ close nodes((*stack).head, vs);
    //@ close stack(stack, vs);
    return result;
}

//@ req stack(stack, ?vs) &*& f != 0;
//@ ensures stack(stack, vs);
unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8)
{
    //@ open stack(stack, vs);
    map_nodes((*stack).head, f, data);
    //@ close stack(stack, vs);
}

//@ req stack(stack, ?vs);
//@ ensures true;
unsafe fn dispose(stack: *mut Stack)
{
    //@ open stack(stack, vs);
    dispose_nodes((*stack).head);
    dealloc(stack as *mut u8, Layout::new::<Stack>());
}

//@ req true;
//@ ensures true;
unsafe fn plus_a(data: *mut u8, x: i32) -> i32
{
    let result = x + *(data as *mut i32);
    result
}

//@ req true;
//@ ensures true;
unsafe fn read_i32() -> i32
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.parse().unwrap()
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::push(s, 30);
        let mut a = read_i32();
        Stack::map(s, plus_a, &mut a as *mut i32 as *mut u8);
        Stack::dispose(s);
    }
}