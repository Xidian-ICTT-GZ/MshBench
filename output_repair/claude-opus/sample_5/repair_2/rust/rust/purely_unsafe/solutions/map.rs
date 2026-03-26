use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Func = unsafe fn(*mut u8, i32) -> i32;

/*@
pred Node_own(n: *mut Node; next: *mut Node, value: i32) =
    (*n).next |-> next &*& (*n).value |-> value &*& alloc_block(n as *mut u8, Layout::new_::<Node>());

pred Nodes(n: *mut Node;) =
    if n == 0 as *mut Node {
        true
    } else {
        Node_own(n, ?next, ?value) &*& Nodes(next)
    };

pred Stack_own(s: *mut Stack; head: *mut Node) =
    (*s).head |-> head &*& alloc_block(s as *mut u8, Layout::new_::<Stack>());

pred Stack(s: *mut Stack;) =
    Stack_own(s, ?head) &*& Nodes(head);

pred_ctor I32Func_pre(f: I32Func, data: *mut u8)() =
    (*((data as *mut i32))).i32_full_borrow_content |-> ?v;

pred_ctor I32Func_post(f: I32Func, data: *mut u8)() =
    (*((data as *mut i32))).i32_full_borrow_content |-> ?v;
@*/

/*@
pred i32_ptr(p: *mut i32; v: i32) = *p |-> v;
@*/

#[requires(Nodes(n) &*& i32_ptr(data as *mut i32, ?dv))]
#[ensures(Nodes(n) &*& i32_ptr(data as *mut i32, dv))]
unsafe fn map_nodes(n: *mut Node, f: I32Func, data: *mut u8) {
    if !n.is_null() {
        //@ open Nodes(n);
        //@ open Node_own(n, ?next, ?value);
        let y = f(data, (*n).value);
        (*n).value = y;
        //@ close Node_own(n, next, y);
        map_nodes((*n).next, f, data);
        //@ close Nodes(n);
    } else {
        //@ open Nodes(n);
        //@ close Nodes(n);
    }
}

#[requires(Nodes(n))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        //@ open Nodes(n);
        //@ open Node_own(n, ?next, ?value);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    } else {
        //@ open Nodes(n);
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(Stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node);
        //@ close Stack_own(stack, 0 as *mut Node);
        //@ close Stack(stack);
        return stack;
    }

    #[requires(Stack(stack))]
    #[ensures(Stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Node_own(n, head, value);
        //@ close Nodes(n);
        //@ close Stack_own(stack, n);
        //@ close Stack(stack);
    }

    #[requires(Stack(stack) &*& (*stack).head != 0 as *mut Node)]
    #[ensures(Stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?h);
        let head = (*stack).head;
        //@ open Nodes(head);
        //@ open Node_own(head, ?next, ?val);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_own(stack, next);
        //@ close Stack(stack);
        return result;
    }

    #[requires(Stack(stack) &*& i32_ptr(data as *mut i32, ?dv))]
    #[ensures(Stack(stack) &*& i32_ptr(data as *mut i32, dv))]
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8) {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?head);
        map_nodes((*stack).head, f, data);
        //@ close Stack_own(stack, head);
        //@ close Stack(stack);
    }

    #[requires(Stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(i32_ptr(data as *mut i32, ?v))]
#[ensures(i32_ptr(data as *mut i32, v))]
unsafe fn plus_a(data: *mut u8, x: i32) -> i32 {
    //@ open i32_ptr(data as *mut i32, v);
    let result = x + *(data as *mut i32);
    //@ close i32_ptr(data as *mut i32, v);
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
        //@ close i32_ptr(&raw mut a, a);
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        //@ open i32_ptr(&raw mut a, a);
        Stack::dispose(s);
    }
}