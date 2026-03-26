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
    (*n).next |-> next &*& (*n).value |-> value;

pred Nodes(n: *mut Node;) =
    if n == 0 as *mut Node {
        emp
    } else {
        Node_own(n, ?next, ?value) &*& Nodes(next)
    };

pred Stack_own(s: *mut Stack; head: *mut Node) =
    (*s).head |-> head;

pred Stack(s: *mut Stack;) =
    Stack_own(s, ?head) &*& Nodes(head);

pred i32_ptr(p: *mut i32; v: i32) = *p |-> v;
@*/

/*@
lemma void map_nodes_lemma(int x) { }
@*/

/*@
void map_nodes(struct Node *n, I32Func f, unsigned char *data)
    requires Nodes(n) &*& i32_ptr((int*)data, ?dv);
    ensures Nodes(n) &*& i32_ptr((int*)data, dv);
@*/
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
    }
}

/*@
void dispose_nodes(struct Node *n)
    requires Nodes(n);
    ensures emp;
@*/
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
    /*@
    struct Stack *Stack_create()
        requires true;
        ensures Stack(result);
    @*/
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

    /*@
    void Stack_push(struct Stack *stack, int value)
        requires Stack(stack);
        ensures Stack(stack);
    @*/
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

    /*@
    int Stack_pop(struct Stack *stack)
        requires Stack(stack) &*& (*stack).head != 0;
        ensures Stack(stack);
    @*/
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

    /*@
    void Stack_map(struct Stack *stack, I32Func f, unsigned char *data)
        requires Stack(stack) &*& i32_ptr((int*)data, ?dv);
        ensures Stack(stack) &*& i32_ptr((int*)data, dv);
    @*/
    unsafe fn map(stack: *mut Stack, f: I32Func, data: *mut u8) {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?head);
        map_nodes((*stack).head, f, data);
        //@ close Stack_own(stack, head);
        //@ close Stack(stack);
    }

    /*@
    void Stack_dispose(struct Stack *stack)
        requires Stack(stack);
        ensures emp;
    @*/
    unsafe fn dispose(stack: *mut Stack) {
        //@ open Stack(stack);
        //@ open Stack_own(stack, ?head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

/*@
int plus_a(unsigned char *data, int x)
    requires i32_ptr((int*)data, ?v);
    ensures i32_ptr((int*)data, v);
@*/
unsafe fn plus_a(data: *mut u8, x: i32) -> i32 {
    //@ open i32_ptr((int*)data, ?v);
    let result = x + *(data as *mut i32);
    //@ close i32_ptr((int*)data, v);
    result
}

/*@
int read_i32()
    requires true;
    ensures true;
@*/
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
        //@ close i32_ptr(&a, a);
        Stack::map(s, plus_a, &raw mut a as *mut u8);
        //@ open i32_ptr(&a, _);
        Stack::dispose(s);
    }
}