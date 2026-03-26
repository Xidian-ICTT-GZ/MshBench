use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Node<T>(node: *mut Node<T>, value: T, next: *mut Node<T>) =
    alloc_block(node, std::mem::size_of::<Node<T>>()) &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

/*@
pred Stack<T>(stack: *mut Stack<T>, nodes: list<*mut Node<T>>) =
    alloc_block(stack, std::mem::size_of::<Stack<T>>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head &*&
    (head.is_null() ?
        nodes == [] &*& true
    :
        Node<T>(head, _, next) &*&
        StackNodes<T>(next, tail(nodes)) &*&
        nodes == cons(head, tail(nodes))
    );

pred StackNodes<T>(head: *mut Node<T>, nodes: list<*mut Node<T>>) =
    head.is_null() ?
        nodes == [] &*& true
    :
        Node<T>(head, _, next) &*&
        StackNodes<T>(next, tail(nodes)) &*&
        nodes == cons(head, tail(nodes));
@*/

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    //@ req true;
    //@ ens Stack<T>(result, []);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close StackNodes<T>(std::ptr::null_mut(), []);
        //@ close Stack<T>(stack, []);
        stack
    }
    
    //@ req Stack<T>(stack, nodes);
    //@ ens Stack<T>(stack, cons(n, nodes));
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open Stack<T>(stack, nodes);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close Node<T>(n, value, (*stack).head);
        //@ close StackNodes<T>(n, nodes);
        (*stack).head = n;
        //@ close Stack<T>(stack, cons(n, nodes));
    }
    
    //@ req Stack<T>(stack, nodes);
    //@ ens Stack<T>(stack, nodes) &*& result == nodes.is_empty();
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open Stack<T>(stack, nodes);
        let head = (*stack).head;
        let result = head.is_null();
        //@ close Stack<T>(stack, nodes);
        result
    }
    
    //@ req Stack<T>(stack, cons(head, tail));
    //@ ens Stack<T>(stack, tail) &*& result == old_value;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open Stack<T>(stack, cons(head, tail));
        let head = (*stack).head;
        (*stack).head = (*head).next;
        //@ open Node<T>(head, old_value, (*head).next);
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack<T>(stack, tail);
        result
    }

    //@ req Stack<T>(stack, []);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open Stack<T>(stack, []);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

//@ assume_correct
unsafe fn input_char() -> char
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

//@ assume_correct
unsafe fn input_i32() -> i32
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

//@ assume_correct
unsafe fn output_i32(value: i32)
{
    println!("{}", value);
}

/*@
pred Vector(v: *mut Vector, x: i32, y: i32) =
    alloc_block(v, std::mem::size_of::<Vector>()) &*&
    struct_Vector_padding(v) &*&
    (*v).x |-> x &*&
    (*v).y |-> y;
@*/

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {
    //@ req x * x + y * y <= limit * limit;
    //@ ens Vector(result, x, y);
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Vector(result, x, y);
        result
    }
}

fn main()
{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        //@ close StackNodes<*mut Vector>(std::ptr::null_mut(), []);
        //@ close Stack<*mut Vector>(s, []);
        
        loop {
            //@ invariant Stack<*mut Vector>(s, nodes);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(limit, x, y);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open Stack<*mut Vector>(s, nodes);
                    //@ assert nodes == cons(?v1_head, ?v1_tail);
                    let v1 = Stack::pop(s);
                    //@ open Stack<*mut Vector>(s, v1_tail);
                    //@ assert v1_tail == cons(?v2_head, ?v2_tail);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open Vector(v1, ?x1, ?y1);
                    //@ open Vector(v2, ?x2, ?y2);
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open Stack<*mut Vector>(s, nodes);
                    //@ assert nodes == cons(?v_head, ?v_tail);
                    let v_ = Stack::pop(s);
                    //@ open Vector(v_, ?x, ?y);
                    std::hint::assert_unchecked((*v_).x * (*v_).x + (*v_).y * (*v_).y <= limit * limit);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                    //@ close Stack<*mut Vector>(s, v_tail);
                }
                _ => panic!("Bad command")
            }
        }
    }
}