use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

/*@
pred Node<T>(node: *mut Node<T>, value: T, next: *mut Node<T>) =
    alloc_block(node, std::mem::size_of::<Node<T>>()) &*&
    struct_Node_padding(&(*node)) &*&
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
    struct_Stack_padding(&(*stack)) &*&
    (*stack).head |-> head &*&
    lseg(head, std::ptr::null_mut(), nodes);
    
pred lseg<T>(head: *mut Node<T>, tail: *mut Node<T>, nodes: list<*mut Node<T>>) =
    head == tail ?
        nodes == [] &*& true
    :
        nodes == [node] + rest &*&
        head == node &*&
        Node(node, ?value, ?next) &*&
        lseg(next, tail, rest);
@*/

struct Stack<T> {
    head: *mut Node<T>,
}

impl<T> Stack<T> {
    //@ req true;
    //@ ens Stack(result, []);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close lseg(std::ptr::null_mut(), std::ptr::null_mut(), []);
        //@ close Stack(stack, []);
        stack
    }
    
    //@ req Stack(stack, ?nodes);
    //@ ens Stack(stack, [n] + nodes);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open Stack(stack, nodes);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close Node(n, value, (*stack).head);
        //@ close lseg(n, std::ptr::null_mut(), [n] + nodes);
        (*stack).head = n;
        //@ close Stack(stack, [n] + nodes);
    }
    
    //@ req Stack(stack, ?nodes);
    //@ ens Stack(stack, nodes) &*& result == nodes.is_empty();
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open Stack(stack, nodes);
        let head = (*stack).head;
        //@ open lseg(head, std::ptr::null_mut(), nodes);
        let result = head.is_null();
        //@ close lseg(head, std::ptr::null_mut(), nodes);
        //@ close Stack(stack, nodes);
        result
    }
    
    //@ req Stack(stack, [?head_node] + ?tail_nodes);
    //@ ens Stack(stack, tail_nodes) &*& Node(head_node, result, _);
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open Stack(stack, [head_node] + tail_nodes);
        let head = (*stack).head;
        //@ open lseg(head, std::ptr::null_mut(), [head_node] + tail_nodes);
        //@ assert Node(head_node, ?value, ?next);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ open Node(head, _, _);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close lseg((*stack).head, std::ptr::null_mut(), tail_nodes);
        //@ close Stack(stack, tail_nodes);
        result
    }

    //@ req Stack(stack, []);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open Stack(stack, []);
        //@ open lseg(std::ptr::null_mut(), std::ptr::null_mut(), []);
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
pred Vector(vec: *mut Vector) =
    alloc_block(vec, std::mem::size_of::<Vector>()) &*&
    struct_Vector_padding(&(*vec)) &*&
    (*vec).x |-> ?x &*&
    (*vec).y |-> ?y;
@*/

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {
    //@ req true;
    //@ ens Vector(result);
    unsafe fn create(x: i32, y: i32) -> *mut Vector
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close Vector(result);
        result
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        //@ close Stack(s, []);
        
        loop {
            //@ inv Stack(s, ?nodes);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    //@ open Vector(v1);
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open Vector(v2);
                    
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open Vector(v_);
                    
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}