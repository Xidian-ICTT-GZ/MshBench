use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@
predicate Node<T>(n: *mut Node<T>; next: *mut Node<T>, value: T) =
    (*n).next |-> next &*& (*n).value |-> value;

predicate Nodes<T>(head: *mut Node<T>) =
    head == std::ptr::null_mut() ?
        true
    :
        (*head).next |-> ?next &*& (*head).value |-> ?value &*& struct_Node_padding(head) &*& alloc_block(head as *mut u8, Layout::new_::<Node<T>>()) &*& Nodes::<T>(next);

predicate Stack<T>(stack: *mut Stack<T>) =
    (*stack).head |-> ?head &*& struct_Stack_padding(stack) &*& alloc_block(stack as *mut u8, Layout::new_::<Stack<T>>()) &*& Nodes::<T>(head);

predicate Vector(v: *mut Vector; x: i32, y: i32) =
    (*v).x |-> x &*& (*v).y |-> y &*& struct_Vector_padding(v) &*& alloc_block(v as *mut u8, Layout::new_::<Vector>());
@*/

impl<T> Stack<T> {
    #[ensures(Stack::<T>(result))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close Nodes::<T>(std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        //@ close Stack::<T>(stack);
        stack
    }

    #[requires(Stack::<T>(stack))]
    #[ensures(Stack::<T>(stack))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        //@ open Stack::<T>(stack);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close Nodes::<T>(n);
        (*stack).head = n;
        //@ close Stack::<T>(stack);
    }

    #[requires(Stack::<T>(stack))]
    #[ensures(Stack::<T>(stack))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        //@ open Stack::<T>(stack);
        let head = (*stack).head;

        let result = head.is_null();
        //@ close Stack::<T>(stack);
        result
    }

    #[requires(Stack::<T>(stack) &*& (*stack).head != std::ptr::null_mut())]
    #[ensures(Stack::<T>(stack))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        //@ open Stack::<T>(stack);
        let head = (*stack).head;
        //@ open Nodes::<T>(head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close Stack::<T>(stack);
        result
    }

    #[requires((*stack).head |-> ?head &*& head == std::ptr::null_mut() &*& struct_Stack_padding(stack) &*& alloc_block(stack as *mut u8, Layout::new_::<Stack<T>>()))]
    unsafe fn dispose(stack: *mut Stack<T>) {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

#[ensures(true)]
unsafe fn input_char() -> char {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

#[ensures(true)]
unsafe fn input_i32() -> i32 {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

#[requires(true)]
#[ensures(true)]
unsafe fn output_i32(value: i32) {
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {
    #[ensures(Vector(result, x, y))]
    unsafe fn create(x: i32, y: i32) -> *mut Vector {
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

fn main() {
    unsafe {
        let s = Stack::create();

        #[invariant(Stack::<*mut Vector>(s))]
        loop {
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    Stack::push(s, v);
                }
                '+' => {
                    //@ open Stack::<*mut Vector>(s);
                    //@ open Nodes::<*mut Vector>((*s).head);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ close Nodes::<*mut Vector>((*s).head);
                    //@ close Stack::<*mut Vector>(s);
                    let v1 = Stack::pop(s);
                    //@ open Vector(v1, ?v1x, ?v1y);

                    //@ open Stack::<*mut Vector>(s);
                    //@ open Nodes::<*mut Vector>((*s).head);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ close Nodes::<*mut Vector>((*s).head);
                    //@ close Stack::<*mut Vector>(s);
                    let v2 = Stack::pop(s);
                    //@ open Vector(v2, ?v2x, ?v2y);

                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    //@ open Stack::<*mut Vector>(s);
                    //@ open Nodes::<*mut Vector>((*s).head);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ close Nodes::<*mut Vector>((*s).head);
                    //@ close Stack::<*mut Vector>(s);
                    let v_ = Stack::pop(s);
                    //@ open Vector(v_, ?vx, ?vy);

                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command"),
            }
        }
    }
}