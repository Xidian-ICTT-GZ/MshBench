use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@
predicate nodes<T>(struct Node<T> *node;) =
    node == 0 ? true : alloc::pointers::struct_Node_own(node) &*& nodes(*node.next);
@*/

/*@
predicate stack<T>(struct Stack<T> *stack;) =
    alloc::pointers::struct_Stack_own(stack) &*& nodes(*stack.head);
@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens stack(result);
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(0);
        //@ close stack(stack);
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack(stack) &*& owned(&value);
    //@ ens stack(stack);
    {
        //@ open stack(stack);
        //@ open nodes(*stack.head);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close nodes(n);
        //@ close stack(stack);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == (*stack.head == 0);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        let result = head.is_null();
        //@ close nodes(head);
        //@ close stack(stack);
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack(stack) &*& (*stack.head != 0);
    //@ ens stack(stack) &*& owned(&result);
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open nodes(head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ close nodes(*stack.head);
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack(stack);
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack(stack);
    //@ ens true;
    {
        //@ open stack(stack);
        //@ open nodes(*stack.head);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

unsafe fn input_char() -> char
//@ req true;
//@ ens true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32
//@ req true;
//@ ens true;
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32)
//@ req true;
//@ ens true;
{
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

/*@
predicate vector(struct Vector *v;) =
    alloc::pointers::struct_Vector_own(v);
@*/

impl Vector {

    unsafe fn create(x: i32, y: i32) -> *mut Vector
    //@ req true;
    //@ ens vector(result);
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close vector(result);
        result
    }
    
}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        //@ close nodes(0);
        //@ close stack(s);
        loop {
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    //@ close nodes(*s.head);
                    Stack::push(s, v);
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    //@ open vector(v1);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    //@ open vector(v2);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ close nodes(*s.head);
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    //@ open vector(v_);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}