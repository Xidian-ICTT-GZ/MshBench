use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ pred node<T>(n: *mut Node<T>, next: *mut Node<T>, v: T) = n as *mut u8 |-> ?b &*& struct_Node_padding(?pad) &*& [?f]std::alloc::GlobalAlloc_block(n as *mut u8, std::alloc::Layout::from_size_align_unchecked(std::mem::size_of::<Node<T>>(), std::mem::align_of::<Node<T>>()), ?m) &*& std::ptr::raw_mut_field(n, 0, next) &*& std::ptr::raw_mut_field(n, 1, v);

//@ pred stack<T>(s: *mut Stack<T>, head: *mut Node<T>) = s as *mut u8 |-> ?b &*& struct_Stack_padding(?pad) &*& [?f]std::alloc::GlobalAlloc_block(s as *mut u8, std::alloc::Layout::from_size_align_unchecked(std::mem::size_of::<Stack<T>>(), std::mem::align_of::<Stack<T>>()), ?m) &*& std::ptr::raw_mut_field(s, 0, head);

//@ pred vector(v: *mut Vector, x: i32, y: i32) = v as *mut u8 |-> ?b &*& struct_Vector_padding(?pad) &*& [?f]std::alloc::GlobalAlloc_block(v as *mut u8, std::alloc::Layout::from_size_align_unchecked(std::mem::size_of::<Vector>(), std::mem::align_of::<Vector>()), ?m) &*& std::ptr::raw_mut_field(v, 0, x) &*& std::ptr::raw_mut_field(v, 1, y);

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    
    
    {
        //@ req true;
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, std::ptr::null_mut());
        
        
        stack
        //@ ens stack(result, std::ptr::null_mut());
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    
    
    {
        //@ req stack(stack, ?old_head);
        //@ open stack(stack, old_head);
        
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close node(n, old_head, value);
        (*stack).head = n;
        //@ close stack(stack, n);
        
        
        //@ ens stack(stack, _);
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    
    
    {
        //@ req stack(stack, ?head);
        let head = (*stack).head;
        
        let result = head.is_null();
        //@ close stack(stack, head);
        
        
        result
        //@ ens stack(stack, ?head_) &*& result == (head_ == std::ptr::null_mut::<Node<T>>());
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    
    
    {
        //@ req stack(stack, ?head) &*& head != std::ptr::null_mut() &*& node(head, ?next, ?v);
        //@ open stack(stack, head);
        let head = (*stack).head;
        //@ open node(head, next, v);
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack(stack, next);
        
        result
        //@ ens stack(stack, ?head_) &*& result == v;
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    
    
    {
        //@ req stack(stack, _);
        //@ open stack(stack, _);
        
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
        //@ ens true;
    }

}

unsafe fn input_char() -> char

{
    //@ req true;
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
    //@ ens true;
}

unsafe fn input_i32() -> i32

{
    //@ req true;
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
    //@ ens true;
}

unsafe fn output_i32(value: i32)

{
    //@ req true;
    println!("{}", value);
    //@ ens true;
}

struct Vector {
    x: i32,
    y: i32,
}

impl Vector {

    unsafe fn create(x: i32, y: i32) -> *mut Vector
    
    
    {
        //@ req true;
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close vector(result, x, y);
        
        result
        //@ ens vector(result, x, y);
    }
    
}

fn main()

{
    unsafe {
        let s = Stack::create();
        //@ let s_pred = stack(s, std::ptr::null_mut());
        //@ close s_pred;
        
        loop {
            
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    let v = Vector::create(x, y);
                    //@ open vector(v, x, y);
                    Stack::push(s, v);
                    //@ open s_pred;
                    //@ close s_pred;
                    
                }
                '+' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open s_pred;
                    let v1 = Stack::pop(s);
                    //@ close s_pred;
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open s_pred;
                    let v2 = Stack::pop(s);
                    //@ close s_pred;
                    
                    
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ open vector(sum, _, _);
                    Stack::push(s, sum);
                    //@ open s_pred;
                    //@ close s_pred;
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    //@ open s_pred;
                    let v_ = Stack::pop(s);
                    //@ close s_pred;
                    
                    
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}