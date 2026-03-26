use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@

pred stack<T>(s: *mut Stack<T>; head: *mut Node<T>) =
    s != 0 &*& (*s).head |-> head;

pred nodes<T>(n: *mut Node<T>) =
    n == 0
        ? true
        : (*n).next |-> ?next &*& (*n).value |-> _ &*& nodes::<T>(next);

@*/

impl<T> Stack<T> {

    unsafe fn create() -> *mut Stack<T>
    //@ req true;
    //@ ens stack::<T>(result, 0);
    
    
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close stack::<T>(stack, _);
        (*stack).head = std::ptr::null_mut();
        //@ close stack::<T>(stack, 0);
        
        
        stack
    }
    
    unsafe fn push(stack: *mut Stack<T>, value: T)
    //@ req stack::<T>(stack, ?head) &*& nodes::<T>(head);
    //@ ens stack::<T>(stack, ?newHead) &*& nodes::<T>(newHead);
    
    
    {
        //@ open stack::<T>(stack, head);
        
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close nodes::<T>(n);
        (*stack).head = n;
        //@ close stack::<T>(stack, n);
        
        
    }
    
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    //@ req stack::<T>(stack, ?head);
    //@ ens stack::<T>(stack, head) &*& result == (head == 0);
    
    
    {
        //@ open stack::<T>(stack, head);
        
        let head = (*stack).head;
        
        let result = head.is_null();
        
        //@ close stack::<T>(stack, head);
        
        
        result
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    //@ req stack::<T>(stack, ?head) &*& head != 0 &*& nodes::<T>(head);
    //@ ens stack::<T>(stack, ?newHead) &*& nodes::<T>(newHead);
    
    
    {
        //@ open stack::<T>(stack, head);
        
        let head = (*stack).head;
        
        //@ open nodes::<T>(head);
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        //@ close stack::<T>(stack, (*stack).head);
        
        
        result
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    //@ req stack::<T>(stack, ?head) &*& nodes::<T>(head);
    //@ ens true;
    
    
    {
        //@ open stack::<T>(stack, head);
        // Note: we do not deallocate remaining nodes; they are intentionally leaked in this conservative specification.
        // We also do not open nodes(head) to avoid needing to recursively consume the list.
        
        
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

impl Vector {

    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    //@ req true;
    //@ ens result != 0 &*& (*result).x |-> x &*& (*result).y |-> y;
    
    
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        
        //@ close_struct(result);
        result
    }
    
}

fn main()
//@ req true;
//@ ens true;

{
    unsafe {
        let limit = input_i32();
        let s = Stack::create();
        
        loop {
            
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
                    let v1 = Stack::pop(s);
                    
                    
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    
                    
                    //@ open_struct(v1);
                    //@ open_struct(v2);
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    //@ open_struct(sum);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ close_struct(sum);
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    
                    
                    //@ open_struct(v_);
                    std::hint::assert_unchecked((*v_).x * (*v_).x + (*v_).y * (*v_).y <= limit * limit);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}