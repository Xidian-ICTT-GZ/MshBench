use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

/*@ predicate node<T>(Node<T>* n, list<T> vs) =
      n != 0
      &*& n->next |-> ?next_
      &*& n->value |-> ?v
      &*& node(next_, ?vs_tail)
      &*& vs == cons(v, vs_tail)
   || n == 0 &*& vs == nil;
@*/

struct Stack<T> {
    head: *mut Node<T>,
}

/*@ predicate stack<T>(Stack<T>* s, list<T> vs) =
      s->head |-> ?head_
      &*& node(head_, vs);
@*/

impl<T> Stack<T> {

    //@ req true;
    //@ ens stack<T>(?stack, nil);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        //@ close node(std::ptr::null_mut(), nil);
        //@ close stack<T>(stack, nil);
        stack
    }
    
    //@ req stack<T>(stack, ?vs);
    //@ ens stack<T>(stack, cons(value, vs));
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ open stack<T>(stack, vs);
        //@ open node((*stack).head, vs);
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        //@ close node(n, cons(value, vs));
        //@ close stack<T>(stack, cons(value, vs));
    }
    
    //@ req stack<T>(stack, ?vs);
    //@ ens stack<T>(stack, vs);
    //@ ensures result == (vs == nil);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open stack<T>(stack, vs);
        let head = (*stack).head;
        //@ open node(head, vs);
        
        let result = head.is_null();
        //@ close node(head, vs);
        //@ close stack<T>(stack, vs);
        result
    }
    
    //@ req stack<T>(stack, ?vs) &*& vs == cons(?v, ?vs_tail);
    //@ ensures stack<T>(stack, vs_tail);
    //@ ensures result == v;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open stack<T>(stack, vs);
        //@ open node((*stack).head, vs);
        
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack<T>(stack, vs_tail);
        result
    }

    //@ req stack<T>(stack, ?vs);
    //@ ensures true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open stack<T>(stack, vs);
        //@ open node((*stack).head, vs);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

unsafe fn input_char() -> char
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32
{
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32)
{
    println!("{}", value);
}

struct Vector {
    x: i32,
    y: i32,
}

/*@ predicate vector(Vector* v, i32 x, i32 y) =
      v->x |-> x &*& v->y |-> y;
@*/

impl Vector {

    //@ req true;
    //@ ensures vector(result, x, y);
    unsafe fn create(x: i32, y: i32) -> *mut Vector
    {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close vector(result, x, y);
        result
    }
    
}

fn main()
{
    unsafe {
        let s = Stack::create();
        
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
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);
                    let sum = Vector::create((*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command")
            }
        }
    }
}