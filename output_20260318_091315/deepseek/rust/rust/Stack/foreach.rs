use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

#[predicate]
fn stack_nodes<T>(head: *mut Node<T>) -> bool {
    pearlite! {{
        if head.is_null() {
            true
        } else {
            exists!((next: *mut Node<T>) => head->next |-> next) &&
            exists!((value: T) => head->value |-> value) &&
            stack_nodes(next)
        }
    }}
}

#[predicate]
fn stack<T>(stack: *mut Stack<T>) -> bool {
    pearlite! {{
        exists!((head: *mut Node<T>) => stack->head |-> head) &&
        stack_nodes(head)
    }}
}

#[predicate]
fn vector(v: *mut Vector) -> bool {
    pearlite! {{
        exists!((x: i32, y: i32) => v->x |-> x && v->y |-> y)
    }}
}

#[predicate]
fn node_with_vector<T>(n: *mut Node<T>) -> bool {
    pearlite! {{
        exists!((next: *mut Node<T>) => n->next |-> next) &&
        exists!((value: *mut Vector) => n->value |-> value) &&
        vector(value)
    }}
}

#[predicate]
fn stack_nodes_with_vectors<T>(head: *mut Node<T>) -> bool {
    pearlite! {{
        if head.is_null() {
            true
        } else {
            node_with_vector(head) &&
            exists!((next: *mut Node<T>) => head->next |-> next) &&
            stack_nodes_with_vectors(next)
        }
    }}
}

#[predicate]
fn stack_with_vectors<T>(stack: *mut Stack<T>) -> bool {
    pearlite! {{
        exists!((head: *mut Node<T>) => stack->head |-> head) &&
        stack_nodes_with_vectors(head)
    }}
}

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    #[requires(stack(stack))]
    #[requires(exists!((value: T) => true))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }
    
    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    #[ensures(result == pearlite! {(*stack).head.is_null()})]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;
        let result = head.is_null();
        result
    }
    
    #[requires(stack(stack))]
    #[requires(!(*stack).head.is_null())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        result
    }

    #[requires(stack(stack))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>) {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

#[requires(true)]
#[ensures(true)]
unsafe fn input_char() -> char {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

#[requires(true)]
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
    #[requires(true)]
    #[ensures(vector(result))]
    unsafe fn create(x: i32, y: i32) -> *mut Vector {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        result
    }
}

fn main() {
    unsafe {
        let s = Stack::create();
        
        #[invariant(stack_with_vectors(s))]
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