use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

/*@
pred Stack_own<T>(s: *mut Stack<T>; head: *mut Node<T>) =
    (*s).head |-> head;

pred Node_own<T>(n: *mut Node<T>; next: *mut Node<T>, value: T) =
    (*n).next |-> next &*& (*n).value |-> value;

pred Nodes<T>(head: *mut Node<T>;) =
    head == 0 ?
        emp
    :
        Node_own(head, ?next, ?value) &*& Nodes(next);
@*/

impl<T> Stack<T> {
    #[requires(true)]
    #[ensures(Stack_own::<T>(result, 0))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(Stack_own::<T>(stack, ?head) &*& Nodes::<T>(head))]
    #[ensures(Stack_own::<T>(stack, ?new_head) &*& Nodes::<T>(new_head))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(Stack_own::<T>(stack, ?head) &*& Nodes::<T>(head))]
    #[ensures(Stack_own::<T>(stack, head) &*& Nodes::<T>(head) &*& (result == (head == 0)))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(Stack_own::<T>(stack, ?head) &*& head != 0 &*& Nodes::<T>(head))]
    #[ensures(Stack_own::<T>(stack, ?new_head) &*& Nodes::<T>(new_head))]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(Stack_own::<T>(stack, ?head) &*& head == 0)]
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

/*@
pred Vector_own(v: *mut Vector; x: i32, y: i32) =
    (*v).x |-> x &*& (*v).y |-> y;
@*/

impl Vector {
    #[requires(true)]
    #[ensures(Vector_own(result, x, y))]
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

/*@
pred Vectors(head: *mut Node<*mut Vector>;) =
    head == 0 ?
        emp
    :
        Node_own::<*mut Vector>(head, ?next, ?v) &*& Vector_own(v, _, _) &*& Vectors(next);
@*/

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let s = Stack::create();

        loop {
            //@ inv Stack_own::<*mut Vector>(s, ?head) &*& Vectors(head);
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
                _ => panic!("Bad command"),
            }
        }
    }
}