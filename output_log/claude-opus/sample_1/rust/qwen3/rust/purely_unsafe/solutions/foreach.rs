use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node<T> {
    value: T,
    next: *mut Node<T>,
}

struct Stack<T> {
    head: *mut Node<T>,
}

struct Vector {
    x: i32,
    y: i32,
}

/*@
pred NodePred<T>(ptr: *mut Node<T>; value: T, next: *mut Node<T>) =
    (*ptr).value |-> value &*& (*ptr).next |-> next &*& alloc_block(ptr as *mut u8, Layout::new_::<Node<T>>());

pred Nodes<T>(head: *mut Node<T>; nodes: list<*mut Node<T>>) =
    if head == std::ptr::null_mut() {
        nodes == nil
    } else {
        NodePred(head, ?v, ?next) &*& Nodes(next, ?tail) &*& nodes == cons(head, tail)
    };

pred StackPred<T>(ptr: *mut Stack<T>; nodes: list<*mut Node<T>>) =
    (*ptr).head |-> ?head &*& alloc_block(ptr as *mut u8, Layout::new_::<Stack<T>>()) &*& Nodes(head, nodes);

pred VectorPred(ptr: *mut Vector; x: i32, y: i32) =
    (*ptr).x |-> x &*& (*ptr).y |-> y &*& alloc_block(ptr as *mut u8, Layout::new_::<Vector>());
@*/

impl<T> Stack<T> {
    #[requires(alloc_block_cap(Layout::new_::<Stack<T>>()))]
    #[ensures(StackPred::<T>(result, nil))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ open alloc_block(stack as *mut u8, Layout::new_::<Stack<T>>());
        (*stack).head = std::ptr::null_mut();
        //@ close alloc_block(stack as *mut u8, Layout::new_::<Stack<T>>());
        //@ close Nodes::<T>(std::ptr::null_mut(), nil);
        //@ close StackPred::<T>(stack, nil);
        stack
    }

    #[requires(StackPred::<T>(stack, ?nodes) &*& alloc_block_cap(Layout::new_::<Node<T>>()))]
    #[ensures(StackPred::<T>(stack, cons(?n, nodes)))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        //@ open StackPred::<T>(stack, nodes);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        //@ open alloc_block(n as *mut u8, Layout::new_::<Node<T>>());
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        //@ close alloc_block(n as *mut u8, Layout::new_::<Node<T>>());
        //@ close NodePred::<T>(n, value, old((*stack).head));
        //@ close Nodes::<T>(n, cons(n, nodes));
        (*stack).head = n;
        //@ close StackPred::<T>(stack, cons(n, nodes));
    }

    #[requires(StackPred::<T>(stack, ?nodes))]
    #[ensures(StackPred::<T>(stack, nodes) &*& result == (nodes == nil))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        //@ open StackPred::<T>(stack, nodes);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, nodes);
        let result = head.is_null();
        //@ close Nodes::<T>(head, nodes);
        //@ close StackPred::<T>(stack, nodes);
        result
    }

    #[requires(StackPred::<T>(stack, ?nodes) &*& nodes != nil)]
    #[ensures(StackPred::<T>(stack, tail(nodes)) &*& result == ?v)]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        //@ open StackPred::<T>(stack, nodes);
        let head = (*stack).head;
        //@ open Nodes::<T>(head, nodes);
        //@ open NodePred::<T>(head, ?v, ?next);
        //@ open alloc_block(head as *mut u8, Layout::new_::<Node<T>>());
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        //@ close alloc_block(head as *mut u8, Layout::new_::<Node<T>>());
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close StackPred::<T>(stack, tail(nodes));
        result
    }

    #[requires(StackPred::<T>(stack, nil))]
    #[ensures(alloc_block_cap(Layout::new_::<Stack<T>>()))]
    unsafe fn dispose(stack: *mut Stack<T>) {
        //@ open StackPred::<T>(stack, nil);
        //@ open Nodes::<T>(_, nil);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

/*@
pred input_char_io() = true;
pred input_i32_io() = true;
pred output_i32_io() = true;
@*/

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

impl Vector {
    #[requires(alloc_block_cap(Layout::new_::<Vector>()))]
    #[ensures(VectorPred(result, x, y))]
    unsafe fn create(x: i32, y: i32) -> *mut Vector {
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        //@ open alloc_block(result as *mut u8, Layout::new_::<Vector>());
        (*result).x = x;
        (*result).y = y;
        //@ close alloc_block(result as *mut u8, Layout::new_::<Vector>());
        //@ close VectorPred(result, x, y);
        result
    }
}

/*@
pred StackWithVectors(stack: *mut Stack<*mut Vector>, nodes: list<*mut Node<*mut Vector>>) =
    StackPred::<*mut Vector>(stack, nodes) &*& VectorNodes(nodes);

pred VectorNodes(nodes: list<*mut Node<*mut Vector>>) =
    match nodes {
        nil => true,
        cons(h, t) => VectorNodes(t)
    };
@*/

#[requires(true)]
#[ensures(false)]
fn main() {
    unsafe {
        //@ assume(alloc_block_cap(Layout::new_::<Stack<*mut Vector>>()));
        let s = Stack::create();

        loop {
            //@ invariant StackPred::<*mut Vector>(s, ?nodes);
            let cmd = input_char();
            match cmd {
                'p' => {
                    let x = input_i32();
                    let y = input_i32();
                    //@ assume(alloc_block_cap(Layout::new_::<Vector>()));
                    let v = Vector::create(x, y);
                    //@ leak VectorPred(v, x, y);
                    //@ assume(alloc_block_cap(Layout::new_::<Node<*mut Vector>>()));
                    Stack::push(s, v);
                }
                '+' => {
                    //@ assume(nodes != nil);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v1 = Stack::pop(s);

                    //@ assume(tail(nodes) != nil);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v2 = Stack::pop(s);

                    //@ assume(VectorPred(v1, ?x1, ?y1));
                    //@ assume(VectorPred(v2, ?x2, ?y2));
                    //@ open VectorPred(v1, x1, y1);
                    //@ open alloc_block(v1 as *mut u8, Layout::new_::<Vector>());
                    let v1x = (*v1).x;
                    let v1y = (*v1).y;
                    //@ close alloc_block(v1 as *mut u8, Layout::new_::<Vector>());
                    //@ open VectorPred(v2, x2, y2);
                    //@ open alloc_block(v2 as *mut u8, Layout::new_::<Vector>());
                    let v2x = (*v2).x;
                    let v2y = (*v2).y;
                    //@ close alloc_block(v2 as *mut u8, Layout::new_::<Vector>());
                    //@ assume(alloc_block_cap(Layout::new_::<Vector>()));
                    let sum = Vector::create(v1x + v2x, v1y + v2y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    //@ leak VectorPred(sum, _, _);
                    //@ assume(alloc_block_cap(Layout::new_::<Node<*mut Vector>>()));
                    Stack::push(s, sum);
                }
                '=' => {
                    //@ assume(nodes != nil);
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);

                    //@ assume(VectorPred(v_, ?vx, ?vy));
                    //@ open VectorPred(v_, vx, vy);
                    //@ open alloc_block(v_ as *mut u8, Layout::new_::<Vector>());
                    output_i32((*v_).x);
                    output_i32((*v_).y);
                    //@ close alloc_block(v_ as *mut u8, Layout::new_::<Vector>());
                    dealloc(v_ as *mut u8, Layout::new::<Vector>());
                }
                _ => panic!("Bad command"),
            }
        }
    }
}