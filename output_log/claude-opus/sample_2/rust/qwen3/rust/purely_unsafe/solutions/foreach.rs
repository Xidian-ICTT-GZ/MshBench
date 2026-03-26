use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
struct NodePred<T>(ptr: *mut Node<T>, value: T, next: *mut Node<T>) = 
    ptr |-> Node { value: v, next: n } &*& v == value &*& n == next;

#[pred]
struct StackPred<T>(ptr: *mut Stack<T>, nodes: list<*mut Node<T>>) =
    ptr |-> Stack { head: head_ptr } &*& nodes == nil ? head_ptr == std::ptr::null_mut() : head_ptr == hd(nodes) &*& nodes_pred(nodes);

fixpoint bool nodes_pred<T>(list<*mut Node<T>> nodes) {
    switch(nodes) {
        case nil: return true;
        case cons(h, t): return NodePred(h, _, _) &*& nodes_pred(t) &*& 
                          h != std::ptr::null_mut() &*& (t == nil || h != hd(t));
    }
}

#[pred]
struct VectorPred(ptr: *mut Vector, x: i32, y: i32) =
    ptr |-> Vector { x: px, y: py } &*& px == x &*& py == y;

impl<T> Stack<T> {
    #[requires(alloc_cap(1))]
    #[ensures(result != std::ptr::null_mut() && StackPred(result, nil))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(StackPred(stack, nodes) &*& alloc_cap(1))]
    #[ensures(StackPred(stack, cons(n, nodes)) &*& NodePred(n, value, old((*stack).head)))]
    unsafe fn push(stack: *mut Stack<T>, value: T) {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
    }

    #[requires(StackPred(stack, nodes))]
    #[ensures(result == (nodes == nil))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool {
        let head = (*stack).head;

        let result = head.is_null();

        result
    }

    #[requires(StackPred(stack, cons(h, tail)) &*& NodePred(h, v, next))]
    #[ensures(StackPred(stack, tail) &*& v == result)]
    unsafe fn pop(stack: *mut Stack<T>) -> T {
        let head = (*stack).head;

        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();

        dealloc(head as *mut u8, Layout::new::<Node<T>>());

        result
    }

    #[requires(StackPred(stack, nodes) &*& nodes == nil)]
    #[ensures(alloc_cap(1))]
    unsafe fn dispose(stack: *mut Stack<T>) {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }
}

unsafe fn input_char() -> char {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.chars().next().unwrap()
}

unsafe fn input_i32() -> i32 {
    let mut line = String::new();
    std::io::stdin().read_line(&mut line).unwrap();
    line.trim().parse().unwrap()
}

unsafe fn output_i32(value: i32) {
    println!("{}", value);
}

impl Vector {
    #[requires(alloc_cap(1))]
    #[ensures(result != std::ptr::null_mut() &*& VectorPred(result, x, y))]
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

#[lemma]
fn node_pred_disjoint<T>(p1: *mut Node<T>, p2: *mut Node<T>)
    requires NodePred(p1, _, _) &*& NodePred(p2, _, _)
    ensures p1 != p2 ==> disjoint(p1, p2)
{
}

#[lemma]
fn stack_pred_valid<T>(stack: *mut Stack<T>, nodes: list<*mut Node<T>>)
    requires StackPred(stack, nodes)
    ensures stack != std::ptr::null_mut() &*& 
            (*stack).head == (nodes == nil ? std::ptr::null_mut() : hd(nodes))
{
}

#[lemma]
fn vector_pred_disjoint(p1: *mut Vector, p2: *mut Vector)
    requires VectorPred(p1, _, _) &*& VectorPred(p2, _, _)
    ensures p1 != p2 ==> disjoint(p1, p2)
{
}

fn main() {
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
                _ => panic!("Bad command"),
            }
        }
    }
}