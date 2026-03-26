use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node<T>(n: *mut Node<T>, value: T, next: *mut Node<T>) = n |-> Node { next: next, value: value };
predicate stack<T>(s: *mut Stack<T>, contents: list<*mut Node<T>>, values: list<T>) =
    s |-> Stack { head: (if contents == nil then std::ptr::null_mut() else head(contents)) }
    &*& nodes_chain(contents, values);

fixpoint bool is_null<T>(T* p) { p == std::ptr::null_mut() }

fixpoint list<*mut Node<T>> tail_list<T>(list<*mut Node<T>> l) {
    switch(l) {
        case nil: nil
        case cons(h, t): t
    }
}

fixpoint list<T> tail_list_values<T>(list<T> l) {
    switch(l) {
        case nil: nil
        case cons(h, t): t
    }
}

predicate nodes_chain<T>(list<*mut Node<T>> ns, list<T> vs) =
    switch(ns) {
        case nil: switch (vs) { case nil: emp case cons(_, _) : false }
        case cons(n, ns0): switch(vs) {
            case nil: false
            case cons(v, vs0): node(n, v, (if ns0 == nil then std::ptr::null_mut() else head(ns0)) ) &*& nodes_chain(ns0, vs0)
        }
    };

lemma void nodes_chain_head<T>(list<*mut Node<T>> ns, list<T> vs)
    requires nodes_chain(ns, vs);
    ensures ns != nil ==> node(head(ns), head(vs), (if tail(ns) == nil then std::ptr::null_mut() else head(tail(ns)))) &*& nodes_chain(tail(ns), tail(vs));
{
    switch(ns) {
        case nil: return;
        case cons(h, t): switch(vs) {
            case nil: return;
            case cons(hv, tv): return;
        }
    }
}

impl<T> Stack<T> {

    #[requires(true)]
    #[ensures(stack(result, nil, nil))]
    unsafe fn create() -> *mut Stack<T> {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        (*stack).head = std::ptr::null_mut();
        
        stack
    }
    
    #[requires(stack(stack, contents, values))]
    #[ensures(stack(stack, cons(n, contents), cons(value, values)) &*& node(n, value, (if contents == nil then std::ptr::null_mut() else head(contents)) ))]
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = (*stack).head;
        (&raw mut (*n).value).write(value);
        (*stack).head = n;
        
    }
    
    #[requires(stack(stack, contents, values))]
    #[ensures(result == true &*& contents == nil &*& stack(stack, contents, values)
        || result == false &*& contents != nil &*& stack(stack, contents, values))]
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        let head = (*stack).head;
        
        let result = head.is_null();
        
        result
    }
    
    #[requires(stack(stack, cons(h, t), cons(v, vs)) &*& node(h, v, (if t == nil then std::ptr::null_mut() else head(t))) )]
    #[ensures(stack(stack, t, vs))]
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        let head = (*stack).head;
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        result
    }

    #[requires(stack(stack, contents, values))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

predicate vector(v: *mut Vector, x: int, y: int) = v |-> Vector { x: x, y: y };

impl Vector {

    #[requires(x*x + y*y <= limit*limit)]
    #[ensures(vector(result, x, y))]
    unsafe fn create(limit: i32, x: i32, y: i32) -> *mut Vector
    {
        assert!(x * x + y * y <= limit * limit, "Vector too big");
        let result = alloc(Layout::new::<Vector>()) as *mut Vector;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Vector>());
        }
        (*result).x = x;
        (*result).y = y;
        
        result
    }
    
}

fn main()
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
                    
                    
                    let sum = Vector::create(limit, (*v1).x + (*v2).x, (*v1).y + (*v2).y);
                    dealloc(v1 as *mut u8, Layout::new::<Vector>());
                    dealloc(v2 as *mut u8, Layout::new::<Vector>());
                    Stack::push(s, sum);
                    
                }
                '=' => {
                    assert!(!Stack::is_empty(s), "Stack underflow");
                    let v_ = Stack::pop(s);
                    
                    
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