use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node<T> {
    next: *mut Node<T>,
    value: T,
}

struct Stack<T> {
    head: *mut Node<T>,
}

//@ pred node<T>(n: *mut Node<T>, next: *mut Node<T>, v: T) = n as *mut u8 |-> ?b &*& struct_Node_padding(b) &*& [?f]std::ptr::raw_ptr_field::<*mut Node<T>>(b, 0, next) &*& [?g]std::ptr::raw_ptr_field::<T>(b, 1, v) &*& std::mem::size_of::<Node<T>>() == std::mem::size_of::<*mut Node<T>>() + std::mem::size_of::<T>() + ?pad &*& pad >= 0;

//@ pred stack<T>(s: *mut Stack<T>, head: *mut Node<T>) = s as *mut u8 |-> ?b &*& struct_Stack_padding(b) &*& [?f]std::ptr::raw_ptr_field::<*mut Node<T>>(b, 0, head) &*& std::mem::size_of::<Stack<T>>() == std::mem::size_of::<*mut Node<T>>() + ?pad &*& pad >= 0;

//@ pred point(p: *mut Point, x: i32, y: i32) = p as *mut u8 |-> ?b &*& struct_Point_padding(b) &*& [?f]std::ptr::raw_i32_field(b, 0, x) &*& [?g]std::ptr::raw_i32_field(b, 1, y) &*& std::mem::size_of::<Point>() == 8 + ?pad &*& pad >= 0;

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
        //@ open stack(stack, head);
        
        let head = (*stack).head;
        
        let result = head.is_null();
        
        //@ close stack(stack, head);
        result
        //@ ens stack(stack, ?head_) &*& result == (head_ == std::ptr::null_mut::<Node<T>>());
    }
    
    unsafe fn pop(stack: *mut Stack<T>) -> T
    
    
    {
        //@ req stack(stack, ?old_head) &*& old_head != std::ptr::null_mut() &*& node(old_head, ?next, ?v);
        //@ open stack(stack, old_head);
        //@ open node(old_head, next, v);
        
        let head = (*stack).head;
        
        (*stack).head = (*head).next;
        let result = (&raw mut (*head).value).read();
        
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        
        //@ close stack(stack, next);
        result
        //@ ens stack(stack, ?new_head) &*& result == v;
    }

    unsafe fn reverse(stack: *mut Stack<T>)
    
    
    {
        //@ req stack(stack, ?orig_head);
        //@ open stack(stack, orig_head);
        
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        
        //@ let orig_n = n;
        //@ let orig_m = m;
        //@ loop_inv stack_nodes(n, ?nodes_n) &*& stack_nodes(m, ?nodes_m) &*& append(nodes_m, nodes_n) == ?all_nodes &*& all_nodes == list_from_ptr(orig_head);
        
        loop {
            
            
            if n.is_null() {
                break;
            }
            //@ open stack_nodes(n, ?nodes_n_);
            let next = (*n).next;
            
            (*n).next = m;
            //@ close stack_nodes(n, cons(n, nodes_m));
            m = n;
            n = next;
            
            
        }
        (*stack).head = m;
        //@ close stack(stack, m);
        
        //@ ens stack(stack, ?new_head) &*& stack_nodes(new_head, reverse(list_from_ptr(orig_head)));
    }

    unsafe fn dispose(stack: *mut Stack<T>)
    
    
    {
        //@ req stack(stack, _);
        //@ open stack(stack, _);
        
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
        //@ ens true;
    }

}

//@ fixpoint list<*mut Node<T>> list_from_ptr(*mut Node<T> p);
//@ fixpoint bool stack_nodes(*mut Node<T> p, list<*mut Node<T>> nodes);

//@ lemma void stack_nodes_nil()
//@ req stack_nodes(std::ptr::null_mut(), ?nodes);
//@ ens nodes == nil;

//@ lemma void stack_nodes_cons()
//@ req stack_nodes(?p, ?nodes) &*& p != std::ptr::null_mut() &*& node(p, ?next, _);
//@ ens nodes == cons(p, ?rest) &*& stack_nodes(next, rest);

//@ predicate_family stack_nodes(*mut Node<T>, list<*mut Node<T>>);
//@ predicate_family_instance stack_nodes(std::ptr::null_mut(), nil) = true;
//@ predicate_family_instance stack_nodes(p, cons(p, rest)) = p != std::ptr::null_mut() &*& node(p, ?next, _) &*& stack_nodes(next, rest);

//@ fixpoint list<T> reverse<T>(list<T> l);
//@ fixpoint list<T> append<T>(list<T> xs, list<T> ys);

struct Point {
    x: i32,
    y: i32,
}

impl Point {

    unsafe fn create(x: i32, y: i32) -> *mut Point
    
    
    {
        //@ req true;
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close point(result, x, y);
        result
        //@ ens point(result, x, y);
    }
    
}

fn main()

{
    unsafe {
        let s = Stack::create();
        let p1 = Point::create(10, 0);
        let p2 = Point::create(0, 10);
        Stack::push(s, p1);
        Stack::push(s, p2);
        Stack::reverse(s);
        std::hint::assert_unchecked(Stack::pop(s) == p1);
        std::hint::assert_unchecked(Stack::pop(s) == p2);
        Stack::dispose(s);
        dealloc(p1 as *mut u8, Layout::new::<Point>());
        dealloc(p2 as *mut u8, Layout::new::<Point>());
    }
}