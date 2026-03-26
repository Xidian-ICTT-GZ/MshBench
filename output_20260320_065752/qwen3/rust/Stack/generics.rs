/*@ pred node<T>(n: *mut Node<T>, next: *mut Node<T>, value: T) = 
    n != 0 as *mut Node<T> &*& 
    alloc_block(n as *u8, std::mem::size_of::<Node<T>>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

/*@ pred stack<T>(s: *mut Stack<T>) =
    s != 0 as *mut Stack<T> &*&
    alloc_block(s as *u8, std::mem::size_of::<Stack<T>>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    stack_nodes(head);
@*/

/*@ pred stack_nodes<T>(n: *mut Node<T>) =
    n == 0 as *mut Node<T> ?
        true
    :
        node(n, ?next, ?value) &*& stack_nodes(next);
@*/

/*@ pred point(p: *mut Point, x: i32, y: i32) =
    p != 0 as *mut Point &*&
    alloc_block(p as *u8, std::mem::size_of::<Point>()) &*&
    struct_Point_padding(p) &*&
    (*p).x |-> x &*&
    (*p).y |-> y;
@*/

impl<T> Stack<T> {

    //@ req true;
    //@ ens stack(result);
    unsafe fn create() -> *mut Stack<T>
    {
        let stack = alloc(Layout::new::<Stack<T>>()) as *mut Stack<T>;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack<T>>());
        }
        //@ close stack_nodes(0 as *mut Node<T>);
        //@ close stack(stack);
        (*stack).head = std::ptr::null_mut();
        stack
    }
    
    //@ req stack(stack) &*& stack_nodes(?old_head) &*& stack_nodes(old_head) &*& stack(stack) &*& true;
    //@ ens stack(stack);
    unsafe fn push(stack: *mut Stack<T>, value: T)
    {
        //@ open stack(stack);
        let old_head = (*stack).head;
        //@ open stack_nodes(old_head);
        let n = alloc(Layout::new::<Node<T>>()) as *mut Node<T>;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node<T>>());
        }
        (*n).next = old_head;
        (&raw mut (*n).value).write(value);
        //@ close node(n, old_head, value);
        //@ close stack_nodes(n);
        (*stack).head = n;
        //@ close stack(stack);
    }
    
    //@ req stack(stack);
    //@ ens stack(stack) &*& result == ((*stack).head == 0 as *mut Node<T>);
    unsafe fn is_empty(stack: *mut Stack<T>) -> bool
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ close stack(stack);
        let result = head.is_null();
        result
    }
    
    //@ req stack(stack) &*& (*stack).head != 0 as *mut Node<T>;
    //@ ens stack(stack) &*& result == ?v;
    unsafe fn pop(stack: *mut Stack<T>) -> T
    {
        //@ open stack(stack);
        let head = (*stack).head;
        //@ open stack_nodes(head);
        //@ open node(head, ?next, ?value);
        (*stack).head = next;
        let result = (&raw mut (*head).value).read();
        dealloc(head as *mut u8, Layout::new::<Node<T>>());
        //@ close stack_nodes(next);
        //@ close stack(stack);
        result
    }

    //@ req stack(stack);
    //@ ens stack(stack);
    unsafe fn reverse(stack: *mut Stack<T>)
    {
        //@ open stack(stack);
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close stack_nodes(m);
        //@ inv stack_nodes(n) &*& stack_nodes(m) &*& (*stack).head |-> ?orig_head &*& stack_nodes(orig_head);
        loop {
            if n.is_null() {
                break;
            }
            //@ open stack_nodes(n);
            //@ open node(n, ?next, ?value);
            let next = (*n).next;
            (*n).next = m;
            //@ close node(n, m, value);
            //@ close stack_nodes(n);
            m = n;
            n = next;
        }
        (*stack).head = m;
        //@ close stack(stack);
    }

    //@ req stack(stack);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack<T>)
    {
        //@ open stack(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack<T>>());
    }

}

impl Point {

    //@ req true;
    //@ ens point(result, x, y);
    unsafe fn create(x: i32, y: i32) -> *mut Point
    {
        let result = alloc(Layout::new::<Point>()) as *mut Point;
        if result.is_null() {
            handle_alloc_error(Layout::new::<Point>());
        }
        (*result).x = x;
        (*result).y = y;
        //@ close point(result, x, y);
        result
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