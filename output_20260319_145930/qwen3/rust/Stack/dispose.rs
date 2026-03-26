/*@ pred node(n: *mut Node; next: *mut Node, value: i32) = 
    n != 0 &*& 
    alloc_block_(n as *u8, std::mem::size_of::<Node>()) &*& 
    struct_Node_padding(n) &*& 
    (*n).next |-> next &*& 
    (*n).value |-> value;
@*/

/*@ pred stack(s: *mut Stack; head: *mut Node) = 
    s != 0 &*& 
    alloc_block_(s as *u8, std::mem::size_of::<Stack>()) &*& 
    struct_Stack_padding(s) &*& 
    (*s).head |-> head;
@*/

/*@ pred nodes(n: *mut Node; vs: list<i32>) = 
    match vs {
        nil => n == 0,
        cons(v, vs0) => 
            node(n, ?next, v) &*& nodes(next, vs0)
    };
@*/

unsafe fn dispose_nodes(n: *mut Node)
//@ req nodes(n, ?vs); ens true;
{
    
    if !n.is_null() {
        //@ open nodes(n, _);
        //@ let next = (*n).next;
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true; ens stack(result, 0);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, 0);
        return stack;
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
    //@ req stack(stack, ?head); ens stack(stack, head) &*& result == (head == 0);
    {
        
        let head = (*stack).head;
        
        let result = (*stack).head.is_null();
        
        
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?old_head) &*& nodes(old_head, ?vs); 
    //@ ens stack(stack, ?new_head) &*& nodes(new_head, cons(value, vs));
    {
        
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, old_head, value);
        (*stack).head = n;
        //@ close stack(stack, n);
        
        
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?old_head) &*& old_head != 0 &*& nodes(old_head, cons(?v, ?vs)); 
    //@ ens stack(stack, ?new_head) &*& nodes(new_head, vs) &*& result == v;
    {
        
        let head = (*stack).head;
        //@ open stack(stack, _);
        //@ open nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, (*stack).head);
        return result;
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?head) &*& nodes(head, ?vs); ens true;
    {
        
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
//@ req true; ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}