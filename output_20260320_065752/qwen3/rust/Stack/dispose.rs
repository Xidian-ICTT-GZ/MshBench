/*@ pred node(n: *mut Node, next: *mut Node, value: i32) = 
    n != 0 as *mut Node &*& 
    alloc_block_n(n as *u8, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

/*@ pred stack(s: *mut Stack, head: *mut Node) = 
    s != 0 as *mut Stack &*& 
    alloc_block_n(s as *u8, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> head;
@*/

/*@ pred nodes(n: *mut Node) =
    n == 0 as *mut Node ? true :
    node(n, ?next, ?val) &*& nodes(next);
@*/

//@ req true;
//@ ens true;
fn main()
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

impl Stack {

    //@ req true;
    //@ ens stack(result, 0 as *mut Node);
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack, 0 as *mut Node);
        (*stack).head = std::ptr::null_mut();
        return stack;
    }
    
    //@ req stack(stack, ?head);
    //@ ens stack(stack, head) &*& result == (head == 0 as *mut Node);
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        return result;
    }

    //@ req stack(stack, ?old_head) &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head) &*& new_head != 0 as *mut Node;
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(n, old_head, value);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close nodes(n);
    }

    //@ req stack(stack, ?old_head) &*& old_head != 0 as *mut Node &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head) &*& result == ?val;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        //@ open nodes(head);
        //@ open node(head, ?next, ?val);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }
    
    //@ req stack(stack, ?head) &*& nodes(head);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node)
{
    if !n.is_null() {
        //@ open nodes(n);
        //@ open node(n, ?next, ?val);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}