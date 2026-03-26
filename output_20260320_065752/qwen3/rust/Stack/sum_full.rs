/*@ pred node(node: *mut Node, next: *mut Node, value: i32) = 
    alloc_block_Node(node) &*& 
    struct_Node_padding(node) &*& 
    (*node).next |-> next &*& 
    (*node).value |-> value;
@*/

/*@ pred stack(stack: *mut Stack, head: *mut Node) = 
    alloc_block_Stack(stack) &*& 
    struct_Stack_padding(stack) &*& 
    (*stack).head |-> head;
@*/

/*@ pred nodes(head: *mut Node; values: list<i32>) =
    match values {
        nil => head == null,
        cons(hd, tl) => 
            node(head, ?next, hd) &*& nodes(next, tl)
    };
@*/

unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req nodes(node, ?vs);
//@ ens nodes(node, vs) &*& result == sum(vs);
{
    
    let mut result = 0;
    if !node.is_null() {
        //@ open nodes(node, _);
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
        //@ close nodes(node, cons((*node).value, _));
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, null) &*& nodes(null, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, null);
        //@ close nodes(null, nil);
        
        stack
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
    //@ req stack(stack, ?head) &*& nodes(head, ?vs);
    //@ ens stack(stack, head) &*& nodes(head, vs) &*& result == sum(vs);
    {
        
        let result = get_nodes_sum((*stack).head);
        
        result
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
        //@ close nodes(n, cons(value, vs));
        
        
    }
    
    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, ?head) &*& head != null &*& nodes(head, cons(?hd, ?tl));
    //@ ens stack(stack, ?new_head) &*& nodes(new_head, tl) &*& result == hd;
    {
        
        let head = (*stack).head;
        //@ open nodes(head, _);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        result
    }

    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, ?head) &*& nodes(head, nil);
    //@ ens true;
    {
        //@ open stack(stack, _);
        //@ open nodes(null, nil);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main()
//@ req true;
//@ ens true;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let sum = Stack::get_sum(s);
        
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}