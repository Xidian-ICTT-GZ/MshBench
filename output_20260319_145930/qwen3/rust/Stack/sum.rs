/*@ pred node(node: *mut Node, next: *mut Node, value: i32) =
    alloc_block_(node as *u8, std::mem::size_of::<Node>()) &*& 
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

/*@ pred stack(stack: *mut Stack, head: *mut Node) =
    alloc_block_(stack as *u8, std::mem::size_of::<Stack>()) &*& 
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

/*@ pred nodes(head: *mut Node, values: list<i32>) =
    head == std::ptr::null_mut() ?
        values == nil
    :
        exists(next: *mut Node, v: i32).
        node(head, next, v) &*& nodes(next, vs) &*& values == cons(v, vs);
@*/

//@ req true;
//@ ens true;
unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
{
    //@ open nodes(nodes, _);
    let mut result = 0;
    
    if !nodes.is_null() {
        //@ assert node(nodes, ?next, ?v) &*& nodes(next, ?vs);
        result = get_nodes_sum((*nodes).next);
        //@ close nodes(nodes, cons(v, vs));
        result += (*nodes).value;
    }
    else {
        //@ close nodes(nodes, nil);
    }
    
    result
}

impl Stack {

    //@ req true;
    //@ ens stack(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, std::ptr::null_mut());
        
        stack
    }
    
    //@ req stack(stack, ?head);
    //@ ens stack(stack, head) &*& result == (head == std::ptr::null_mut());
    unsafe fn is_empty(stack: *mut Stack) -> bool
    {
        //@ open stack(stack, head);
        let head = (*stack).head;
        //@ close stack(stack, head);
        
        let result = (*stack).head.is_null();
        
        
        result
    }
    
    //@ req stack(stack, ?head) &*& nodes(head, ?values);
    //@ ens stack(stack, head) &*& nodes(head, values) &*& result == sum(values);
    unsafe fn get_sum(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, head);
        let result = get_nodes_sum((*stack).head);
        //@ close stack(stack, head);
        
        result
    }

    //@ req stack(stack, ?old_head) &*& nodes(old_head, ?old_values);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head, cons(value, old_values));
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        //@ open stack(stack, old_head);
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

    //@ req stack(stack, ?old_head) &*& old_head != std::ptr::null_mut() &*& nodes(old_head, cons(?v, ?vs));
    //@ ens stack(stack, ?new_head) &*& nodes(new_head, vs) &*& result == v;
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        //@ open stack(stack, old_head);
        //@ open nodes(old_head, _);
        let head = (*stack).head;
        
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open node(head, ?next, result);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        
        result
    }
    
    //@ req stack(stack, ?head) &*& nodes(head, _);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack)
    {
        //@ open stack(stack, head);
        let mut n = (*stack).head;
        //@ open nodes(n, _);
        loop {
            //@ inv nodes(n, _) &*& stack(stack, n);
            if n.is_null() {
                break;
            }
            
            //@ open nodes(n, _);
            //@ open node(n, ?next, _);
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            n = next;
            //@ close stack(stack, n);
        }
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}