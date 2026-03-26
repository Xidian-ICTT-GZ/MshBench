/*@ pred node(n: *mut Node, next: *mut Node, value: i32) =
    alloc_block_n((n as *u8), std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;
@*/

/*@ pred stack(s: *mut Stack, head: *mut Node) =
    alloc_block_n((s as *u8), std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> head;
@*/

/*@ pred nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        node(n, ?next, ?value) &*& nodes(next);
@*/

//@ req true;
//@ ens true;
fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}

//@ req true;
//@ ens nodes(result);
unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

impl Stack {

    //@ req true;
    //@ ens stack(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack, std::ptr::null_mut());
        (*stack).head = std::ptr::null_mut();
        stack
    }

    //@ req stack(stack, ?old_head) &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head);
    unsafe fn push(stack: *mut Stack, value: i32) {
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

    //@ req stack(stack, ?old_head) &*& old_head != std::ptr::null_mut() &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head) &*& result == ?val;
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open stack(stack, old_head);
        //@ open nodes(old_head);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open node(head, ?next, result);
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        result
    }

    //@ req stack(stack, ?head) &*& nodes(head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        //@ open stack(stack, head);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close stack(stack, ?new_head);
    }

    //@ req stack(stack, ?head) &*& nodes(head);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack, head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

//@ req *n |-> ?node_ptr &*& nodes(node_ptr);
//@ ens *n |-> ?new_node_ptr &*& nodes(new_node_ptr);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    if !(*n).is_null() {
        //@ open nodes(*n);
        let keep = p((**n).value);
        if keep {
            //@ close nodes(*n);
            filter_nodes(&raw mut (**n).next, p);
        } else {
            let next_ = (**n).next;
            //@ open node(*n, _, _);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

//@ req nodes(n);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        //@ open nodes(n);
        //@ open node(n, ?next, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}