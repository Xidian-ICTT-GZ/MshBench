/*@ pred stack_block(t: *mut Stack) = alloc_block_(t as *u8, std::alloc::Layout::new::<Stack>()) &*& struct_Stack_padding(t); @*/
/*@ pred node_block(t: *mut Node) = alloc_block_(t as *u8, std::alloc::Layout::new::<Node>()) &*& struct_Node_padding(t); @*/
/*@ pred nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        true
    :
        node_block(n) &*& (*n).next |-> ?next &*& (*n).value |-> _ &*& nodes(next);
@*/

impl Stack {

    //@ req true;
    //@ ens stack_block(result) &*& (*result).head |-> std::ptr::null_mut();
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack_block(stack);
        (*stack).head = std::ptr::null_mut();
        //@ close nodes(std::ptr::null_mut());
        stack
    }

    //@ req stack_block(stack) &*& (*stack).head |-> ?head &*& nodes(head);
    //@ ens stack_block(stack) &*& (*stack).head |-> head &*& nodes(head) &*& result == length_nodes(head);
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        //@ open nodes(n);
        //@ while n != std::ptr::null_mut() invariant nodes(n) &*& i == length_nodes(head) - length_nodes(n);
        loop {
            if n.is_null() {
                break;
            }
            //@ open nodes(n);
            n = (*n).next;
            i += 1;
        }
        //@ close nodes(std::ptr::null_mut());
        i
    }

    //@ req stack_block(stack) &*& (*stack).head |-> ?head1 &*& nodes(head1) &*&
    
    //@ ens stack_block(stack) &*& (*stack).head |-> ?new_head &*& nodes(new_head) &*&
    
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        //@ open stack_block(other);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            //@ open nodes(n);
            loop {
                if (*n).next.is_null() {
                    break;
                }
                //@ open nodes((*n).next);
                n = (*n).next;
            }
            (*n).next = (*stack).head;
            //@ close nodes((*stack).head);
            (*stack).head = head0;
            //@ close nodes(head0);
        } else {
            //@ close nodes(std::ptr::null_mut());
        }
    }

    //@ req stack_block(stack) &*& (*stack).head |-> ?old_head &*& nodes(old_head);
    //@ ens stack_block(stack) &*& (*stack).head |-> ?new_head &*& nodes(new_head);
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node_block(n);
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close nodes((*stack).head);
        (*stack).head = n;
        //@ close nodes(n);
    }

    //@ req stack_block(stack) &*& (*stack).head |-> ?old_head &*& old_head != std::ptr::null_mut() &*& nodes(old_head);
    //@ ens stack_block(stack) &*& (*stack).head |-> ?new_head &*& nodes(new_head) &*& result == head_value(old_head);
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        //@ open nodes(head);
        let result = (*head).value;
        (*stack).head = (*head).next;
        //@ open node_block(head);
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    //@ req stack_block(stack);
    //@ ens dealloc_block_(stack as *u8, std::alloc::Layout::new::<Stack>());
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack_block(stack);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

/*@ fixpoint i32 length_nodes(*mut Node n) {
    match n {
        std::ptr::null_mut() => 0,
        _ => 1 + length_nodes((*(n as *const Node)).next)
    }
} @*/

/*@ fixpoint i32 head_value(*mut Node n) {
    (*(n as *const Node)).value
} @*/

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