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

/*@ pred node(node: *mut Node, next: *mut Node, value: i32) =
    alloc_block_(node as *mut u8, std::alloc::Layout::new::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

/*@ pred stack(stack: *mut Stack, head: *mut Node) =
    alloc_block_(stack as *mut u8, std::alloc::Layout::new::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

/*@ pred nodes(n: *mut Node) =
    n == std::ptr::null_mut() ?
        emp
    :
        node(n, ?next, ?val) &*& nodes(next);
@*/

unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

//@ req nodes(n);
//@ ens nodes(result) &*& nodes(?rest) &*& n == std::ptr::null_mut() || (node(n, ?old_next, ?val) &*& if keep then result == n &*& rest == old_next else result == ?filtered_rest &*& rest == n);
unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node {
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        //@ open nodes(n);
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);
            //@ close node(n, next, (*n).value);
            //@ close nodes(n);
            (*n).next = next;
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

//@ req nodes(n);
//@ ens emp;
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        //@ open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    //@ req true;
    //@ ens stack(result, std::ptr::null_mut());
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close stack(stack, std::ptr::null_mut());
        stack
    }

    //@ req stack(stack, ?old_head) &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head) &*& new_head == ?n &*& node(n, old_head, value);
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack(stack, old_head);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close node(n, old_head, value);
        //@ close nodes(n);
        //@ close stack(stack, n);
    }

    //@ req stack(stack, ?old_head) &*& old_head != std::ptr::null_mut() &*& node(old_head, ?next, ?val) &*& nodes(next);
    //@ ens stack(stack, next) &*& nodes(next) &*& result == val;
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open stack(stack, old_head);
        //@ open node(old_head, next, val);
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, next);
        result
    }

    //@ req stack(stack, ?old_head) &*& nodes(old_head);
    //@ ens stack(stack, ?new_head) &*& nodes(new_head);
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        //@ open stack(stack, old_head);
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
        //@ close stack(stack, head);
    }

    //@ req stack(stack, ?head) &*& nodes(head);
    //@ ens emp;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack, head);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}