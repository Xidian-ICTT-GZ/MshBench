/*@ pred node(node: *mut Node, next: *mut Node, value: i32) = 
    alloc_block_(node, std::alloc::Layout::new::<Node>()) &*& 
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

/*@ pred stack(stack: *mut Stack, nodes: list<*mut Node>) =
    alloc_block_(stack, std::alloc::Layout::new::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> ?head &*&
    nodes == list_from_ptr(head) &*&
    list<Node>(head, node);
@*/

/*@ fixpoint list<t> list_from_ptr<t>(t ptr); @*/
/*@ fixpoint bool list<t>(t ptr, predicate(t, t, int) p); @*/

impl Stack {

    //@ req true;
    //@ ens stack(result, nil);
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close stack(stack, nil);
        (*stack).head = std::ptr::null_mut();
        stack
    }

    //@ req stack(stack, ?nodes);
    //@ ens stack(stack, nodes) &*& result == length(nodes);
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        let mut n = head;
        let mut i = 0;
        //@ open stack(stack, _);
        //@ close stack(stack, _);
        loop {
            //@ inv stack(stack, ?nodes_) &*& n == list_nth(nodes_, i) &*& i <= length(nodes_);
            if n.is_null() {
                break;
            }
            n = (*n).next;
            i += 1;
        }
        i
    }

    //@ req stack(stack, ?nodes1) &*& stack(other, ?nodes2);
    //@ ens stack(stack, append(reverse(nodes2), nodes1));
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        //@ open stack(other, _);
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;
        if !n.is_null() {
            loop {
                //@ inv n != null &*& list<Node>(n, node) &*& list_from_ptr(n) == ?tail &*& tail != nil;
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }
            (*n).next = (*stack).head;
            (*stack).head = head0;
        }
        //@ open stack(stack, _);
        //@ close stack(stack, _);
    }

    //@ req stack(stack, ?nodes);
    //@ ens stack(stack, cons(?new_node, nodes));
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(n, (*stack).head, value);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ open stack(stack, _);
        //@ close stack(stack, _);
    }

    //@ req stack(stack, cons(?head_node, ?rest));
    //@ ens stack(stack, rest) &*& result == ?val &*& node(head_node, _, val);
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        //@ open stack(stack, _);
        //@ open node(head, _, ?val);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack(stack, _);
        result
    }

    //@ req stack(stack, _);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack, _);
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