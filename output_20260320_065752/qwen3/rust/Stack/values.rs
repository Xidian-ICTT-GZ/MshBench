//@ req true;
//@ ens true;
fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}

/*@ pred node(node: *mut Node, next: *mut Node, value: i32) =
    alloc_block_(node as *mut u8, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(node) &*&
    (*node).next |-> next &*&
    (*node).value |-> value;
@*/

/*@ pred stack(stack: *mut Stack, head: *mut Node) =
    alloc_block_(stack as *mut u8, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(stack) &*&
    (*stack).head |-> head;
@*/

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

    //@ req stack(stack, ?old_head) &*& true;
    //@ ens stack(stack, ?new_head) &*& node(new_head, old_head, value);
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack(stack, _);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close node(n, (*stack).head, value);
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close stack(stack, n);
    }

    //@ req stack(stack, _);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack(stack, _);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}