//@ pred Stack(node: *mut Node; ?count: i32) = 
//@   node == null ? count == 0 : 
//@     exists(?next, ?val). node->Node{next: next, val: val} &*& Stack(next, count - 1);

//@ pred stack_t(stack: *mut Stack) = 
//@   stack->Stack{head: ?h} &*& Stack(h, ?count);

unsafe fn stack_get_count(stack: *mut Stack) -> i32
{
    //@ open stack_t(stack);
    let mut n = (*stack).head;
    let mut i = 0;
    //@ Stack_fuel(i32::MAX);
    loop {
        if n.is_null() {
            break;
        }
        //@ open Stack(n, _);
        n = (*n).next;
        i += 1;
    }
    //@ close stack_t(stack);
    i
}