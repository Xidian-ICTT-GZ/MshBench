//@ req true;
//@ ens true;
fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        
        let result2 = Stack::pop(s);
        
        Stack::dispose(s);
    }
}

/*@ pred stack(node: *mut Node, vs: list<i32>) =
    node == std::ptr::null_mut::<Node>() &*& vs == nil
    || node != std::ptr::null_mut::<Node>() &*&
       alloc_block_Node(node) &*&
       (*node).value |-> ?v &*&
       (*node).next |-> ?next &*&
       stack(next, ?rest) &*&
       vs == cons(v, rest);
@*/

/*@ pred stack_struct(s: *mut Stack, vs: list<i32>) =
    alloc_block_Stack(s) &*&
    (*s).head |-> ?h &*&
    stack(h, vs);
@*/

impl Stack {

    //@ req true;
    //@ ens stack_struct(result, nil);
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        //@ close alloc_block_Stack(stack)();
        (*stack).head = std::ptr::null_mut();
        //@ close stack(std::ptr::null_mut(), nil);
        //@ close stack_struct(stack, nil);
        stack
    }
    
    //@ req stack_struct(stack, ?vs);
    //@ ens stack_struct(stack, cons(value, vs));
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open stack_struct(stack, vs);
        //@ open alloc_block_Stack(stack)();
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        //@ close alloc_block_Node(n)();
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close stack(n, cons(value, vs));
        //@ close stack_struct(stack, cons(value, vs));
    }
    
    //@ req stack_struct(stack, cons(?v, ?vs));
    //@ ens stack_struct(stack, vs) &*& result == v;
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open stack_struct(stack, cons(v, vs));
        //@ open alloc_block_Stack(stack)();
        let head = (*stack).head;
        //@ open stack(head, cons(v, vs));
        //@ open alloc_block_Node(head)();
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close stack((*stack).head, vs);
        //@ close stack_struct(stack, vs);
        result
    }
    
    //@ req stack_struct(stack, ?vs);
    //@ ens stack_struct(stack, reverse(vs));
    unsafe fn reverse(stack: *mut Stack) {
        //@ open stack_struct(stack, vs);
        //@ open alloc_block_Stack(stack)();
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        //@ close stack(m, nil);
        //@ assert stack(n, vs);
        //@ inv stack(n, ?curr) &*& stack(m, ?rev_curr) &*& append(rev_curr, curr) == vs;
        loop {
            if n.is_null() {
                break;
            }
            //@ open stack(n, ?curr);
            //@ open alloc_block_Node(n)();
            let next = (*n).next;
            (*n).next = m;
            //@ close stack(n, cons(?hd, rev_curr));
            m = n;
            n = next;
            //@ close stack(m, cons(hd, rev_curr));
            //@ assert append(cons(hd, rev_curr), curr) == vs;
        }
        (*stack).head = m;
        //@ open stack(m, _);
        //@ close stack_struct(stack, reverse(vs));
    }

    //@ req stack_struct(stack, _);
    //@ ens true;
    unsafe fn dispose(stack: *mut Stack) {
        //@ open stack_struct(stack, _);
        //@ open alloc_block_Stack(stack)();
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}