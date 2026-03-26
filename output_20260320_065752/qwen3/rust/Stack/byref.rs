/*@ pred node(n: *mut Node; next: *mut Node, value: i32) =
    n != 0 &*&
    alloc_block_n(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    struct_Node_next(n, next) &*&
    struct_Node_value(n, value);
@*/

/*@ pred stack(s: *mut Stack; head: *mut Node) =
    s != 0 &*&
    alloc_block_n(s, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    struct_Stack_head(s, head);
@*/

/*@ pred nodes(n: *mut Node; vs: list<i32>) =
    match vs {
        nil => n == 0,
        cons(v, vs0) => node(n, ?n0, v) &*& nodes(n0, vs0)
    };
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
//@ ens exists(?s, stack(s, _));
unsafe fn Stack::create() -> *mut Stack {
    let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
    if stack.is_null() {
        handle_alloc_error(Layout::new::<Stack>());
    }
    (*stack).head = std::ptr::null_mut();
    //@ close stack(stack, 0);
    stack
}

//@ req stack(stack, ?head) &*& nodes(head, ?vs);
//@ ens stack(stack, ?head1) &*& nodes(head1, cons(value, vs));
unsafe fn Stack::push(stack: *mut Stack, value: i32) {
    //@ open stack(stack, head);
    let n = alloc(Layout::new::<Node>()) as *mut Node;
    if n.is_null() {
        handle_alloc_error(Layout::new::<Node>());
    }
    (*n).next = (*stack).head;
    (*n).value = value;
    (*stack).head = n;
    //@ close node(n, head, value);
    //@ close stack(stack, n);
}

//@ req stack(stack, ?head) &*& head != 0 &*& node(head, ?next, ?v) &*& nodes(next, ?vs);
//@ ens stack(stack, next) &*& nodes(next, vs) &*& result == v;
unsafe fn Stack::pop(stack: *mut Stack) -> i32 {
    //@ open stack(stack, head);
    //@ open node(head, next, v);
    let head = (*stack).head;
    let result = (*head).value;
    (*stack).head = (*head).next;
    dealloc(head as *mut u8, Layout::new::<Node>());
    //@ close stack(stack, next);
    result
}

//@ req stack(stack, ?head) &*& nodes(head, ?vs);
//@ ens stack(stack, ?head1) &*& nodes(head1, ?vs1) &*& filter_list(vs, p, vs1);
unsafe fn Stack::filter(stack: *mut Stack, p: I32Predicate) {
    //@ open stack(stack, head);
    filter_nodes(&raw mut (*stack).head, p);
    //@ close stack(stack, *(&raw mut (*stack).head));
}

//@ req *n |-> ?head &*& nodes(head, ?vs);
//@ ens *n |-> ?head1 &*& nodes(head1, ?vs1) &*& filter_list(vs, p, vs1);
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    if !(*n).is_null() {
        //@ open nodes(*n, vs);
        let keep = p((**n).value);
        if keep {
            //@ close nodes(*n, cons((**n).value, ?tail));
            filter_nodes(&raw mut (**n).next, p);
        } else {
            let next_ = (**n).next;
            //@ open node(*n, _, _);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    } else {
        //@ close nodes(0, nil);
    }
}

/*@ fix filter_list(xs: list<i32>, p: I32Predicate, ys: list<i32>): bool {
    match xs {
        nil => ys == nil,
        cons(x, xs0) => if p(x) { ys == cons(x, ?ys0) &*& filter_list(xs0, p, ys0) } else { filter_list(xs0, p, ys) }
    }
} @*/

//@ req nodes(n, ?vs);
//@ ens true;
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        //@ open nodes(n, vs);
        //@ open node(n, ?next, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

//@ req stack(stack, ?head) &*& nodes(head, _);
//@ ens true;
unsafe fn Stack::dispose(stack: *mut Stack) {
    //@ open stack(stack, head);
    dispose_nodes((*stack).head);
    dealloc(stack as *mut u8, Layout::new::<Stack>());
}

//@ req true;
//@ ens result == (x != 20);
unsafe fn neq_20(x: i32) -> bool {
    x != 20
}