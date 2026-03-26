predicate node(n: *mut Node; next: *mut Node, value: i32) =
    n != std::ptr::null_mut() &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

predicate nodes(n: *mut Node; values: list<i32>) =
    match values {
        Nil => n == std::ptr::null_mut(),
        Cons(h, t) => exists(next: *mut Node). node(n, next, h) &*& nodes(next, t)
    };

predicate stack(s: *mut Stack; values: list<i32>) =
    s != std::ptr::null_mut() &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    nodes(head, values);

lemma void nodes_split(*mut Node n, list<i32> vs)
    requires nodes(n, vs);
    ensures nodes(n, vs);
{
    admit();
}

lemma void nodes_join(*mut Node n, list<i32> vs)
    requires nodes(n, vs);
    ensures nodes(n, vs);
{
    admit();
}

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    requires *n |-> ?head &*& nodes(head, ?vs) &*&
             foreach(vs, lambda(x: i32). true) &*&
             forall(vs, lambda(x: i32). p(x) || !p(x));
    ensures *n |-> ?new_head &*& nodes(new_head, ?filtered_vs) &*&
            foreach(filtered_vs, lambda(x: i32). p(x)) &*&
            foreach(vs, lambda(x: i32). mem(x, filtered_vs) || !p(x));
{
    if !(*n).is_null() {
        let head = *n;
        assert node(head, ?next, ?val) &*& nodes(next, ?rest);
        let keep = p(val);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
            assert nodes(next, ?kept_rest);
            leak node(head, next, val);
            leak nodes(next, kept_rest);
        } else {
            let next_ = (**n).next;
            dealloc(head as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
            leak nodes(next_, ?kept_rest);
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n, ?vs);
    ensures emp;
{
    if !n.is_null() {
        assert node(n, ?next, ?val) &*& nodes(next, ?rest);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        requires emp;
        ensures stack(result, Nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack, ?vs);
        ensures stack(stack, Cons(value, vs));
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack, Cons(?v, ?vs));
        ensures stack(stack, vs) &*& result == v;
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires stack(stack, ?vs) &*&
                 forall(vs, lambda(x: i32). p(x) || !p(x));
        ensures stack(stack, ?filtered_vs) &*&
                foreach(filtered_vs, lambda(x: i32). p(x)) &*&
                foreach(vs, lambda(x: i32). mem(x, filtered_vs) || !p(x));
    {
        filter_nodes(&raw mut (*stack).head, p);
    }

    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack, ?vs);
        ensures emp;
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
    requires true;
    ensures result == (x != 20);
{
    x != 20
}

fn main()
    requires emp;
    ensures emp;
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}