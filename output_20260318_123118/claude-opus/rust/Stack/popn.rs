use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate_node<Node> (n: *mut Node, value: i32, next: *mut Node) = 
    n->Node { next: next, value: value };

predicate_nodes_sum(nodes: *mut Node, ints: list<i32>) = 
    switch(ints) {
        case nil => nodes == std::ptr::null_mut();
        case cons(h, t) => 
            exists *mut Node next_node;
            nodes->Node { next: next_node, value: h } &*& predicate_nodes_sum(next_node, t);
    };

predicate_stack(stack: *mut Stack, contents: list<i32>) = 
    stack->Stack { head: ?head } &*& predicate_nodes_sum(head, contents);

predicate nodes_sum_nodes(nodes: *mut Node, sum: int) = 
    switch(nodes) {
        case std::ptr::null_mut() => sum == 0;
        case _ => 
            exists int v; 
            exists *mut Node next_node;
            nodes->Node { next: next_node, value: v } &*& nodes_sum_nodes(next_node, ?rest_sum) &*& sum == v + rest_sum;
    };

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
    #[requires predicate_nodes_sum(nodes, ?ints)]
    #[ensures predicate_nodes_sum(nodes, ints) &*& result == sum(ints)]
{
    let mut result = 0;
    
    if !nodes.is_null() {
        let head = (*nodes).value;
        let next = (*nodes).next;
        
        open predicate_nodes_sum(nodes, ?ints0);
        switch(ints0) {
            case cons(h, t) => {
                assert h == head;
                assert t == ?tail;
                close predicate_nodes_sum(next, tail);
                result = get_nodes_sum(next);
                result += head;
                close predicate_nodes_sum(nodes, ints0);
            }
            case nil => {}
        }
    } else {
        close predicate_nodes_sum(nodes, nil);
    }
    
    result
}

impl Stack {

    unsafe fn create() -> *mut Stack
        #[ensures predicate_stack(result, nil)]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close predicate_nodes_sum(std::ptr::null_mut(), nil);
        close predicate_stack(stack, nil);
        stack
    }
    
    unsafe fn is_empty(stack: *mut Stack) -> bool
        #[requires predicate_stack(stack, ?ints)]
        #[ensures predicate_stack(stack, ints)]
    {
        let head = (*stack).head;
        let result = (*stack).head.is_null();
        result
    }
    
    unsafe fn get_sum(stack: *mut Stack) -> i32
        #[requires predicate_stack(stack, ?ints)]
        #[ensures predicate_stack(stack, ints) &*& result == sum(ints)]
    {
        let head = (*stack).head;
        open predicate_stack(stack, ints);
        close predicate_nodes_sum(head, ints);
        let result = get_nodes_sum(head);
        close predicate_stack(stack, ints);
        result
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires predicate_stack(stack, ?ints)]
        #[ensures predicate_stack(stack, cons(value, ints))]
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        open predicate_stack(stack, ints);
        let old_head = (*stack).head;
        close predicate_nodes_sum(old_head, ints);
        
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close predicate_nodes_sum(n, cons(value, ints));
        close predicate_stack(stack, cons(value, ints));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires predicate_stack(stack, ?ints) &*& ints != nil]
        #[ensures predicate_stack(stack, tail(ints)) &*& result == head(ints)]
    {
        open predicate_stack(stack, ints);
        switch(ints) {
            case cons(h, t) => {
                let head = (*stack).head;
                open predicate_nodes_sum(head, ints);
                
                (*stack).head = (*head).next;
                dealloc(head as *mut u8, Layout::new::<Node>());
                close predicate_nodes_sum((*stack).head, t);
                close predicate_stack(stack, t);
                return h;
            }
            case nil => unreachable!()
        }
    }
    
    unsafe fn popn(stack: *mut Stack, n: i32)
        #[requires predicate_stack(stack, ?ints) &*& length(ints) >= n]
        #[ensures predicate_stack(stack, drop(n, ints))]
    {
        let mut i = 0;
        open predicate_stack(stack, ints);
        let mut curr_contents = ints;
        while(i < n)
            invariant predicate_stack(stack, curr_contents) &*& length(curr_contents) == length(ints) - i &*& i <= n
        {
            Stack::pop(stack);
            i += 1;
            curr_contents = drop(1, curr_contents);
        }
        close predicate_stack(stack, curr_contents);
    }
    
    unsafe fn dispose(stack: *mut Stack)
        #[requires predicate_stack(stack, ?ints)]
        #[ensures emp]
    {
        open predicate_stack(stack, ints);
        let mut n = (*stack).head;
        open predicate_nodes_sum(n, ints);
        while(n != std::ptr::null_mut())
            invariant predicate_nodes_sum(n, ?rest)
        {
            let next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            if next != std::ptr::null_mut() {
                open predicate_nodes_sum(next, ?next_rest);
                n = next;
            } else {
                n = std::ptr::null_mut();
            }
        }
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

fixpoint int sum(list<int> l) {
    switch(l) {
        case nil: return 0;
        case cons(h,t): return h + sum(t);
    }
}

fixpoint list<int> drop(int n, list<int> l) {
    return n <= 0 ? l : (switch(l) { case nil => nil; case cons(h,t) => drop(n - 1, t); });
}

fixpoint int length<t>(list<t> l) {
    switch(l) {
        case nil: return 0;
        case cons(_,t): return 1 + length(t);
    }
}