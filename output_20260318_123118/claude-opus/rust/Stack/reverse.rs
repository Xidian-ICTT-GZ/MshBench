use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(*n: *mut Node) =
    n != std::ptr::null_mut() ==> (
        n->Node.next |-> ?next &*&
        n->Node.value |-> _ &*&
        nodes(next)
    );

predicate nodes_values(*n: *mut Node, list: list<i32>) =
    switch(list) {
        case nil => n == std::ptr::null_mut();
        case cons(h,t) => n != std::ptr::null_mut() &*&
            n->Node.next |-> ?next &*&
            n->Node.value |-> h &*&
            nodes_values(next, t);
    };

predicate stack(stack_ptr: *mut Stack, list: list<i32>) =
    stack_ptr->Stack.head |-> ?head &*&
    nodes_values(head, list);

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack(stack, ?list))]
    #[ensures(stack(stack, cons(value, list)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, ?list) &*& list != nil)]
    #[ensures(stack(stack, tail(list)) &*& result == head(list))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;
        open nodes_values(head, list);
        let result = (*head).value;
        (*stack).head = (*head).next;
        close nodes_values((*stack).head, tail(list));
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack, ?list))]
    #[ensures(stack(stack, reverse(list)))]
    unsafe fn reverse(stack: *mut Stack) {
        let mut n = (*stack).head;
        let mut m = std::ptr::null_mut();
        open nodes_values(n, list);
        lemma_reverse_loop(&mut n, &mut m, list, nil);
        (*stack).head = m;
        close nodes_values(m, reverse(list));
    }

    #[predicate]
    #[verbatim]
    lemma void lemma_reverse_loop(*mut *mut Node n_ptr, *mut *mut Node m_ptr, list<i32> n_list, list<i32> m_list)
        requires *n_ptr |-> ?n &*& *m_ptr |-> ?m &*& nodes_values(n, n_list) &*& nodes_values(m, m_list);
        ensures *n_ptr |-> n &*& *m_ptr |-> m &*& nodes_values(n, n_list) &*& nodes_values(m, m_list);
    {
        open nodes_values(n, n_list);
        switch (n_list) {
            case nil:
                
            case cons(h, t):
                leak nodes_values(n, n_list); 
                let next = (*(n)).next;
                *(n_ptr) = next;
                (*(n)).next = *m_ptr;
                *(m_ptr) = n;
                lemma_reverse_loop(n_ptr, m_ptr, t, cons(h, m_list));
            }
    }

    #[requires(stack(stack, ?list))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack(stack, list);
        open nodes_values((*stack).head, list);
        lemma_dispose_nodes((*stack).head, list);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

    #[predicate]
    #[verbatim]
    lemma void lemma_dispose_nodes(*mut Node n, list<i32> list)
        requires nodes_values(n, list);
        ensures true;
    {
        open nodes_values(n, list);
        switch (list) {
            case nil:
            case cons(h, t):
                lemma_dispose_nodes((*n).next, t);
                dealloc(n as *mut u8, Layout::new::<Node>());
        }
    }
}
fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        let result1 = Stack::pop(s);
        let result2 = Stack::pop(s);
        Stack::dispose(s);
    }
}