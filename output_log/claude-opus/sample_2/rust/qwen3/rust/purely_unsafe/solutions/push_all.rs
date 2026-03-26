use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred] struct NodePred {
    next: *mut Node,
    value: i32,
} = self == std::ptr::null_mut() ? false :
    (self |-> NodeData { next: next, value: value });

#[struct] struct NodeData {
    next: *mut Node,
    value: i32,
}

#[pred] struct StackPred {
    head: *mut Node,
} = self == std::ptr::null_mut() ? false :
    (self |-> StackData { head: head });

#[struct] struct StackData {
    head: *mut Node,
}

#[pred] struct ListPred(head: *mut Node) {
    head != std::ptr::null_mut() ? 
    (head |-> NodeData { next: tail, value: v } * ListPred(tail)) : 
    emp
}

predicate nodes_list(head: *mut Node)
    requires head != std::ptr::null_mut()
{
    head |-> NodeData { next: _, value: _ };
}

#[lemma] fn count_list_lemma(head: *mut Node) 
    requires ListPred(head)
    ensures result == count_list(head)
{
}

#[open] fn count_list(head: *mut Node) -> i32 {
    match head {
        std::ptr::null_mut() => 0,
        _ => {
            head |-> NodeData { next: tail, value: v };
            1 + count_list(tail)
        }
    }
}

impl Stack {
    #[requires(Layout::new::<Stack>().size() > 0)]
    #[ensures(result |-> StackPred { head: std::ptr::null_mut() })]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack |-> StackData { head: head } * ListPred(head))]
    #[ensures(result == count_list(head) && stack |-> StackData { head: head } * ListPred(head))]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        #[invariant(
            (n == std::ptr::null_mut() ? emp : (n |-> NodeData { next: next_n, value: _ } * ListPred(next_n))) *
            i + count_list(n) == count_list(head) &&
            stack |-> StackData { head: head }
        )]
        loop {
            if n.is_null() {
                break;
            }

            n = (*n).next;
            i += 1;
        }

        i
    }

    #[requires(
        stack |-> StackData { head: h1 } * ListPred(h1) *
        other |-> StackData { head: h2 } * ListPred(h2)
    )]
    #[ensures(stack |-> StackData { head: h2 } * ListPred(h2))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());

        let mut n = head0;

        if !n.is_null() {
            #[invariant(
                (n == std::ptr::null_mut() ? emp : (n |-> NodeData { next: next_n, value: _ } * ListPred(next_n)))
            )]
            loop {
                if (*n).next.is_null() {
                    break;
                }
                n = (*n).next;
            }

            (*n).next = (*stack).head;

            (*stack).head = head0;
        }
    }

    #[requires(
        stack |-> StackData { head: h } * ListPred(h) *
        Layout::new::<Node>().size() > 0
    )]
    #[ensures(
        stack |-> StackData { head: n } * n |-> NodeData { next: h, value: value } * ListPred(h)
    )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(
        stack |-> StackData { head: h } * h |-> NodeData { next: tail, value: v } * ListPred(tail)
    )]
    #[ensures(
        result == v && stack |-> StackData { head: tail } * ListPred(tail)
    )]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack |-> StackData { head: h } * ListPred(h))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}