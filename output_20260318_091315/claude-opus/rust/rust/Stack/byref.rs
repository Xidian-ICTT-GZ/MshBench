use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(struct Node *n; int value, struct Node *next) =
    n->value |-> value &*& n->next |-> next;

predicate nodes(struct Node *n; list<int> vs) =
    switch(vs) {
        case nil: n == null;
        case cons(h, t): node(n, h, ?next) &*& nodes(next, t);
    };

predicate stack(struct Stack *s; list<int> vs) =
    s->head |-> ?head &*& nodes(head, vs);

type I32Predicate = unsafe fn(i32) -> bool;

#[requires(n != null ==> nodes(*n, ?vs))]
#[ensures(*n == null ==> nodes(*n, nil))]
#[ensures(*n != null ==> nodes(*n, ?filtered))]
#[ensures(forall<int>(?x) ^^ mem(x, filtered) ==> p(x))]
#[ensures(subset(filtered, vs))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    
    
{
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            filter_nodes(&raw mut (**n).next, p);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

#[requires(n != null ==> nodes(n, ?vs))]
#[ensures(nodes(n, nil))]
unsafe fn dispose_nodes(n: *mut Node)
    
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        stack
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, cons(value, vs)))]
    unsafe fn push(stack: *mut Stack, value: i32)
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, ?vs) &*& vs != nil)]
    #[ensures(stack(stack, tail(vs)) &*& result == head(vs))]
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        result
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, ?filtered) &*& forall<int>(?x) ^^ mem(x, filtered) ==> p(x) &*& subset(filtered, vs))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    {
        filter_nodes(&raw mut (*stack).head, p);
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}