use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(struct Node *n; int v, struct Node *next) =
    n->value |-> v &*& n->next |-> next;

predicate nodes(struct Node *n; list<int> values) =
    switch(values) {
        case nil: return n == null;
        case cons(h, t): return node(n; h, ?next) &*& nodes(next; t);
    };

predicate stack(struct Stack *s; list<int> elems) =
    s->head |-> ?head &*& nodes(head; elems);

type I32Predicate = unsafe fn(i32) -> bool;

#[requires(nodes(n; ?vals) &*& forall<int>(vals, p))]
#[ensures(nodes(result; ?filtered))]
unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
    requires nodes(n; ?vals) &*& forall<int>(vals, p);
    ensures nodes(result; ?filtered);
{
    if n.is_null() {
        return std::ptr::null_mut();
    } else {
        open nodes(n; vals);
        open node(n; ?v, ?next);
        bool keep = p(v);
        if (keep) {
            let filtered_next = filter_nodes(next, p);
            (*n).next = filtered_next;
            close node(n; v, filtered_next);
            close nodes(n; cons(v, filtered_next ? filtered_next : nil)); 
            
            close nodes(n; cons(v, ?filtered_tail));
            return n;
        } else {
            let filtered_result = filter_nodes(next, p);
            dealloc(n as *mut u8, Layout::new::<Node>());
            return filtered_result;
        }
    }
}

#[requires(nodes(n; ?vals))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n; ?vals);
    ensures true;
{
    if !n.is_null() {
        open nodes(n; ?vals);
        open node(n; _, ?next);
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    #[requires(true)]
    #[ensures(stack(result; nil))]
    unsafe fn create() -> *mut Stack
        requires true;
        ensures stack(result; nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack(stack; nil);
        return stack;
    }
    
    #[requires(stack(stack; ?elems))]
    #[ensures(stack(stack; cons(value, elems)))]
    unsafe fn push(stack: *mut Stack, value: i32)
        requires stack(stack; ?elems);
        ensures stack(stack; cons(value, elems));
    {
        open stack(stack; elems);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node(n; value, (*n).next);
        close nodes((*stack).head; cons(value, elems));
        close stack(stack; cons(value, elems));
    }

    #[requires(stack(stack; ?elems)) &*& elems != nil]
    #[ensures(stack(stack; tail(elems)))]
    #[ensures(result == head(elems))]
    unsafe fn pop(stack: *mut Stack) -> i32
        requires stack(stack; ?elems) &*& elems != nil;
        ensures stack(stack; tail(elems)) &*& result == head(elems);
    {
        open stack(stack; elems);
        open nodes((*stack).head; elems);
        open node((*stack).head; ?v, ?next);
        
        let head = (*stack).head;
        (*stack).head = next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        
        close nodes(next; tail(elems));
        close stack(stack; tail(elems));
        return v;
    }
    
    #[requires(stack(stack; ?elems)) &*& forall<int>(elems, p)]
    #[ensures(stack(stack; ?filtered))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        requires stack(stack; ?elems) &*& forall<int>(elems, p);
        ensures stack(stack; ?filtered);
    {
        open stack(stack; elems);
        open nodes((*stack).head; elems);
        let head = filter_nodes((*stack).head, p);
        (*stack).head = head;
        close stack(stack; ?filtered);
    }
    
    #[requires(stack(stack; ?elems))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
        requires stack(stack; ?elems);
        ensures true;
    {
        open stack(stack; elems);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

#[requires(true)]
#[ensures(result == (x != 20))]
unsafe fn neq_20(x: i32) -> bool
    requires true;
    ensures result == (x != 20);
{
    x != 20
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}