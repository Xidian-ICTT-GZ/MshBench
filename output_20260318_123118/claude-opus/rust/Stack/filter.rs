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

predicate nodes(struct Node *n; list<int> vs) =
    n == 0 ? vs == nil :
    node(n, head(vs), ?next) &*& nodes(next, tail(vs));

predicate stack(struct Stack *s; list<int> vs) =
    s->head |-> ?h &*& nodes(h, vs);

type I32Predicate = unsafe fn(i32) -> bool;

#[requires(nodes(n, ?vs) &*& forall<int>(vs, p))]
#[ensures(nodes(result, ?filteredVs))]
unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
    where forall<int>(list<int>, I32Predicate) -> bool
{
    if n == std::ptr::null_mut() {
        std::ptr::null_mut()
    } else {
        open nodes(n, vs);
        bool keep = p((*n).value);
        if (keep) {
            struct Node *next_filtered = filter_nodes((*n).next, p);
            (*n).next = next_filtered;
            close node(n, (*n).value, next_filtered);
            close nodes(n, cons((*n).value, ?tail_filtered));
            return n;
        } else {
            struct Node *next = (*n).next;
            close nodes(next, tail(vs));
            dealloc(n as *mut u8, Layout::new::<Node>());
            return filter_nodes(next, p);
        }
    }
}

#[requires(nodes(n, _) )]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    if n != std::ptr::null_mut() {
        open nodes(n, ?vs);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack(stack, nil);
        return stack;
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, cons(value, vs)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node(n, value, (*n).next);
        close nodes(n, cons(value, vs));
        close stack(stack, cons(value, vs));
    }

    #[requires(stack(stack, ?vs) &*& vs != nil)]
    #[ensures(stack(stack, tail(vs)) &*& result == head(vs))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        open stack(stack, vs);
        open nodes((*stack).head, vs);
        let head = (*stack).head;
        int result = (*head).value;
        (*stack).head = (*head).next;
        close stack(stack, tail(vs));
        dealloc(head as *mut u8, Layout::new::<Node>());
        return result;
    }

    #[requires(stack(stack, ?vs) &*& forall<int>(vs, p))]
    #[ensures(stack(stack, ?filteredVs))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        open stack(stack, vs);
        struct Node *head = filter_nodes((*stack).head, p);
        (*stack).head = head;
        close stack(stack, filteredVs);
    }

    #[requires(stack(stack, _))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        open stack(stack, ?vs);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool {
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