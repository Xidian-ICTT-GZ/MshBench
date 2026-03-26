use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}
struct Stack {
    head: *mut Node,
}

/*@

predicate node(struct Node *n; struct Node *next, i32 v) =
    n->next |-> next &*& n->value |-> v;

predicate nodes(struct Node *h) =
    h == 0 ?
        emp
    :
        node(h, ?nxt, ?v) &*& nodes(nxt);

predicate stack(struct Stack *s) =
    s->head |-> ?h &*& nodes(h);

lemma void nodes_dispose(struct Node *h)
    requires nodes(h);
    ensures emp;
{
    if (h == 0) {
    } else {
        open nodes(h);
        open node(h, ?nxt, ?v);
        nodes_dispose(nxt);
    }
}

@*/

impl Stack {
    #[requires(true)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack(stack) )]
    #[ensures(stack(stack) )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack) &*& (*stack).head != std::ptr::null_mut())]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}
fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}