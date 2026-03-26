use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

predicate node(*mut Node n; i32 value, *mut Node next) = 
    n |-> Node { next: next, value: value };

predicate nodes(*mut Node head; list<i32> values) =
    match values {
        [] => head == std::ptr::null_mut(),
        [v] + vs => exists(*mut Node next). node(head, v, next) * nodes(next, vs)
    };

predicate stack(*mut Stack s; list<i32> values) =
    s |-> Stack { head: ?head } * nodes(head, values);

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) 
    requires *n |-> ?head * nodes(head, ?vs) * foreach(vs, (|v: i32| p(v) || true)),
    ensures *n |-> ?head2 * nodes(head2, ?vs2) * foreach(vs2, (|v: i32| p(v))),
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

unsafe fn dispose_nodes(n: *mut Node)
    requires nodes(n, _),
    ensures emp,
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(stack(result, []))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr:: null_mut();

        stack
    }

    #[requires(stack(stack, ?vs))]
    #[ensures(stack(stack, [value] + vs))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack(stack, [?v] + ?vs))]
    #[ensures(stack(stack, vs) && result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack, ?vs) * foreach(vs, (|x: i32| p(x) || true)))]
    #[ensures(stack(stack, ?vs2) * foreach(vs2, (|x: i32| p(x))))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        filter_nodes(&raw mut (*stack).head, p);
    }

    #[requires(stack(stack, _))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

#[requires(true)]
#[ensures(true)]
fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}