use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate nodes(struct Node *n;) =
    n == std::ptr::null_mut() ?
        emp
    :
        n |-> Node { next: ?next, value: _ } &*& nodes(next);

predicate stack(struct Stack *s;) =
    s |-> Stack { head: ?head } &*& nodes(head);

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(nodes(n))]
    #[ensures(emp)]
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
        #[requires(true)]
        #[ensures(stack(result))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        close nodes(std::ptr::null_mut());
        close stack(stack);
        return stack;
    }

    unsafe fn is_empty(stack: *mut Stack) -> bool
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        close stack(stack);
        return result;
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack(stack))]
        #[ensures(stack(stack))]
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;

        
        open stack(stack);
        close nodes(n);
        close stack(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires(stack(stack) &*& (*stack).head != std::ptr::null_mut() &*& nodes((*stack).head))]
        #[ensures(stack(stack))]
    {
        open stack(stack);
        let head = (*stack).head;
        open nodes(head);

        let result = (*head).value;
        (*stack).head = (*head).next;
        close nodes((*head).next);
        dealloc(head as *mut u8, Layout::new::<Node>());

        close stack(stack);
        return result;
    }

    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack(stack))]
        #[ensures(emp)]
    {
        open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main()
{
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        Stack::pop(s);
        Stack::pop(s);
        Stack::dispose(s);
    }
}