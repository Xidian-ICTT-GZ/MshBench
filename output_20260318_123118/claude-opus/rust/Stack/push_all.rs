use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate nodes(struct Node *n; list<int> vals) =
    n == std::ptr::null_mut()
    ?
        emp
    :
        n |-> Node { next: ?next0, value: ?v }
        &*& nodes(next0, ?rest)
        &*& vals == cons(v, rest);

predicate stack(struct Stack *s; list<int> vals) =
    s |-> Stack { head: ?head0 }
    &*& nodes(head0, vals);

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
    #[ensures(stack(stack, vs))]
    #[ensures(result == length(vs))]
    unsafe fn get_count(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        #[invariant nodes(n, ?rest) &*& length(rest) + i == length(vs)]
        loop {
            if n.is_null() {
                break;
            }

            n = (*n).next;
            i += 1;
        }

        i
    }

    #[requires(stack(stack, ?vs) **& stack(other, ?ovs))]
    #[ensures(stack(stack, append(ovs, vs)))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack)
    {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant nodes(n, ?ns) &*& ns != nil]
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

    #[requires(stack(stack, cons(?v, ?vs)))]
    #[ensures(stack(stack, vs))]
    #[ensures(result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack(stack, nil))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack)
    {
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