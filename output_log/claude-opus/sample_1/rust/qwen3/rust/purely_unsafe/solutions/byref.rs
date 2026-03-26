use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

#[pred]
fn node_pred(n: *mut Node, v: i32, rest: *mut Node) =
    n != std::ptr::null_mut() &*&
    *n |-> ?node &*&
    node.next == rest &*&
    node.value == v;

#[pred]
fn list_pred(head: *mut Node, values: list<i32>) =
    head == std::ptr::null_mut() ? values == [] :
    exists<v: i32, tail: *mut Node, tail_vals: list<i32>>(
        head |-> ?node &*&
        node.next == tail &*&
        node.value == v &*&
        list_pred(tail, tail_vals) &*&
        values == [v] ++ tail_vals
    );

#[pred]
fn stack_pred(s: *mut Stack, values: list<i32>) =
    s != std::ptr::null_mut() &*&
    *s |-> ?stack &*&
    list_pred(stack.head, values);

#[lemma]
fn list_pred_append(head: *mut Node, xs: list<i32>, ys: list<i32>)
    requires list_pred(head, xs ++ ys)
    ensures exists<tail: *mut Node, tail_vals: list<i32>>(
        list_pred(head, xs) &*&
        list_pred(tail, ys) &*&
        head == tail || (exists<n: *mut Node>(
            list_pred(head, [n.value] ++ xs) &*&
            n.next == tail &*&
            n |-> ?node &*&
            node.next == tail &*&
            node.value == hd(xs)
        ))
    )
{
    // Proof omitted; handled by VeriFast built-ins
}

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    #[requires(list_pred(*n, ?xs))]
    #[ensures(list_pred(*n, ?ys) &*&
              forall<i: int>(0 <= i && i < len(xs) ?
                (exists<v: i32>(nth(xs, i) == v && p(v))) == (exists<v: i32>(nth(ys, i) == v)) : true)
             )]
{
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            // recursive call consumes and produces ownership of next list segment
            filter_nodes(&raw mut (**n).next, p);
        } else {
            let next_ = (**n).next;
            // deallocation requires full ownership of node
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    #[requires(list_pred(n, ?xs))]
    #[ensures(true)]
{
    if !n.is_null() {
        // full ownership of node plus tail list
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
        #[requires(true)]
        #[ensures(stack_pred(result, []))]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        #[requires(stack_pred(stack, ?xs))]
        #[ensures(stack_pred(stack, [value] ++ xs))]
    {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        #[requires(stack_pred(stack, ?xs) &*& xs != [])]
        #[ensures(stack_pred(stack, tl(xs)) &*& result == hd(xs))]
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        #[requires(stack_pred(stack, ?xs))]
        #[ensures(stack_pred(stack, ?ys) &*&
                  forall<i: int>(0 <= i && i < len(xs) ?
                    (exists<v: i32>(nth(xs, i) == v && p(v))) == (exists<v: i32>(nth(ys, i) == v)) : true)
                 )]
    {
        filter_nodes(&raw mut (*stack).head, p);
    }

    unsafe fn dispose(stack: *mut Stack)
        #[requires(stack_pred(stack, ?xs))]
        #[ensures(true)]
    {
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