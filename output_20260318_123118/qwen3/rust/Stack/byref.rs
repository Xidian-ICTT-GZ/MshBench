use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

predicate node(*mut Node n; i32 value, *mut Node next) =
    n |-> struct Node { next: next, value: value };

predicate stack(*mut Stack s; list<*mut Node> nodes) =
    s |-> struct Stack { head: ?head } &*&
    nodes == match nodes {
        cons(h, t) => h,
        nil => std::ptr::null_mut()
    } &*&
    stack_nodes(nodes);

predicate stack_nodes(list<*mut Node> nodes) =
    match nodes {
        nil => emp,
        cons(n, rest) => node(n, ?v, ?next) &*& next == match rest { cons(h, _) => h, nil => std::ptr:: null_mut() } &*& stack_nodes(rest)
    };

lemma void stack_nodes_nil() req emp ens stack_nodes(nil);
{
}

lemma void stack_nodes_cons(*mut Node n, i32 v, *mut Node next, list<*mut Node> rest)
    req node(n, v, next) &*& next == match rest { cons(h, _) => h, nil => std::ptr::null_mut() } &*& stack_nodes(rest)
    ens stack_nodes(cons(n, rest));
{
}

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    req *n |-> ?head &*& stack_nodes(?nodes) &*& nodes == match nodes { cons(h, _) => h, nil => std::ptr::null_mut() }
    ens *n |-> ?new_head &*& stack_nodes(?new_nodes) &*& new_nodes == match new_nodes { cons(h, _) => h, nil => std::ptr::null_mut() };
{
    if !(*n).is_null() {
        let keep = p((**n).value);
        if keep {
            let old_head = *n;
            let old_next = (**n).next;
            close node(old_head, (**n).value, old_next);
            assert stack_nodes(cons(old_head, ?rest));
            open stack_nodes(cons(old_head, rest));
            filter_nodes(&raw mut (**n).next, p);
            close stack_nodes(cons(old_head, rest));
        } else {
            let next_ = (**n).next;
            let old_head = *n;
            assert stack_nodes(cons(old_head, ?rest));
            open stack_nodes(cons(old_head, rest));
            dealloc(old_head as *mut u8, Layout::new::<Node>());
            *n = next_;
            filter_nodes(n, p);
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    req stack_nodes(?nodes) &*& nodes == match nodes { cons(h, _) => h, nil => std::ptr::null_mut() }
    ens emp;
{
    if !n.is_null() {
        assert stack_nodes(cons(n, ?rest));
        open stack_nodes(cons(n, rest));
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {

    unsafe fn create() -> *mut Stack
        req emp
        ens stack(result, nil);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        close stack_nodes(nil)();
        close stack(stack, nil);
        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
        req stack(stack, ?nodes)
        ens stack(stack, cons(?new_node, nodes));
    {
        open stack(stack, nodes);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        close node(n, value, (*stack).head);
        close stack_nodes(cons(n, nodes));
        close stack(stack, cons(n, nodes));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
        req stack(stack, cons(?head_node, ?rest))
        ens stack(stack, rest) &*& result == ?val;
    {
        open stack(stack, cons(head_node, rest));
        let head = (*stack).head;
        let result = (*head).value;
        (*stack).head = (*head).next;
        open stack_nodes(cons(head, rest));
        dealloc(head as *mut u8, Layout::new::<Node>());
        close stack(stack, rest);
        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        req stack(stack, ?nodes)
        ens stack(stack, ?filtered_nodes);
    {
        open stack(stack, nodes);
        filter_nodes(&raw mut (*stack).head, p);
        close stack(stack, filtered_nodes);
    }

    unsafe fn dispose(stack: *mut Stack)
        req stack(stack, ?nodes)
        ens emp;
    {
        open stack(stack, nodes);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }

}

unsafe fn neq_20(x: i32) -> bool
    req emp
    ens emp &*& result == (x != 20);
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