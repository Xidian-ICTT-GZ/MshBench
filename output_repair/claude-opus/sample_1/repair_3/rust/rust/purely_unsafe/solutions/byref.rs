use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

/*@
pred Nodes(n: *mut Node; values: list<i32>) =
    if n == 0 {
        values == nil
    } else {
        (*n).value |-> ?v &*&
        (*n).next |-> ?next &*&
        struct_Node_padding(n) &*&
        alloc_block(n as *mut u8, Layout::new_::<Node>()) &*&Nodes(next, ?rest) &*&
        values == cons(v, rest)
    };

pred Stack_own(s: *mut Stack; values: list<i32>) =
    (*s).head |-> ?head &*&
    struct_Stack_padding(s) &*&
    alloc_block(s as *mut u8, Layout::new_::<Stack>()) &*&
    Nodes(head, values);

pred NodeRef(n: *mut *mut Node; values: list<i32>) =
    *n |-> ?node &*&
    Nodes(node, values);

pred I32Pred(p: I32Predicate;) = true;
@*/

/*@
pred_ctor I32Pred_neq_20()() = true;
@*/

#[requires(NodeRef(n, ?values) &*& I32Pred(p))]
#[ensures(NodeRef(n, ?new_values) &*& I32Pred(p))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate) {
    //@ open NodeRef(n, values);
    if !(*n).is_null() {
        //@ open Nodes(*n, values);
        let keep = p((**n).value);
        if keep {
            //@ close Nodes(*n, _);
            //@ close NodeRef(&raw mut (**n).next, _);
            filter_nodes(&raw mut (**n).next, p);
            //@ open NodeRef(&raw mut (**n).next, ?new_tail);
            //@ close Nodes(*n, _);
        } else {
            let next_ = (**n).next;
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close NodeRef(n, _);
            filter_nodes(n, p);
            //@ open NodeRef(n, ?new_vals);
        }
    } else {
        //@ open Nodes(*n, values);
    }
    //@ close NodeRef(n, _);
}

#[requires(Nodes(n, ?values))]
#[ensures(true)]
unsafe fn dispose_nodes(n: *mut Node) {
    //@ open Nodes(n, values);
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(true)]
    #[ensures(Stack_own(result, nil))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close Nodes(0 as *mut Node, nil);
        //@ close Stack_own(stack, nil);
        stack
    }

    #[requires(Stack_own(stack, ?values))]
    #[ensures(Stack_own(stack, cons(value, values)))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        //@ open Stack_own(stack, values);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
        //@ close Nodes(n, cons(value, values));
        //@ close Stack_own(stack, cons(value, values));
    }

    #[requires(Stack_own(stack, cons(?v, ?rest)))]
    #[ensures(Stack_own(stack, rest) &*& result == v)]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        //@ open Stack_own(stack, cons(v, rest));
        let head = (*stack).head;
        //@ open Nodes(head, cons(v, rest));
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close Stack_own(stack, rest);
        result
    }

    #[requires(Stack_own(stack, ?values) &*& I32Pred(p))]
    #[ensures(Stack_own(stack, ?new_values) &*& I32Pred(p))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate) {
        //@ open Stack_own(stack, values);
        //@ close NodeRef(&raw mut (*stack).head, values);
        filter_nodes(&raw mut (*stack).head, p);
        //@ open NodeRef(&raw mut (*stack).head, ?new_values);
        //@ close Stack_own(stack, new_values);
    }

    #[requires(Stack_own(stack, ?values))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        //@ open Stack_own(stack, values);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(true)]
#[ensures(result == (x != 20))]
unsafe fn neq_20(x: i32) -> bool {
    x != 20
}

fn main() {
    unsafe {
        //@ close I32Pred(neq_20);
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);

        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}