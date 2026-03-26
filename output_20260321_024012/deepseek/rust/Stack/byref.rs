use std::alloc::{Layout, alloc, handle_alloc_error, dealloc};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
//@ req node_lseg(*n, 0, ?vs) &*& [_]is_i32predicate(p, _);
//@ ens node_lseg(*n, 0, ?vs2) &*& forall(v, mem(v, vs) && !func_call(p, v)) ==> !mem(v, vs2);
{
    if !(*n).is_null() {
        //@ open node_lseg(*n, 0, vs);
        //@ open node(*n, _, _);
        let keep = p((**n).value);
        if keep {
            //@ close node(*n, (**n).next, (**n).value);
            //@ close node_lseg((**n).next, 0, tail(vs));
            filter_nodes(&raw mut (**n).next, p);
            //@ open node_lseg((**n).next, 0, ?vs_tail);
            //@ close node_lseg(*n, 0, cons((**n).value, vs_tail));
        } else {
            let next_ = (**n).next;
            //@ open node(*n, next_, _);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close node_lseg(*n, 0, tail(vs));
            filter_nodes(n, p);
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
//@ req node_lseg(n, 0, _);
//@ ens true;
{
    //@ open node_lseg(n, 0, _);
    if !n.is_null() {
        //@ open node(n, _, _);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    //@ req true;
    //@ ens stack(result, &[]);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();
        //@ close node_lseg(std::ptr::null_mut(), 0, []);
        //@ close stack(stack, []);
        stack
    }
    
    unsafe fn push(stack: *mut Stack, value: i32)
    //@ req stack(stack, ?vs);
    //@ ens stack(stack, cons(value, vs));
    {
        //@ open stack(stack, vs);
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        //@ close node(n, (*stack).head, value);
        //@ close node_lseg(n, 0, cons(value, vs));
        (*stack).head = n;
        //@ close stack(stack, cons(value, vs));
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    //@ req stack(stack, cons(?v, ?vs));
    //@ ens stack(stack, vs) &*& result == v;
    {
        //@ open stack(stack, cons(v, vs));
        let head = (*stack).head;
        //@ open node_lseg(head, 0, cons(v, vs));
        //@ open node(head, ?next, v);
        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());
        //@ close node_lseg((*stack).head, 0, vs);
        //@ close stack(stack, vs);
        result
    }
    
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    //@ req stack(stack, ?vs) &*& [_]is_i32predicate(p, _);
    //@ ens stack(stack, ?vs2) &*& forall(v, mem(v, vs) && !func_call(p, v)) ==> !mem(v, vs2);
    {
        //@ open stack(stack, vs);
        filter_nodes(&raw mut (*stack).head, p);
        //@ close stack(stack, _);
    }
    
    unsafe fn dispose(stack: *mut Stack)
    //@ req stack(stack, _);
    //@ ens true;
    {
        //@ open stack(stack, _);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

unsafe fn neq_20(x: i32) -> bool
//@ req true;
//@ ens result == (x != 20);
{
    x != 20
}

fn main() {
    unsafe {
        let s = Stack::create();
        Stack::push(s, 10);
        Stack::push(s, 20);
        //@ close is_i32predicate(neq_20, neq_20);
        Stack::filter(s, neq_20);
        Stack::dispose(s);
    }
}

/*@
predicate node(struct Node* n; struct Node* next, i32 value) =
    alloc_block(n, std::mem::size_of::<Node>()) &*&
    struct_Node_padding(n) &*&
    (*n).next |-> next &*&
    (*n).value |-> value;

predicate node_lseg(struct Node* first, struct Node* last; list<i32> values) =
    first == last ?
        values == []
    :
        node(first, ?next, ?value) &*& node_lseg(next, last, ?tail) &*& values == cons(value, tail);

predicate stack(struct Stack* s; list<i32> values) =
    alloc_block(s, std::mem::size_of::<Stack>()) &*&
    struct_Stack_padding(s) &*&
    (*s).head |-> ?head &*&
    node_lseg(head, 0, values);

predicate is_i32predicate(I32Predicate p, I32Predicate p_func) = p == p_func;
@*/