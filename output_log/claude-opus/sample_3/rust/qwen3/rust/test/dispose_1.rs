use std::alloc::{dealloc, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

#[pred]
pred node(v: *mut Node, val: i32, nxt: *mut Node) =
    v != 0 &*&
    alloc_block(v as *mut u8, Layout::new::<Node>()) &*&
    (*v).value |-> val &*&
    (*v).next |-> nxt;

#[pred]
pred stack(s: *mut Stack, head: *mut Node) =
    s != 0 &*&
    alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    (*s).head |-> head;

#[pred]
pred list(p: *mut Node, vals: list<i32>) =
    p == 0 &*& vals == [] ||
    p != 0 &*&
    node(p, hd(vals), (*p).next) &*&
    list((*p).next, tl(vals));

#[lemma]
fn list_dispose_lem(p: *mut Node, vals: list<i32>)
    requires list(p, vals)
    ensures true
{
    if p != 0 {
        list_dispose_lem((*p).next, tl(vals));
    }
}

unsafe fn dispose_nodes(n: *mut Node)
    #[requires list(n, ?vals)]
    #[ensures emp]
{
    if !n.is_null() {
        let next = (*n).next;
        dispose_nodes(next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn dispose(stack: *mut Stack)
        #[requires stack != 0 &*& stack_points_to(stack, ?head) &*& list(head, ?vals)]
        #[ensures emp]
    {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[pred]
pred stack_points_to(s: *mut Stack, h: *mut Node) =
    s != 0 &*&
    alloc_block(s as *mut u8, Layout::new::<Stack>()) &*&
    (*s).head |-> h;