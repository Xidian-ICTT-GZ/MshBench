use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
struct Node {
    value: i32,
    next: *mut Node,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

type I32Predicate = fn(i32) -> bool;

#[predicate]
#[verifier(public)]
fn node_pred(n: *mut Node) = n != 0 &*& malloc_block_Node(n) &*& (*n).value |-> _ &*& (*n).next |-> _ &*&
    (let next = (*n).next; let value = (*n).value; node_pred(next) &*& value == value) || // recursive
    n == 0 &*& emp;

#[predicate]
#[verifier(public)]
fn list_pred(head: *mut Node) =
    head == 0 ? emp : node_pred(head) &*& list_pred((*head).next);

#[predicate]
#[verifier(public)]
fn stack_pred(s: *mut Stack) = s != 0 &*& malloc_block_Stack(s) &*& (*s).head |-> ?h &*& list_pred(h);

#[lemma]
#[verifier(public)]
fn node_pred_split(n: *mut Node)
    requires node_pred(n),
    ensures (*n).next |-> ?next &*& (*n).value |-> ?value &*& node_pred(next)
{
    open node_pred(n);
    assert (*n).next |-> next;
    assert (*n).value |-> value;
    close node_pred(n);
}

#[lemma]
#[verifier(public)]
fn list_pred_split(head: *mut Node)
    requires list_pred(head),
    ensures head == 0 ? emp : node_pred(head) &*& list_pred((*head).next)
{
    open list_pred(head);
    close list_pred(head);
}

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
#[requires list_pred(n)]
#[ensures list_pred(result)]
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        open list_pred(n);
        open node_pred(n);
        let keep = p((*n).value);
        let next;
        let res;
        if keep {
            next = filter_nodes((*n).next, p);
            (*n).next = next;

            close node_pred(n);
            close list_pred(n);
            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            res = filter_nodes(next, p);
            close list_pred(res);
            res
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
#[requires list_pred(n)]
#[ensures emp]
{
    if !n.is_null() {
        open list_pred(n);
        open node_pred(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    #[requires emp]
    #[ensures stack_pred(result)]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        close list_pred(std::ptr::null_mut());
        close stack_pred(stack);

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    #[requires stack_pred(stack)]
    #[ensures stack_pred(stack)]
    {
        open stack_pred(stack);
        open list_pred((*stack).head);

        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;

        close node_pred(n);
        close list_pred(n);
        (*stack).head = n;

        close stack_pred(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    #[requires stack_pred(stack) &*& (*(*stack).head).value |-> ?v]
    #[ensures stack_pred(stack)]
    {
        open stack_pred(stack);
        open list_pred((*stack).head);
        open node_pred((*stack).head);
        assert (*stack).head != std::ptr::null_mut();

        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        close list_pred((*stack).head);
        close stack_pred(stack);

        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    #[requires stack_pred(stack)]
    #[ensures stack_pred(stack)]
    {
        open stack_pred(stack);
        open list_pred((*stack).head);

        let head = filter_nodes((*stack).head, p);

        (*stack).head = head;

        close stack_pred(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    #[requires stack_pred(stack)]
    #[ensures emp]
    {
        open stack_pred(stack);
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