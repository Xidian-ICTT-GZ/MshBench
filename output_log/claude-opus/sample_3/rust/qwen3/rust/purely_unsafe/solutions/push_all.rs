use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred]
pub unsafe fn NodePred(node: *mut Node) -> bool
    requires node != std::ptr::null_mut()
{
    node |-> Node { next: _, value: _ }
}
#[pred]  
struct NodePred {
    next: *mut Node,
    value: i32,
}

#[pred]  
struct StackPred {
    head: *mut Node,
}

#[pred]
pub unsafe fn ListPred(head: *mut Node) -> bool
{
    match head {
        std::ptr::null_mut() => 
            true,
        _ => 
            exists n: *mut Node, v: i32, tail: *mut Node {
                head |-> NodePred { next: tail, value: v } *
                ListPred(tail)
            },
    }
}

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    #[requires(Layout::new::<Stack>().size() > 0)]
    #[ensures(result |-> StackPred { head: std::ptr::null_mut() })]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(stack |-> StackPred { head: head } * ListPred(head))]
    #[ensures(result == count_list(head) && stack |-> StackPred { head: head } * ListPred(head))]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        #[invariant(n |-> NodePred { next: next_n, value: _ } * ListPred(next_n) * i == count_list(head) - count_list(n) 
                    || (n == std::ptr::null_mut() && i == count_list(head)))]
        loop {
            if n.is_null() {
                break;
            }

            n = (*n).next;
            i += 1;
        }

        i
    }

    #[requires(stack |-> StackPred { head: h1 } * ListPred(h1) *
               other |-> StackPred { head: h2 } * ListPred(h2))]
    #[ensures(stack |-> StackPred { head: h2 } * ListPred(h2))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(n |-> NodePred { next: next_n, value: _ } * ListPred(next_n))]
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

    #[requires(stack |-> StackPred { head: h } * ListPred(h) *
               Layout::new::<Node>().size() > 0)]
    #[ensures(stack |-> StackPred { head: n } * n |-> NodePred { next: h, value: value } * ListPred(h))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack |-> StackPred { head: h } * h |-> NodePred { next: tail, value: v } * ListPred(tail))]
    #[ensures(result == v * stack |-> StackPred { head: tail } * ListPred(tail))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(stack |-> StackPred { head: h } * ListPred(h))]
    #[ensures(true)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[lem]
fn count_list(head: *mut Node) -> i32 {
    match head {
        std::ptr::null_mut() => 0,
        _ => {
            let n = head;
            let v = (*n).value;
            let tail = (*n).next;
            1 + count_list(tail)
        }
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