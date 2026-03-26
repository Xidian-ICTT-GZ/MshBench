use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred] struct NodePred(node: *mut Node) {
    node |-> Node { next: next, value: value } *
    if next.is_null() then true else true
}

#[pred] struct StackPred(stack: *mut Stack) {
    stack |-> Stack { head: head }
}

#[pred] struct ListPred(head: *mut Node) {
    switch head {
        std::ptr::null_mut() => emp,
        _ => exists next: *mut Node, value: i32 {
            head |-> Node { next: next, value: value } * ListPred(next)
        }
    }
}

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

impl Stack {
    #[requires(Layout::new::<Stack>().size() > 0)]
    #[ensures(StackPred(result) &*& ListPred(std::ptr::null_mut()))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    #[requires(StackPred(stack) &*& ListPred((*stack).head))]
    #[ensures(result == count_list((*stack).head) &*& StackPred(stack) &*& ListPred((*stack).head))]
    unsafe fn get_count(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let mut n = head;
        let mut i = 0;

        #[invariant((n == std::ptr::null_mut() ?
                    StackPred(stack) &*& ListPred(n) &*& i == count_list(head)
                    :
                    StackPred(stack) &*& ListPred(n) &*& i + count_list(n) == count_list(head)))]
        loop {
            if n.is_null() {
                break;
            }

            let next_n = (*n).next;

            n = next_n;
            i += 1;
        }

        i
    }

    #[requires(StackPred(stack) &*& ListPred((*stack).head) &*&
               StackPred(other) &*& ListPred((*other).head))]
    #[ensures(StackPred(stack) &*& ListPred((*stack).head) &*&
              ListPred(std::ptr::null_mut()))]
    unsafe fn push_all(stack: *mut Stack, other: *mut Stack) {
        let head0 = (*other).head;
        dealloc(other as *mut u8, Layout::new::<Stack>());
        let mut n = head0;

        if !n.is_null() {
            #[invariant(ListPred(n) &*& StackPred(stack))]
            loop {
                let next_n = (*n).next;
                if next_n.is_null() {
                    break;
                }
                n = next_n;
            }

            (*n).next = (*stack).head;

            (*stack).head = head0;
        }
    }

    #[requires(StackPred(stack) &*& ListPred((*stack).head) &*& Layout::new::<Node>().size() > 0)]
    #[ensures(StackPred(stack) &*& ListPred((*stack).head) &*&
              (*stack).head |-> Node { next: old_head, value: value } * ListPred(old_head))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let old_head = (*stack).head;

        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = old_head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(StackPred(stack) &*& ListPred((*stack).head) &*&
               (*stack).head |-> Node { next: tail, value: v } * ListPred(tail))]
    #[ensures(result == v &*& StackPred(stack) &*& ListPred((*stack).head))]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    #[requires(StackPred(stack) &*& ListPred((*stack).head))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[lem]
fn count_list(head: *mut Node) -> i32
    requires true
    ensures true
{
    switch head {
        std::ptr::null_mut() => 0,
        _ => {
            let n = head;
            let tail = unsafe { (*n).next };
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