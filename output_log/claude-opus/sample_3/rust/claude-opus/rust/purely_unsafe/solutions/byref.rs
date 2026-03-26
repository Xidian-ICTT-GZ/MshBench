use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

type I32Predicate = unsafe fn(i32) -> bool;

predicate malloc_block_Node(void* p) = malloc_block(p, sizeof(Node));
predicate malloc_block_Stack(void* p) = malloc_block(p, sizeof(Stack));

predicate nodes(n: *mut Node) =
    if n == std::ptr::null_mut() {
        emp
    } else {
        malloc_block_Node(n) &*&
        (*n).value |-> ?v &*&
        (*n).next |-> ?next &*&
        nodes(next)
    };

predicate stack(s: *mut Stack) =
    malloc_block_Stack(s) &*&
    (*s).head |-> ?h &*&
    nodes(h);

predicate pred_spec(p: I32Predicate) = pointer(p, _) &*& closure_pred(p);

predicate closure_pred(p: I32Predicate) = true;

predicate pointer_to_nodes(n: *mut *mut Node) =
    pointer(n, ?node) &*& nodes(node);

#[requires(pointer_to_nodes(n) &*& pred_spec(p))]
#[ensures(pointer_to_nodes(n) &*& pred_spec(p))]
unsafe fn filter_nodes(n: *mut *mut Node, p: I32Predicate)
    //@ requires pointer_to_nodes(n) &*& pred_spec(p);
    //@ ensures pointer_to_nodes(n) &*& pred_spec(p);
{
    if !(*n).is_null() {
        open pointer_to_nodes(n);
        open pointer(n, ?node);
        open nodes(node);
        let keep = p((**n).value);
        if keep {
            //@ close pointer(&raw mut (**n).next, (*node).next);
            //@ close pointer_to_nodes(&raw mut (**n).next);
            filter_nodes(&raw mut (**n).next, p);
            //@ close nodes(node);
            //@ close pointer(n, node);
            //@ close pointer_to_nodes(n);
        } else {
            let next_ = (**n).next;
            //@ close nodes(next_);
            dealloc(*n as *mut u8, Layout::new::<Node>());
            *n = next_;
            //@ close pointer_to_nodes(n);
            filter_nodes(n, p);
            //@ close pointer_to_nodes(n);
        }
    } else {
        //@ close pointer_to_nodes(n);
    }
}

#[requires(nodes(n))]
#[ensures(emp)]
unsafe fn dispose_nodes(n: *mut Node)
    //@ requires nodes(n);
    //@ ensures emp;
{
    if n != std::ptr::null_mut() {
        open nodes(n);
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    #[requires(emp)]
    #[ensures(stack(result))]
    unsafe fn create() -> *mut Stack
        //@ requires emp;
        //@ ensures stack(result);
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        //@ close nodes(std::ptr::null_mut());
        //@ close pointer(&raw mut (*stack).head, std::ptr::null_mut());
        //@ close stack(stack);
        stack
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn push(stack: *mut Stack, value: i32)
        //@ requires stack(stack);
        //@ ensures stack(stack);
    {
        open stack(stack);
        let head = (*stack).head;
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = head;
        (*n).value = value;

        //@ close nodes(head);
        //@ close nodes(n);
        (*stack).head = n;
        close stack(stack);
    }

    #[requires(stack(stack))]
    #[ensures(stack(stack))]
    unsafe fn pop(stack: *mut Stack) -> i32
        //@ requires stack(stack);
        //@ ensures stack(stack);
    {
        open stack(stack);
        let head = (*stack).head;
        open nodes(head);

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        close stack(stack);
        result
    }

    #[requires(stack(stack) &*& pred_spec(p))]
    #[ensures(stack(stack) &*& pred_spec(p))]
    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
        //@ requires stack(stack) &*& pred_spec(p);
        //@ ensures stack(stack) &*& pred_spec(p);
    {
        open stack(stack);
        //@ close pointer_to_nodes(&raw mut (*stack).head);
        filter_nodes(&raw mut (*stack).head, p);
        close stack(stack);
    }

    #[requires(stack(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack)
        //@ requires stack(stack);
        //@ ensures emp;
    {
        open stack(stack);
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(emp)]
#[ensures(true)]
unsafe fn neq_20(x: i32) -> bool
    //@ requires emp;
    //@ ensures true;
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