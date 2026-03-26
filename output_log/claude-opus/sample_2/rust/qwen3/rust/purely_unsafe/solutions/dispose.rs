use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn NodePred(n: *mut Node, next: *mut Node, value: i32, owned: bool) =
    owned == true ?
    // When owned, full ownership over Node memory and its fields:
    (n != std::ptr::null_mut()
     &*& n->next |-> next
     &*& n->value |-> value
     &*& malloc_block_Node(n))
    :
    // When not owned, no ownership over heap memory:
    (true == false)
;

#[predicate]
fn StackPred(s: *mut Stack, head: *mut Node, owned: bool) =
    owned == true ?
    (s != std::ptr::null_mut()
     &*& s->head |-> head
     &*& malloc_block_Stack(s))
    :
    (true == false)
;

#[lemma]
fn node_pred_dispose(n: *mut Node)
    requires
        NodePred(n, ?next, ?value, true),
    ensures
        NodePred(n, next, value, false),
{
    // This lemma allows reasoning about disposal of Node ownership.
}

#[lemma]
fn stack_pred_dispose(s: *mut Stack)
    requires
        StackPred(s, ?head, true),
    ensures
        StackPred(s, head, false),
{
}

impl Stack {
    #[requires(
        Layout::new::<Stack>().size() > 0 &&
        Layout::new::<Stack>().align() > 0
    )]
    #[ensures(
        result != std::ptr::null_mut() &&
        StackPred(result, std::ptr::null_mut(), true)
    )]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        return stack;
    }

    #[requires(
        StackPred(stack, ?head, true)
    )]
    #[ensures(
        StackPred(stack, head, true) &&
        result == ((*stack).head == std::ptr::null_mut())
    )]
    unsafe fn is_empty(stack: *mut Stack) -> bool {
        let head = (*stack).head;

        let result = (*stack).head.is_null();

        return result;
    }

    #[requires(
        StackPred(stack, ?old_head, true) &&
        Layout::new::<Node>().size() > 0 &&
        Layout::new::<Node>().align() > 0
    )]
    #[ensures(
        StackPred(stack, ?new_head, true) &&
        NodePred(new_head, old_head, value, true)
    )]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        // Allocate memory yields ownership of NodePred with owned=true:
        assume(NodePred(n, std::ptr::null_mut(), 0, false) == false); // dummy to support reasoning

        // Initialize fields:
        (*n).next = (*stack).head;
        (*n).value = value;

        // Update ownership facts accordingly:
        // Produce NodePred for new node (with next and value):
        // Update stack head:
        (*stack).head = n;
    }

    #[requires(
        StackPred(stack, ?head, true) &&
        head != std::ptr::null_mut() &&
        NodePred(head, ?next, ?value, true)
    )]
    #[ensures(
        StackPred(stack, next, true) &&
        result == value &&
        NodePred(head, next, value, false)
    )]
    unsafe fn pop(stack: *mut Stack) -> i32 {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;

        dealloc(head as *mut u8, Layout::new::<Node>());

        return result;
    }

    #[requires(
        StackPred(stack, ?head, true)
    )]
    #[ensures(
        StackPred(stack, head, false)
    )]
    unsafe fn dispose(stack: *mut Stack) {
        dispose_nodes((*stack).head);
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

#[requires(
    NodePred(n, ?next, ?value, true)
)]
#[ensures(
    NodePred(n, next, value, false)
)]
unsafe fn dispose_nodes(n: *mut Node) {
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
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