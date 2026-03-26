use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[pred node_pred(n: *mut Node) = 
    n != 0 &*& 
    malloc_block_Node(n) &*&
    let next = (*n).next;
    let value = (*n).value;
    node_pred(next) * value == value
]

#[pred stack_pred(s: *mut Stack) = 
    s != 0 &*& 
    malloc_block_Stack(s) &*&
    node_pred((*s).head)
]

#[pred list_pred(head: *mut Node) = 
    head == 0 ? emp : 
    node_pred(head) * list_pred((*head).next)
]

#[lemma]
fn node_pred_split(n: *mut Node)
    requires node_pred(n),
    ensures node_pred((*n).next) * (*n).value == (*n).value
{
    // VeriFast can infer this automatically via predicate unfolding
}

#[lemma]
fn list_pred_split(head: *mut Node)
    requires list_pred(head),
    ensures head == 0 ? emp : node_pred(head) * list_pred((*head).next)
{
    // VeriFast can infer this automatically
}

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
#[requires list_pred(n)]
#[ensures list_pred(result)]
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        let keep = p((*n).value);
        let next;
        if keep {
            next = filter_nodes((*n).next, p);

            (*n).next = next;

            n
        } else {
            next = (*n).next;
            dealloc(n as *mut u8, Layout::new::<Node>());
            let result = filter_nodes(next, p);
            result
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
#[requires list_pred(n)]
#[ensures emp]
{
    if !n.is_null() {
        dispose_nodes((*n).next);
        dealloc(n as *mut u8, Layout::new::<Node>());
    }
}

impl Stack {
    unsafe fn create() -> *mut Stack
    #[requires true]
    #[ensures stack_pred(result)]
    {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    #[requires stack_pred(stack)]
    #[ensures stack_pred(stack)]
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
    #[requires stack_pred(stack) * (*(*stack).head).value |-> ?v]
    #[ensures stack_pred(stack)]
    {
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    #[requires stack_pred(stack)]
    #[ensures stack_pred(stack)]
    {
        let head = filter_nodes((*stack).head, p);

        (*stack).head = head;
    }

    unsafe fn dispose(stack: *mut Stack)
    #[requires stack_pred(stack)]
    #[ensures emp]
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