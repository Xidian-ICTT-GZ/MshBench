use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    value: i32,
    next: *mut Node,
}

struct Stack {
    head: *mut Node,
}

predicate node_pred(n: *mut Node;) =
    n != 0 &*&
    malloc_block_Node(n) &*&
    (*n).value |-> ?v &*&
    (*n).next |-> ?nx &*&
    list_pred(nx)()
;

predicate list_pred(head: *mut Node();) =
    head == 0 ?
        emp
    :
        node_pred(head)
;

predicate stack_pred(s: *mut Stack;) =
    s != 0 &*&
    malloc_block_Stack(s) &*&
    (*s).head |-> ?h &*&
    list_pred(h)()
;

lemma void node_pred_split(Node* n)
    requires node_pred(n);
    ensures (*n).value |-> ?v &*& (*n).next |-> ?nx &*& list_pred(nx)() &*& malloc_block_Node(n);
{
    open node_pred(n);
    close node_pred(n);
}

lemma void list_pred_split(Node* head)
    requires list_pred(head)();
    ensures head == 0 ? emp : node_pred(head) * list_pred((Node*)(*(head)).next)();
{
    open list_pred(head)();
    if (head != 0) {
        open node_pred(head);
        close node_pred(head);
        close list_pred((Node*)(*(head)).next)();
    }
    close list_pred(head)();
}

unsafe fn filter_nodes(n: *mut Node, p: I32Predicate) -> *mut Node
#[requires list_pred(n)()]
#[ensures list_pred(result)()]
{
    if n.is_null() {
        std::ptr::null_mut()
    } else {
        open list_pred(n)();
        open node_pred(n);
        let v = (*n).value;
        let next = (*n).next;
        close list_pred(next)();

        let keep = p(v);

        if keep {
            let filtered_next = filter_nodes(next, p);

            (*n).next = filtered_next;

            close node_pred(n);
            close list_pred(n)();

            filtered_next
        } else {
            dealloc(n as *mut u8, Layout::new::<Node>());
            close list_pred(next)();

            filter_nodes(next, p)
        }
    }
}

unsafe fn dispose_nodes(n: *mut Node)
#[requires list_pred(n)()]
#[ensures emp]
{
    if !n.is_null() {
        open list_pred(n)();
        open node_pred(n);
        let next = (*n).next;
        close list_pred(next)();

        dispose_nodes(next);

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

        close stack_pred(stack);

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32)
    #[requires stack_pred(stack)]
    #[ensures stack_pred(stack)]
    {
        open stack_pred(stack);
        let old_head = (*stack).head;

        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }

        (*n).value = value;
        (*n).next = old_head;

        close node_pred(n);
        close list_pred(n)();

        (*stack).head = n;

        close (*stack).head |-> n &*& list_pred(n)();
        close stack_pred(stack);
    }

    unsafe fn pop(stack: *mut Stack) -> i32
    #[requires stack_pred(stack) &*& (*(*stack).head).value |-> ?v &*& (*(*stack).head).next |-> ?nx &*& list_pred(nx)()]
    #[ensures stack_pred(stack) &*& result == v]
    {
        open stack_pred(stack);
        let head = (*stack).head;
        open node_pred(head);
        let result = (*head).value;
        let next = (*head).next;

        (*stack).head = next;

        close list_pred(next)();
        close (*stack).head |-> next &*& list_pred(next)();
        close stack_pred(stack);

        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn filter(stack: *mut Stack, p: I32Predicate)
    #[requires stack_pred(stack)]
    #[ensures stack_pred(stack)]
    {
        open stack_pred(stack);
        let head = (*stack).head;
        close list_pred(head)();
        let filtered_head = filter_nodes(head, p);
        (*stack).head = filtered_head;
        close (*stack).head |-> filtered_head &*& list_pred(filtered_head)();
        close stack_pred(stack);
    }

    unsafe fn dispose(stack: *mut Stack)
    #[requires stack_pred(stack)]
    #[ensures emp]
    {
        open stack_pred(stack);
        let head = (*stack).head;
        close list_pred(head)();
        dispose_nodes(head);
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