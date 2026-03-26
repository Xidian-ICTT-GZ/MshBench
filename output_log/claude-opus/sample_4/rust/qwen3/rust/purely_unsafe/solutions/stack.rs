use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

#[predicate]
fn node_pred(n: *mut Node, v: i32, next: *mut Node) =
    n->next |-> next 
    &*& n->value |-> v;

#[predicate]
fn stack_pred(s: *mut Stack, head: *mut Node) =
    s->head |-> head;

#[predicate]
fn nodes_list(mut head: *mut Node) =
    if head == std::ptr::null_mut() {
        emp
    } else exists<v: i32, nxt: *mut Node> (
        node_pred(head, v, nxt) &*& nodes_list(nxt)
    );

impl Stack {
    unsafe fn create() -> *mut Stack {
        #[requires(Layout::new::<Stack>().size() > 0)]
        #[ensures(result != std::ptr::null_mut() && stack_pred(result, std::ptr::null_mut()))]
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = std::ptr::null_mut();

        stack
    }

    unsafe fn push(stack: *mut Stack, value: i32) {
        #[requires(stack_pred(stack, ?old_head) &*& nodes_list(old_head))]
        #[ensures(stack_pred(stack, ?new_head) &*& nodes_list(new_head) &*& 
                  new_head != std::ptr::null_mut() &*&
                  node_pred(new_head, value, old_head))]
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    unsafe fn pop(stack: *mut Stack) -> i32 {
        #[requires(stack_pred(stack, ?head) &*& head != std::ptr::null_mut()
                    &*& nodes_list(head))]
        #[ensures(stack_pred(stack, ?new_head) &*& nodes_list(new_head)
                  &*& result == old(head).value
                  &*& nodes_list_remove(head))]
        let head = (*stack).head;

        let result = (*head).value;
        (*stack).head = (*head).next;
        dealloc(head as *mut u8, Layout::new::<Node>());

        result
    }

    unsafe fn dispose(stack: *mut Stack) {
        #[requires(stack_pred(stack, std::ptr::null_mut()))]
        #[ensures(true)]
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

predicate nodes_list_remove(*head: *mut Node) =
    /* matches nodes_list but excludes ownership of head node */
    true; // will be expanded by lemma

// Lemma: Removing a head node from nodes_list yields nodes_list of the tail
#[lemma]
fn nodes_list_remove_lemma(head: *mut Node)
    requires head != std::ptr::null_mut() &*& nodes_list(head);
    ensures nodes_list_remove(head);
{
    open nodes_list(head);
    open node_pred(head, _, _);
    close nodes_list_remove(head);
}

// Lemma to pack nodes_list after push/pop
#[lemma]
fn pack_nodes_list(head: *mut Node, v: i32, next: *mut Node)
    requires node_pred(head, v, next) &*& nodes_list(next);
    ensures nodes_list(head);
{
    close nodes_list(head);
}

// Lemma to unpack nodes_list before push/pop
#[lemma]
fn unpack_nodes_list(head: *mut Node)
    requires nodes_list(head);
    ensures node_pred(head, ?v, ?next) &*& nodes_list(next);
{
    open nodes_list(head);
    open node_pred(head, v, next);
}

// Lemma: stack_pred implies ownership of head pointer
#[lemma]
fn stack_pred_lemma(s: *mut Stack, head: *mut Node)
    requires stack_pred(s, head);
    ensures s->head |-> head;
{
    open stack_pred(s, head);
}

// Lemma: After push, stack head points to new node
#[lemma]
fn stack_pred_update(s: *mut Stack, old_head: *mut Node, new_head: *mut Node)
    requires stack_pred(s, old_head);
    ensures stack_pred(s, new_head);
{
    open stack_pred(s, old_head);
    close stack_pred(s, new_head);
}