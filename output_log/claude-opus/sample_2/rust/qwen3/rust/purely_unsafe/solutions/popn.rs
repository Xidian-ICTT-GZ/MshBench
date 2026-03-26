use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[predicate]
fn node_pred(n: *mut Node) = n != 0 &*&
    malloc_block_Node(n) &*&
    (*n).next |-> ?next &*&
    (*n).value |-> ?value &*&
    (next == 0 ? emp : node_pred(next));

#[predicate]
fn stack_pred(s: *mut Stack) = s != 0 &*&
    malloc_block_Stack(s) &*&
    (*s).head |-> ?head &*&
    (head == 0 ? emp : node_pred(head));

#[predicate]
fn list_pred(head: *mut Node, tail: *mut Node) = 
    head != 0 &*& tail != 0 &*&
    head == tail ? 
        node_pred(head)
    :
        node_pred(head) &*&
        list_pred((*head).next, tail);

#[predicate]
fn nodelist_pred(head: *mut Node, tail: *mut Node) =
    head != 0 &*& tail != 0 &*&
    head == tail ?
        node_pred(head)
    :
        node_pred(head) &*&
        nodelist_pred((*head).next, tail);

#[repr(C)]
struct Node {
    next: *mut Node,
    value: i32,
}

#[repr(C)]
struct Stack {
    head: *mut Node,
}

#[requires(true)]
#[ensures(result != 0 &*& node_pred(result))]
fn node_new(value: i32) -> *mut Node
    ensures
        node_pred(result)
{
    let layout = Layout::new::<Node>();
    let n = unsafe { alloc(layout) as *mut Node };
    if n.is_null() {
        handle_alloc_error(layout);
    }
    unsafe {
        (*n).next = 0 as *mut Node;
        (*n).value = value;
    }
    n
}

#[requires(node_pred(n))]
#[ensures(true)]
fn node_free(n: *mut Node)
{
    unsafe {
        let layout = Layout::new::<Node>();
        dealloc(n as *mut u8, layout);
    }
}

#[requires(stack_pred(s))]
#[ensures(true)]
fn stack_free(mut s: *mut Stack)
{
    unsafe {
        while (*s).head != 0 as *mut Node {
            let head = (*s).head;
            (*s).head = (*head).next;
            node_free(head);
        }
        let layout = Layout::new::<Stack>();
        dealloc(s as *mut u8, layout);
    }
}

#[requires(stack_pred(s))]
#[ensures(stack_pred(s))]
fn stack_push(s: *mut Stack, value: i32)
{
    let n = node_new(value);
    unsafe {
        (*n).next = (*s).head;
        (*s).head = n;
    }
}

#[requires(stack_pred(s))]
#[ensures(stack_pred(s))]
fn stack_pop(s: *mut Stack) -> i32
    requires exists|head| stack_pred(s) &*& (*s).head == head &*& head != 0;
{
    unsafe {
        let head = (*s).head;
        let val = (*head).value;
        (*s).head = (*head).next;
        node_free(head);
        val
    }
}