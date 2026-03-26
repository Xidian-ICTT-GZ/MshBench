use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};

#[repr(C)]
pub struct Node {
    next: *mut Node,
    value: i32,
}

#[predicate]
pub fn nodes_list(mut ptr: *mut Node) -> bool {
    if ptr == std::ptr::null_mut() {
        true
    } else {
        ptr != std::ptr::null_mut() &*&
        ptr as usize != 0 &*&
        ^match unsafe { *ptr } {
            Node { next, value: _ } => nodes_list(next)
        }
    }
}

#[predicate]
pub fn node(ptr: *mut Node) = ptr != std::ptr::null_mut() &*&
    malloc_block_Node(ptr) &*&
    nodes_list(ptr);

#[requires(true)]
#[ensures(!result.is_null() &*& malloc_block_Node(result) &*& node(result))]
pub unsafe fn node_new(val: i32) -> *mut Node;
#[requires(true)]
#[ensures(malloc_block_Node(result))]
unsafe fn alloc_node() -> *mut Node {
    let layout = Layout::new::<Node>();
    let ptr = alloc(layout) as *mut Node;
    if ptr.is_null() { handle_alloc_error(layout) }
    ptr
}

#[requires(true)]
#[ensures(malloc_block_Node(result) &*& node(result))]
pub unsafe fn node_new(val: i32) -> *mut Node {
    let n = alloc_node();
    (*n).next = std::ptr::null_mut();
    (*n).value = val;
    n
}

#[requires(node(n))]
#[ensures(emp)]
pub unsafe fn node_delete(n: *mut Node) {
    let layout = Layout::new::<Node>();
    dealloc(n as *mut u8, layout);
}

#[requires(nodes_list(head))]
pub fn list_len(mut head: *mut Node) -> usize;
#[requires(true)]
#[ensures(result == 0)]
fn list_len_null() -> usize;

fn list_len(mut head: *mut Node) -> usize {
    let mut len = 0;
    while head != std::ptr::null_mut()
        //@ invariant nodes_list(head);
    {
        //@ open nodes_list(head);
        unsafe {
            head = (*head).next;
        }
        len += 1;
    }
    len
}

#[requires(nodes_list(head))]
#[ensures(nodes_list(head) &*& result == old(list_len(head)))]
pub fn dummy_len(head: *mut Node) -> usize {
    list_len(head)
}

#[requires(nodes_list(head))]
#[ensures(emp)]
pub unsafe fn list_free(mut head: *mut Node) {
    while head != std::ptr::null_mut()
        //@ invariant nodes_list(head);
    {
        //@ open nodes_list(head);
        let next = (*head).next;
        node_delete(head);
        head = next;
    }
}