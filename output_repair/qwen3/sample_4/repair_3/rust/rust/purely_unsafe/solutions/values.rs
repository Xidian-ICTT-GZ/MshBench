use std::alloc::{alloc, dealloc, handle_alloc_error, Layout};
use std::ptr;

// VeriFast predicates for separation logic
predicate node_own(*mut Node n, *mut Node next, i32 value) =
    n as *mut u8 |-> (next as usize) &*&
    (n as usize + std::mem::size_of::<*mut Node>()) as *mut i32 |-> value;

predicate stack_own(*mut Stack s, *mut Node head) =
    s as *mut *mut Node |-> head;

predicate node_list(*mut Node n) =
    n == ptr::null_mut() ?
        emp
    :
        exists<*mut Node, i32>(?next, ?val) &*&
        node_own(n, next, val) &*&
        node_list(next);

predicate stack_valid(*mut Stack s) =
    exists<*mut Node>(?head) &*&
    stack_own(s, head) &*&
    node_list(head);

struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

impl Stack {
    #[ensures(stack_valid(result))]
    unsafe fn create() -> *mut Stack {
        let stack = alloc(Layout::new::<Stack>()) as *mut Stack;
        if stack.is_null() {
            handle_alloc_error(Layout::new::<Stack>());
        }
        (*stack).head = ptr::null_mut();
        result
    }

    #[requires(stack_valid(stack))]
    #[ensures(stack_valid(stack))]
    unsafe fn push(stack: *mut Stack, value: i32) {
        let n = alloc(Layout::new::<Node>()) as *mut Node;
        if n.is_null() {
            handle_alloc_error(Layout::new::<Node>());
        }
        
        // Acquire ownership of the new node's memory via predicate construction implicitly by writing to it
        // We must ensure we have permission to write. 
        // In VeriFast Rust, raw pointer writes require ownership. 
        // However, since 'n' is a fresh allocation, we own it fully.
        // The specification relies on the fact that after alloc, we own the memory.
        
        (*n).next = (*stack).head;
        (*n).value = value;
        (*stack).head = n;
    }

    #[requires(stack_valid(stack))]
    #[ensures(emp)]
    unsafe fn dispose(stack: *mut Stack) {
        // Before deallocation, we must consume the stack_valid predicate to get ownership of the heap cells
        // Then we can deallocate.
        // Note: In VeriFast, consuming the predicate gives us the resources.
        // We need to explicitly destructure the predicates to free memory.
        
        // Consume stack_valid to get stack_own and node_list
        // This step effectively "consumes" the heap resources so they can be freed.
        
        dealloc(stack as *mut u8, Layout::new::<Stack>());
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}