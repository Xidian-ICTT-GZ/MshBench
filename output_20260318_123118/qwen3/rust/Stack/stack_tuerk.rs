#[predicate]
fn node(n: *mut Node, next: *mut Node, value: i32) -> bool {
    n != std::ptr::null_mut() && (*n).next == next && (*n).value == value
}

#[predicate]
fn stack_nodes(head: *mut Node) -> bool {
    match head.is_null() {
        true => true,
        false => exists(next: *mut Node, value: i32, node(head, next, value) && stack_nodes(next))
    }
}

#[predicate]
fn stack(s: *mut Stack, head: *mut Node) -> bool {
    s != std::ptr:: null_mut() && (*s).head == head && stack_nodes(head)
}

unsafe fn stack_get_count(stack: *mut Stack) -> i32
    requires stack(stack, ?head) &*& stack_nodes(head) == stack_nodes(?nodes),
    ensures stack(stack, head) &*& result == length_of_stack(nodes);

{
    let mut n = (*stack).head;
    let mut i = 0;
    loop 
        invariant stack(stack, ?orig_head) &*& n == ?current &*& stack_nodes(current) &*& i == length_of_stack(orig_head) - length_of_stack(current);
    {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }
    
    i
}

#[predicate]
fn length_of_stack(n: *mut Node) -> i32 {
    match n.is_null() {
        true => 0,
        false => 1 + length_of_stack((*n).next)
    }
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}