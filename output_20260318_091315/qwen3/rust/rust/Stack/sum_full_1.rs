#[predicate]
pub pred Node(node: *mut Node) = 
    node != std::ptr::null_mut() && 
    (*node).next |-> ?next &*& 
    (*node).value |-> ?value &*& 
    if next == std::ptr::null_mut() { true } else { Node(next) };

#[predicate]
pub pred Stack(stack: *mut Stack) = 
    stack != std::ptr:: null_mut() && 
    (*stack).head |-> ?head &*& 
    if head == std::ptr::null_mut() { true } else { Node(head) };

unsafe fn get_nodes_sum(node: *mut Node) -> i32
    requires node == std::ptr::null_mut() || Node(node);
    ensures node == std::ptr::null_mut() ? result == 0 : 
            (Node(node) &*& result == sum_nodes(node));
{
    let mut result = 0;
    if !node.is_null() {
        let tail_sum = get_nodes_sum((*node).next);
        result = (*node).value + tail_sum;
    }
    result
}

#[lemma]
fn sum_nodes_lemma(node: *mut Node)
    requires Node(node);
    ensures Node(node) &*& sum_nodes(node) == (*node).value + 
            (if (*node).next == std::ptr::null_mut() { 0 } else { sum_nodes((*node).next) });
{
    open Node(node);
    if (*node).next != std::ptr::null_mut() {
        sum_nodes_lemma((*node).next);
    }
    close Node(node);
}

#[predicate]
fn sum_nodes(node: *mut Node) -> i32 = 
    match node == std::ptr::null_mut() {
        true => 0,
        false => (*node).value + sum_nodes((*node).next),
    };

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32
        requires Stack(stack);
        ensures Stack(stack) &*& result == 
                (if (*stack).head == std::ptr::null_mut() { 0 } else { sum_nodes((*stack).head) });
    {
        let result = get_nodes_sum((*stack).head);
        result
    }
}