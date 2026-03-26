unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}
impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        let result = get_nodes_sum((*stack).head);

        result
    }
}

#[verifast::predicate]
pub fn node_pred(n: *mut Node, value: i32, next: *mut Node) -> bool {
    std::ptr::raw_mut_field!(n, value) |-> value &*&
    std::ptr::raw_mut_field!(n, next) |-> next
}

#[verifast::predicate]
pub fn nodes_sum_pred(nodes: *mut Node, sum: i32) -> bool {
    if nodes.is_null() {
        true
    } else {
        std::exists(|(value, next, rest_sum): (i32, *mut Node, i32)|
            node_pred(nodes, value, next) &*&
            nodes_sum_pred(next, rest_sum) &*&
            sum == value + rest_sum
        )
    }
}

#[verifast::predicate]
pub fn stack_pred(s: *mut Stack, head: *mut Node) -> bool {
    std::ptr::raw_mut_field!(s, head) |-> head
}

unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    #[verifast::requires(nodes_sum_pred(nodes, ?sum))]
    #[verifast::ensures(nodes_sum_pred(nodes, sum) &*& result == sum)]
    let mut result = 0;

    if !nodes.is_null() {
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}

impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        #[verifast::requires(std::exists(|(head, sum): (*mut Node, i32)|
            stack_pred(stack, head) &*&
            nodes_sum_pred(head, sum)
        ))]
        #[verifast::ensures(std::exists(|(head, sum): (*mut Node, i32)|
            stack_pred(stack, head) &*&
            nodes_sum_pred(head, sum) &*&
            result == sum
        ))]
        let result = get_nodes_sum((*stack).head);

        result
    }
}