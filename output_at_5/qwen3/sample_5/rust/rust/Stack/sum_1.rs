unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ requires nodes == null || is_node_list(nodes);
{
let mut result = 0;

if !nodes.is_null() {
result = get_nodes_sum((*nodes).next);
result += (*nodes).value;
}

result
}
impl Stack {
unsafe fn get_sum(stack: *mut Stack) -> i32
//@ requires stack == null || is_stack(*stack);
{

let result = get_nodes_sum((*stack).head);

result
}
}