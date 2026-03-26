unsafe fn get_nodes_sum(nodes: *mut Node) -> i32


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


{

let result = get_nodes_sum((*stack).head);

result
}
}