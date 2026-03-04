unsafe fn get_nodes_sum(nodes: *mut Node) -> i32
//@ req Nodes(nodes, ?count);
//@ ens Nodes(nodes, count);
{
let mut result = 0;
//@ open Nodes(nodes, count);
if !nodes.is_null() {
result = get_nodes_sum((*nodes).next);
result += (*nodes).value;
}
//@ close Nodes(nodes, count);
result
}
impl Stack {
unsafe fn get_sum(stack: *mut Stack) -> i32
//@ req Stack(stack, ?count);
//@ ens Stack(stack, count);
{
//@ open Stack(stack, count);
let result = get_nodes_sum((*stack).head);
//@ close Stack(stack, count);
result
}
}