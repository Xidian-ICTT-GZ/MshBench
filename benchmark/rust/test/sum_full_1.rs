/*@
fix i32s_sum(values: i32s) -> i32 {
match values {
i32s_nil => 0,
i32s_cons(value, values0) => value + i32s_sum(values0),
}
}
@*/
unsafe fn get_nodes_sum(node: *mut Node) -> i32
//@ req Nodes(node, ?values);
//@ ens Nodes(node, values) &*& result == i32s_sum(values);
{
//@ open Nodes(node, values);
let mut result = 0;
if !node.is_null() {
let tail_sum = get_nodes_sum((*node).next);
result = (*node).value + tail_sum;
}
//@ close Nodes(node, values);
result
}
impl Stack {
unsafe fn get_sum(stack: *mut Stack) -> i32
//@ req Stack(stack, ?values);
//@ ens Stack(stack, values) &*& result == i32s_sum(values);
{
//@ open Stack(stack, values);
let result = get_nodes_sum((*stack).head);
//@ close Stack(stack, values);
result
}
}