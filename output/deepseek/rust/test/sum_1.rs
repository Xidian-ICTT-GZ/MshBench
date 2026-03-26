unsafe fn get_nodes_sum(nodes: *mut Node) -> i32 {
    #[requires(nodes.is_null() ==> true)]
    #[requires(!nodes.is_null() ==> 
        (*nodes).next.is_null() ==> true)]
    #[requires(!nodes.is_null() ==> 
        !(*nodes).next.is_null() ==> true)]
    #[ensures(result == old(result))]
    let mut result = 0;

    if !nodes.is_null() {
        #[requires(!nodes.is_null())]
        #[requires((*nodes).next.is_null() ==> true)]
        #[requires(!(*nodes).next.is_null() ==> true)]
        #[ensures(result == old(result))]
        result = get_nodes_sum((*nodes).next);
        result += (*nodes).value;
    }

    result
}
impl Stack {
    unsafe fn get_sum(stack: *mut Stack) -> i32 {
        #[requires(!stack.is_null())]
        #[requires((*stack).head.is_null() ==> true)]
        #[requires(!(*stack).head.is_null() ==> true)]
        let result = get_nodes_sum((*stack).head);

        result
    }
}