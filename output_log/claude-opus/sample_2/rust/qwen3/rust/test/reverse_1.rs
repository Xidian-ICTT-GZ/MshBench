#[pred] struct node_pred(ptr: *mut Node, next: *mut Node) {
    ptr != std::ptr::null_mut() &*&
    (*ptr).next |-> next
}

#[pred] struct list_seg(head: *mut Node, tail: *mut Node) {
    head == tail ? emp :
    head != std::ptr::null_mut() &*&
    node_pred(head, next) &*&
    list_seg(next, tail)
}

#[requires(list_seg(n, std::ptr::null_mut()))]
#[ensures(list_seg(result, std::ptr::null_mut()))]
unsafe fn reverse_in_place(mut n: *mut Node) -> *mut Node {
    let mut m = std::ptr::null_mut();
    #[invariant(list_seg(n, std::ptr::null_mut()) * list_seg(m, n))]
    loop {
        if n.is_null() {
            return m;
        }
        let k = (*n).next;
        #[assert(node_pred(n, k))]
        (*n).next = m;
        m = n;
        n = k;
    }
}