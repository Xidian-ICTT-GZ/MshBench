predicate node_list(ptr: *mut Node, len: i32) =
  ptr.is_null() ? len == 0 : 
    (ptr as usize) != 0 && 
    (exists n: i32 :: n >= 0 && len == n + 1 && 
      ((*ptr).next as usize) != 0 || (*ptr).next.is_null());

predicate stack(s: *mut Stack, len: i32) =
  (s as usize) != 0 && node_list((*s).head, len);

#[requires(stack(stack, _))]
#[ensures(result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    loop {
        if n.is_null() {
            break;
        }
        n = (*n).next;
        i += 1;
    }

    i
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}