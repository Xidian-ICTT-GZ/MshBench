struct Node {
    next: *mut Node,
    value: i32,
}

struct Stack {
    head: *mut Node,
}

predicate node(n: *mut Node, count: i32) =
  if n == std::ptr::null_mut() {
    count == 0
  } else {
    exists rest: i32;
    count == rest + 1 &*& 
    n != std::ptr::null_mut() &*&
    std::ptr::Owned(n) &*&
    std::ptr::PointsTo(n as *mut i32, _) &*&
    std::ptr::PointsTo((n as *mut i32).offset(1), ?next) &*&
    node(next, rest)
  };

predicate stack(s: *mut Stack) =
  s != std::ptr::null_mut() &*&
  std::ptr::Owned(s) &*&
  std::ptr::PointsTo(s as *mut *mut Node, ?h) &*&
  node(h, _);

#[requires(stack(stack))]
#[ensures(result >= 0)]
unsafe fn stack_get_count(stack: *mut Stack) -> i32 {
    let mut n = (*stack).head;
    let mut i = 0;
    #[invariant(
      i >= 0 &*&
      node(n, ?remaining) &*&
      exists total: i32;
      total >= 0 &*&
      i + remaining == total
    )]
    loop {
        if n == std::ptr::null_mut() {
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