#[pred mem_block(p: *const u8, n: usize) = 
    p != 0 && 
    exists<bytes>(b: [u8; _]) [
        b.len == n &&
        points_to_block(p, b)
    ]
]

#[requires(mem_block(p1, count) * mem_block(p2, count))]
#[ensures(result == 0 ==> forall<i: usize> (0 <= i && i < count ==> *p1.add(i) == *p2.add(i)) &&
         result == -1 ==> exists<i: usize> (0 <= i && i < count &&
            (forall<j: usize> (0 <= j && j < i ==> *p1.add(j) == *p2.add(j))) &&
            *p1.add(i) < *p2.add(i)) &&
         result == 1 ==> exists<i: usize> (0 <= i && i < count &&
            (forall<j: usize> (0 <= j && j < i ==> *p1.add(j) == *p2.add(j))) &&
            *p1.add(i) > *p2.add(i))
]
unsafe fn memcmp(p1: *const u8, p2: *const u8, count: usize) -> i32 {
    let mut result = 0;
    let mut i = 0;
    #[invariant(
        0 <= i && i <= count &&
        mem_block(p1, count) * mem_block(p2, count) *
        (forall<j: usize> (0 <= j && j < i ==> *p1.add(j) == *p2.add(j)))
    )]
    loop {
        if i == count {
            break;
        }
        if *p1.add(i) < *p2.add(i) {
            result = -1;
            break;
        }
        if *p1.add(i) > *p2.add(i) {
            result = 1;
            break;
        }
        i += 1;
    }
    result
}

fn main() {
    println!("stack_tuerk.rs compiles successfully!");
}