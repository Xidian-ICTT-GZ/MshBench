class Program {
  /*@ 
    predicate valid_inputs(short x, short y, short z) = true;
  @*/

  //@ requires valid_inputs(x, y, z);
  //@ ensures (result == x || result == y || result == z) &*& result <= x &*& result <= y &*& result <= z;
  static short min(short x, short y, short z) {
      short m = x < y ? x : y;
      m = m < z ? m : z;
      return m;
  }
}