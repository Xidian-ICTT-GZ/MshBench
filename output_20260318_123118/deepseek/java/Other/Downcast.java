class C {
    int x;

    //@ requires true;
    //@ ensures this.x |-> 0;
    C()
    {
    }

}

class D extends C {
    int y;

    //@ requires true;
    //@ ensures this.x |-> 0 &*& this.y |-> 0;
    D()
    {
    }

    //@ requires this.y |-> ?v;
    //@ ensures this.y |-> v &*& result == v;
    int getY()
    {
        return this.y;
    }
}

class E extends D {
    int z;

    //@ requires true;
    //@ ensures this.x |-> 0 &*& this.y |-> 0 &*& this.z |-> 0;
    E()
    {
    }

    //@ requires this.y |-> ?v;
    //@ ensures this.y |-> v &*& result == v;
    int getY()
    {
        return super.getY();
    }
}

class Program {
    //@ requires c != null;
    //@ ensures true;
    static int getY(C c)
    {
        if (c instanceof D) {
            D d = (D)c;
            return d.getY();
        } else {
            return 0;
        }
    }

    //@ requires true;
    //@ ensures true;
    static void test()
    {
        E e = new E();
        getY(e);
    }
}