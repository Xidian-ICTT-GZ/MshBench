//@ predicate GenericClass_own<T>(GenericClass<T> g; T value) = g.field |-> value;

public class GenericClass<T>{
	public T field;
	
	//@ requires true;
	//@ ensures GenericClass_own(this, f);
	public GenericClass(T f)
	{
		field = f;
	}
	
	//@ requires GenericClass_own(this, _);
	//@ ensures GenericClass_own(this, arg) &*& result == arg;
	public T add(T arg)
	{
		field = arg;
		return field;
	}
	
	//@ requires GenericClass_own(this, v) &*& v == this.field;
	//@ ensures GenericClass_own(this, v) &*& result == v;
	public T get()
	{
		return field;
	}
}

public class Foo<T> {
	//@ requires true;
	//@ ensures true;
	public Foo(T arg)
	{
		GenericClass<T> b = new GenericClass<T>(arg);
	}
}

public interface Parent<A,B>{
	public A get1(A arg1);
	public B get2();
}

public interface Child<C,D> extends Parent<D,C>{
	public D get1(D arg1);
	public C get2();
}

public class ChildClass<C,D> implements Parent<D,C>{
	//@ requires true;
	//@ ensures result == null;
	public D get1(D arg1) {return null;}
	
	//@ requires true;
	//@ ensures result == null;
	public C get2() {return null;}
}

public abstract class AbstractParentClass<A,B> {
	public abstract A get1(A arg1);
}

public class ChildClassInheritance<C,D> extends AbstractParentClass<C,D>{
	//@ requires true;
	//@ ensures result == null;
	public C get1(C arg1){return null;}
}

public class HelloWorld 
{
  public static GenericClass<GenericClass<Foo> > genericInstance;
  
  //@ requires true;
  //@ ensures true;
  public static void main(String[] args) 
  {
    String[] sentence = {"Hello", "World"};
    List<String> sentenceList = Arrays.<String>asList(sentence);
    Foo<String> foo = new Foo<String>("test");
    GenericClass<String> simple = new GenericClass<String>("Example");
    GenericClass<GenericClass<String> > nested = new GenericClass<GenericClass<String> >(new GenericClass<String>("foo"));
    nested.add(new GenericClass<String>("hello"));
    GenericClass<String> s = nested.get();   
    
    List<String> l = new ArrayList< >();
    l.add("foo");
    String abba = l.get(0);
  }
}