import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;

public class GenericClass<T>{
	public T field;
	//@ requires true;
	//@ ensures this.field |-> f;
	public GenericClass(T f)
	
	
	{
		field = f;
	}
	
	//@ requires this.field |-> _;
	//@ ensures this.field |-> arg &*& result == arg;
	public T add(T arg)
	
	
	{
		field = arg;
		return field;
	}
	
	//@ requires this.field |-> ?v;
	//@ ensures this.field |-> v &*& result == v;
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
	//@ requires true;
	//@ ensures true;
	public A get1(A arg1);
	//@ requires true;
	//@ ensures true;
	public B get2();
}

public interface Child<C,D> extends Parent<D,C>{
	//@ requires true;
	//@ ensures true;
	public D get1(D arg1);
	//@ requires true;
	//@ ensures true;
	public C get2();
}

public class ChildClass<C,D> implements Parent<D,C>{
	//@ requires true;
	//@ ensures true;
	public D get1(D arg1) {return null;}
	//@ requires true;
	//@ ensures true;
	public C get2() {return null;}
}

public abstract class AbstractParentClass<A,B> {
	//@ requires true;
	//@ ensures true;
	public abstract A get1(A arg1);
}
public class ChildClassInheritance<C,D> extends AbstractParentClass<C,D>{
	//@ requires true;
	//@ ensures true;
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