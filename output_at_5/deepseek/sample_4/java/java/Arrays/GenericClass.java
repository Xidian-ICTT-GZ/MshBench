import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;

public class GenericClass<T>{
	public T field;
	
	//@ predicate valid() = this.field |-> ?v;
	
	public GenericClass(T f)
	//@ requires true;
	//@ ensures valid();
	{
		field = f;
		//@ close valid();
	}
	
	public T add(T arg)
	//@ requires valid();
	//@ ensures valid();
	{
		//@ open valid();
		field = arg;
		//@ close valid();
		return field;
	}
	
	public T get()
	//@ requires valid();
	//@ ensures valid() &*& result == field;
	{
		//@ open valid();
		T result = field;
		//@ close valid();
		return result;
	}
}

public class Foo<T> {
	//@ predicate valid() = true;
	
	public Foo(T arg)
	//@ requires true;
	//@ ensures valid();
	{
		GenericClass<T> b = new GenericClass<T>(arg);
		//@ close valid();
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
	//@ predicate valid() = true;
	
	public D get1(D arg1) 
	//@ requires valid();
	//@ ensures valid();
	{
		//@ close valid();
		return null;
	}
	
	public C get2() 
	//@ requires valid();
	//@ ensures valid();
	{
		//@ close valid();
		return null;
	}
}

public abstract class AbstractParentClass<A,B> {
	public abstract A get1(A arg1);
}

public class ChildClassInheritance<C,D> extends AbstractParentClass<C,D>{
	//@ predicate valid() = true;
	
	public C get1(C arg1)
	//@ requires valid();
	//@ ensures valid();
	{
		//@ close valid();
		return null;
	}
}

public class HelloWorld 
{
  public static GenericClass<GenericClass<Foo> > genericInstance;
  
  public static void main(String[] args) 
  //@ requires true;
  //@ ensures true;
  {
    String[] sentence = {"Hello", "World"};
    List<String> sentenceList = Arrays.<String>asList(sentence);
    Foo<String> foo = new Foo<String>("test");
    //@ close foo.valid();
    GenericClass<String> simple = new GenericClass<String>("Example");
    GenericClass<GenericClass<String> > nested = new GenericClass<GenericClass<String> >(new GenericClass<String>("foo"));
    nested.add(new GenericClass<String>("hello"));
    GenericClass<String> s = nested.get();   
    
    List<String> l = new ArrayList< >();
    l.add("foo");
    String abba = l.get(0);
  }
}