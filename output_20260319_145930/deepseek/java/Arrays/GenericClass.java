import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;

//@ predicate GenericClass<T>(GenericClass<T> g; T v) = g.field |-> v &*& g != null;
//@ predicate Foo<T>(Foo<T> f) = f != null;

public class GenericClass<T>{
	public T field;
	
	//@ requires true;
	//@ ensures GenericClass<T>(this, f);
	public GenericClass(T f)
	
	
	{
		field = f;
		//@ close GenericClass<T>(this, f);
	}
	
	//@ requires GenericClass<T>(this, _);
	//@ ensures GenericClass<T>(this, arg) &*& result == arg;
	public T add(T arg)
	
	
	{
		//@ open GenericClass<T>(this, _);
		field = arg;
		//@ close GenericClass<T>(this, arg);
		return field;
	}
	
	//@ requires GenericClass<T>(this, v);
	//@ ensures GenericClass<T>(this, v) &*& result == v;
	public T get()
	
	
	{
		//@ open GenericClass<T>(this, v);
		T result = field;
		//@ close GenericClass<T>(this, v);
		return result;
	}
}

public class Foo<T> {
	//@ requires true;
	//@ ensures Foo<T>(this);
	public Foo(T arg)
	
	
	{
		GenericClass<T> b = new GenericClass<T>(arg);
		//@ close Foo<T>(this);
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
    //@ close Foo<String>(foo);
    Foo<String> foo = new Foo<String>("test");
    //@ close GenericClass<String>(simple, "Example");
    GenericClass<String> simple = new GenericClass<String>("Example");
    //@ close GenericClass<String>(tmp, "foo");
    GenericClass<String> tmp = new GenericClass<String>("foo");
    //@ close GenericClass<GenericClass<String> >(nested, tmp);
    GenericClass<GenericClass<String> > nested = new GenericClass<GenericClass<String> >(tmp);
    //@ close GenericClass<String>(tmp2, "hello");
    GenericClass<String> tmp2 = new GenericClass<String>("hello");
    nested.add(tmp2);
    GenericClass<String> s = nested.get();   
    
    List<String> l = new ArrayList< >();
    l.add("foo");
    String abba = l.get(0);
  }
}