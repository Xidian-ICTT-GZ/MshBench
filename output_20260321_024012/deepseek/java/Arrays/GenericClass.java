import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;

/*@
predicate GenericClass(GenericClass<T> this, T f) = this.field |-> f;
@*/

public class GenericClass<T>{
	public T field;
	
	//@ requires true;
	//@ ensures GenericClass(this, f);
	public GenericClass(T f)
	
	
	{
		//@ close GenericClass(this, f);
		field = f;
	}
	
	//@ requires GenericClass(this, _);
	//@ ensures GenericClass(this, arg) &*& result == arg;
	public T add(T arg)
	
	
	{
		//@ open GenericClass(this, _);
		field = arg;
		//@ close GenericClass(this, arg);
		return field;
	}
	
	//@ requires GenericClass(this, f);
	//@ ensures GenericClass(this, f) &*& result == f;
	public T get()
	
	
	{
		//@ open GenericClass(this, f);
		//@ close GenericClass(this, f);
		return field;
	}
}

/*@
predicate Foo(Foo<T> this) = true;
@*/

public class Foo<T> {
	//@ requires true;
	//@ ensures Foo(this);
	public Foo(T arg)
	
	
	{
		//@ close Foo(this);
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
    //@ close Foo(foo);
    Foo<String> foo = new Foo<String>("test");
    //@ close GenericClass(simple, "Example");
    GenericClass<String> simple = new GenericClass<String>("Example");
    //@ close GenericClass(tmp, "foo");
    GenericClass<String> tmp = new GenericClass<String>("foo");
    //@ close GenericClass(nested, tmp);
    GenericClass<GenericClass<String> > nested = new GenericClass<GenericClass<String> >(new GenericClass<String>("foo"));
    //@ close GenericClass(tmp2, "hello");
    GenericClass<String> tmp2 = new GenericClass<String>("hello");
    nested.add(new GenericClass<String>("hello"));
    GenericClass<String> s = nested.get();   
    
    List<String> l = new ArrayList< >();
    l.add("foo");
    String abba = l.get(0);
  }
}