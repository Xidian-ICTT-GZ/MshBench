import java.util.ArrayList;
import java.util.List;
import java.util.Arrays;

/*@
predicate GenericClassObject(GenericClass<?> obj) = obj != null;
@*/
public class GenericClass<T>{
	public T field;
	//@ requires true;
	//@ ensures GenericClassObject(this);
	public GenericClass(T f)
	
	
	{
		field = f;
	}
	
	//@ requires GenericClassObject(this);
	//@ ensures GenericClassObject(this) &*& result == arg;
	public T add(T arg)
	
	
	{
		field = arg;
		return field;
	}
	
	//@ requires GenericClassObject(this);
	//@ ensures GenericClassObject(this) &*& result == this.field;
	public T get()
	
	
	{
		return field;
	}
}

/*@
predicate FooObject(Foo<?> obj) = obj != null;
@*/
public class Foo<T> {
	//@ requires true;
	//@ ensures FooObject(this);
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
	//@ ensures true;
	public D get1(D arg1) {return null;}
	//@ requires true;
	//@ ensures true;
	public C get2() {return null;}
}

public abstract class AbstractParentClass<A,B> {
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