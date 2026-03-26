package chat;

import java.io.*;
import java.net.*;
import java.util.*;

/*@
predicate Member(Member m) = 
    m.nick |-> ?nick &*& m.writer |-> ?writer &*& writer != null;
@*/

class Member {
    String nick;
    Writer writer;
    
    public Member(String nick, Writer writer)
    //@ requires writer != null;
    //@ ensures Member(this);
    {
        this.nick = nick;
        this.writer = writer;
        //@ close Member(this);
    }
}