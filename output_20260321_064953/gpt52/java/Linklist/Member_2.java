package chat;

import java.io.*;
import java.net.*;
import java.util.*;

/*@
predicate Member_state(Member m; String nick, Writer writer) =
    m.nick |-> nick &*& m.writer |-> writer;
@*/

class Member {
    String nick;
    Writer writer;
    
    //@ requires true;
    //@ ensures Member_state(this, nick, writer);
    public Member(String nick, Writer writer)
        
        
    {
        //@ close Member_state(this, ?n0, ?w0);
        //@ open Member_state(this, n0, w0);
        this.nick = nick;
        this.writer = writer;
        //@ close Member_state(this, nick, writer);
        
    }
}