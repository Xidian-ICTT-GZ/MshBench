package chat;

import java.io.*;
import java.net.*;
import java.util.*;

/*@
predicate Member_pred(Member m; String nick, Writer writer) =
    m.nick |-> nick &*& m.writer |-> writer;
@*/

class Member {
    String nick;
    Writer writer;
    
    public Member(String nick, Writer writer)
        //@ requires true;
        //@ ensures Member_pred(this, nick, writer);
    {
        this.nick = nick;
        this.writer = writer;
        //@ close Member_pred(this, nick, writer);
    }
}