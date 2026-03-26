package chat;

import java.io.*;
import java.net.*;
import java.util.*;

/*@
predicate member(Member m; String nick, Writer writer) =
    m.nick |-> nick &*& m.writer |-> writer;
@*/

class Member {
    String nick;
    Writer writer;
    
    // Predicates cannot appear as line comments with requires/ensures. Use only line comments inside methods.
    // Constructor requires and ensures:
    // We write them as //@ requires ...; //@ ensures ...;
    //
    //@ requires writer != null;
    //@ ensures member(this, nick, writer);
    public Member(String nick, Writer writer)
    {
        this.nick = nick;
        this.writer = writer;
    }
}