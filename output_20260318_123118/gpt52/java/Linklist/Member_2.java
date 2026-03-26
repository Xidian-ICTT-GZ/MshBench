package chat;

import java.io.*;
import java.net.*;
import java.util.*;

class Member {
    String nick;
    Writer writer;

    /*@ predicate member(String n, Writer w) =
            this.nick |-> n
        &*& this.writer |-> w;
    @*/
    
    public Member(String nick, Writer writer)
    //@ requires true;
    //@ ensures member(nick, writer);
    {
        this.nick = nick;
        this.writer = writer;
        
    }
}