package chat;

import java.io.*;
import java.net.*;
import java.util.*;

/*@
predicate MemberInv(Member this) = 
    this.nick != null &*& this.writer != null;
@*/

class Member {
    String nick;
    Writer writer;
    
    //@ requires nick != null &*& writer != null;
    //@ ensures MemberInv(this);
    public Member(String nick, Writer writer)
        
        
    {
        this.nick = nick;
        this.writer = writer;
        
    }
}