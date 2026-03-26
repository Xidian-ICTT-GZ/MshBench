```java
package Addressbook;

import javacard.framework.*;

public final class Addressbook extends Applet {

    
    private static final byte Store_CLA = (byte) 0xB0;

    
    private static final byte ADD = (byte) 0x10;
    private static final byte DELETE = (byte) 0x20;
    private static final byte SEARCH = (byte) 0x30;
    private static final byte ADDGROUP = (byte) 0x40;
    private static final byte DELETEGROUP = (byte) 0x50;
    private static final byte ADDCONTACTTOGROUP = (byte) 0x41;
    private static final byte REMOVECONTACTFROMGROUP = (byte) 0x42;
    private static final byte SEARCHINGROUP = (byte) 0x43;
    private static final byte FILTERCONTACTS = (byte) 0x61;

    
    private static final byte SW_ADDRESSBOOK_FULL = (byte) 0x5300;
    private static final byte SW_PERSON_NOT_FOUND = (byte) 0x2100;
    private static final byte SW_GROUP_NOT_FOUND = (byte) 0x6100;
    private static final byte SW_GROUPBOOK_FULL = (byte) 0x6200;
    private static final byte SW_GROUP_FULL = (byte) 0x6300;
    private static final byte SW_NO_PERSON_FOUND = (byte) 0x4000;

    
    private static final short NR_LENGTH = 5;
    private static final short NAME_LENGTH = 15;
    private static final short RECORD_LENGTH = 20;
    private static final short GROUPNAME_LENGTH = 10;
    private static final short GROUPNUMBERS_LENGTH = 10;

    
    private static byte[] zeros;
    private static byte[] phoneNbs;
    private static short[] emptyPhoneNbs;
    private static byte[] groupnames;
    private static byte[] groupnbs;
    private static short[] emptyGroups;
    private static byte[] filteredNames;

    /*@
    predicate valid() =
        zeros |-> ?z &*& z != null &*& z.length == 20 &*& array_slice(z, 0, z.length, _) &*&
        phoneNbs |-> ?p &*& p != null &*& p.length == 400 &*& array_slice(p, 0, p.length, _) &*&
        emptyPhoneNbs |-> ?ep &*& ep != null &*& ep.length == 20 &*& array_slice(ep, 0, ep.length, _) &*&
        groupnames |-> ?gn &*& gn != null &*& gn.length == 100 &*& array_slice(gn, 0, gn.length, _) &*&
        groupnbs |-> ?gnb &*& gnb != null &*& gnb.length == 100 &*& array_slice(gnb, 0, gnb.length, _) &*&
        emptyGroups |-> ?eg &*& eg != null &*& eg.length == 10 &*& array_slice(eg, 0, eg.length, _) &*&
        filteredNames |-> ?fn &*& fn != null &*& fn.length == 400 &*& array_slice(fn, 0, fn.length, _);
    @*/

    public static void install(byte[] bArray, short bOffset, byte bLength)
    //@ requires system_inv() &*& array_slice(bArray, 0, bArray.length, _);
    //@ ensures system_inv();
    {
        Addressbook addressbook = new Addressbook();
        addressbook.register();
    }

    protected Addressbook()
    //@ requires system_inv();
    //@ ensures system_inv() &*& valid();
    {
        
        phoneNbs = new byte[400];
        emptyPhoneNbs = new short[20];
        zeros = new byte[20];
        groupnames = new byte[100];
        groupnbs = new byte[100];
        emptyGroups = new short[10];
        filteredNames = new byte[400];

        
        for(short i =0; i< 100; i++)
        //@ invariant 0 <= i &*& i <= 100 &*& groupnbs |-> ?gnb &*& gnb != null &*& gnb.length == 100 &*& array_slice(gnb, 0, gnb.length, _);
        {
        	groupnbs[i] = (byte)0;
        }
        //@ close valid();
    }

    public void process(APDU apdu)
    //@ requires system_inv() &*& valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures system_inv() &*& valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();

        if(selectingApplet())
            return;

        if(abuffer[ISO7816.OFFSET_CLA] != Store_CLA)
          ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);

        switch(abuffer[ISO7816.OFFSET_INS]){
            case ADD: add(apdu);return;
            case DELETE: delete(apdu);return;
            case SEARCH: search(apdu);return;
            case ADDGROUP: addGroup(apdu);return;
            case DELETEGROUP: deleteGroup(apdu);return;
            case ADDCONTACTTOGROUP: addContactToGroup(apdu);return;
            case REMOVECONTACTFROMGROUP: removeContactFromGroup(apdu);return;
            case SEARCHINGROUP: searchInGroup(apdu);return;
            case FILTERCONTACTS: filterContacts(apdu);return;
            default: ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
        }
    }

    private void add(APDU apdu)
    //@ requires system_inv() &*& valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures system_inv() &*& valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != RECORD_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@ open valid();
        short length = (short) emptyPhoneNbs.length;

        boolean added = false;

        for(short i=0;i<length;i++)
        //@ invariant 0 <= i &*& i <= length &*& emptyPhoneNbs |-> ?ep &*& ep != null &*& ep.length == 20 &*& array_slice(ep, 0, ep.length, _) &*& phoneNbs |-> ?p &*& p != null &*& p.length == 400 &*& array_slice(p, 0, p.length, _) &*& zeros |-> ?z &*& z != null &*& z.length == 20 &*& array_slice(z, 0, z.length, _) &*& groupnames |-> ?gn &*& gn != null &*& gn.length == 100 &*& array_slice(gn, 0, gn.length, _) &*& groupnbs |-> ?gnb &*& gnb != null &*& gnb.length == 100 &*& array_slice(gnb, 0, gnb.length, _) &*& emptyGroups |-> ?eg &*& eg != null &*& eg.length == 10 &*& array_slice(eg, 0, eg.length, _) &*& filteredNames |-> ?fn &*& fn != null &*& fn.length == 400 &*& array_slice(fn, 0, fn.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
        {
            short item = emptyPhoneNbs[i];

            if(item == 0 && added==false){
                JCSystem.beginTransaction();
                added = true;
                emptyPhoneNbs[i] = 1;
                Util.arrayCopy(abuffer,(short)ISO7816.OFFSET_CDATA,phoneNbs,(short)(i * RECORD_LENGTH),(short) RECORD_LENGTH);
                JCSystem.commitTransaction();
            }
        }
        //@ close valid();

        if(!added)
            ISOException.throwIt(SW_ADDRESSBOOK_FULL);
    }

    private void delete(APDU apdu)
    //@ requires system_inv() &*& valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures system_inv() &*& valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@ open valid();
        short length = (short) emptyPhoneNbs.length;

        for(short i=0;i<length;i++)
        //@ invariant 0 <= i &*& i <= length &*& emptyPhoneNbs |-> ?ep &*& ep != null &*& ep.length == 20 &*& array_slice(ep, 0, ep.length, _) &*& phoneNbs |-> ?p &*& p != null &*& p.length == 400 &*& array_slice(p, 0, p.length, _) &*& zeros |-> ?z &*& z != null &*& z.length == 20 &*& array_slice(z, 0, z.length, _) &*& groupnames |-> ?gn &*& gn != null &*& gn.length == 100 &*& array_slice(gn, 0, gn.length, _) &*& groupnbs |-> ?gnb &*& gnb != null &*& gnb.length == 100 &*& array_slice(gnb, 0, gnb.length, _) &*& emptyGroups |-> ?eg &*& eg != null &*& eg.length == 10 &*& array_slice(eg, 0, eg.length, _) &*& filteredNames |-> ?fn &*& fn != null &*& fn.length == 400 &*& array_slice(fn, 0, fn.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
        {
            short item = emptyPhoneNbs[i];

            if(item == 1){
                short equal = (short)Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);

                if(equal == 0){
                    JCSystem.beginTransaction();
                    emptyPhoneNbs[i] = 0;
                    Util.arrayCopy(zeros,(short)0,phoneNbs,(short)(i * RECORD_LENGTH),(short) RECORD_LENGTH);
                    JCSystem.commitTransaction();
                }
            }
        }
        //@ close valid();
    }

    private void search(APDU apdu)
    //@ requires system_inv() &*& valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures system_inv() &*& valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != NAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@ open valid();
        short length = (short) emptyPhoneNbs.length;
        boolean found = false;
        
        for(short i=0;i<length;i++)
        //@ invariant 0 <= i &*& i <= length &*& emptyPhoneNbs |-> ?ep &*& ep != null &*& ep.length == 20 &*& array_slice(ep, 0, ep.length, _) &*& phoneNbs |-> ?p &*& p != null &*& p.length == 400 &*& array_slice(p, 0, p.length, _) &*& zeros |-> ?z &*& z != null &*& z.length == 20 &*& array_slice(z, 0, z.length, _) &*& groupnames |-> ?gn &*& gn != null &*& gn.length == 100 &*& array_slice(gn, 0, gn.length, _) &*& groupnbs |-> ?gnb &*& gnb != null &*& gnb.length == 100 &*& array_slice(gnb, 0, gnb.length, _) &*& emptyGroups |-> ?eg &*& eg != null &*& eg.length == 10 &*& array_slice(eg, 0, eg.length, _) &*& filteredNames |-> ?fn &*& fn != null &*& fn.length == 400 &*& array_slice(fn, 0, fn.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
        {
            short item = emptyPhoneNbs[i];
            
            if(item == 1 && found == false){
                if(Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH) == 0){
                    found = true;
                    apdu.setOutgoing();
                    apdu.setOutgoingLength(NR_LENGTH);
                    apdu.sendBytesLong(phoneNbs, (short)((i * RECORD_LENGTH)+NAME_LENGTH), NR_LENGTH);
                }
            }
        }
        //@ close valid();
        
        if(found == false){
            ISOException.throwIt(SW_PERSON_NOT_FOUND);
        }
    }

    private void addGroup (APDU apdu)
    //@ requires system_inv() &*& valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures system_inv() &*& valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != GROUPNAME_LENGTH)
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@ open valid();
        short length = (short) emptyGroups.length;

        boolean added = false;
        
        for(short i=0;i<length;i++)
        //@ invariant 0 <= i &*& i <= length &*& emptyPhoneNbs |-> ?ep &*& ep != null &*& ep.length == 20 &*& array_slice(ep, 0, ep.length, _) &*& phoneNbs |-> ?p &*& p != null &*& p.length == 400 &*& array_slice(p, 0, p.length, _) &*& zeros |-> ?z &*& z != null &*& z.length == 20 &*& array_slice(z, 0, z.length, _) &*& groupnames |-> ?gn &*& gn != null &*& gn.length == 100 &*& array_slice(gn, 0, gn.length, _) &*& groupnbs |-> ?gnb &*& gnb != null &*& gnb.length == 100 &*& array_slice(gnb, 0, gnb.length, _) &*& emptyGroups |-> ?eg &*& eg != null &*& eg.length == 10 &*& array_slice(eg, 0, eg.length, _) &*& filteredNames |-> ?fn &*& fn != null &*& fn.length == 400 &*& array_slice(fn, 0, fn.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
        {
            short item = emptyGroups[i];
            
            if(item == 0 && added==false){
                JCSystem.beginTransaction();
                added = true;
                emptyGroups[i] = 1;
                Util.arrayCopy(abuffer,(short)ISO7816.OFFSET_CDATA,groupnames,(short)(i * GROUPNAME_LENGTH),(short) GROUPNAME_LENGTH);
                JCSystem.commitTransaction();
            }
        }
        //@ close valid();
       
        if(added == false){
            ISOException.throwIt(SW_GROUPBOOK_FULL);
        }
    }

    private void addContactToGroup (APDU apdu)
    //@ requires system_inv() &*& valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures system_inv() &*& valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != (NAME_LENGTH + GROUPNAME_LENGTH))
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@ open valid();
        short length = (short) emptyPhoneNbs.length;

        boolean found = false;
        byte contactnb = 0;
        
        for(short i=0;i<length;i++)
        //@ invariant 0 <= i &*& i <= length &*& emptyPhoneNbs |-> ?ep &*& ep != null &*& ep.length == 20 &*& array_slice(ep, 0, ep.length, _) &*& phoneNbs |-> ?p &*& p != null &*& p.length == 400 &*& array_slice(p, 0, p.length, _) &*& zeros |-> ?z &*& z != null &*& z.length == 20 &*& array_slice(z, 0, z.length, _) &*& groupnames |-> ?gn &*& gn != null &*& gn.length == 100 &*& array_slice(gn, 0, gn.length, _) &*& groupnbs |-> ?gnb &*& gnb != null &*& gnb.length == 100 &*& array_slice(gnb, 0, gnb.length, _) &*& emptyGroups |-> ?eg &*& eg != null &*& eg.length == 10 &*& array_slice(eg, 0, eg.length, _) &*& filteredNames |-> ?fn &*& fn != null &*& fn.length == 400 &*& array_slice(fn, 0, fn.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
        {
            short equal = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);
            
            if(found==false && equal == 0 ){
                found = true;
                contactnb = (byte)(short)(i+1);
            }
        }

        if(found == false){
            //@ close valid();
            ISOException.throwIt(SW_PERSON_NOT_FOUND);
        }

        short g_length = (short) emptyGroups.length;

        boolean g_found = false;
        boolean added = false;

        for(short i=0;i<g_length;i++)
        //@ invariant 0 <= i &*& i <= g_length &*& emptyPhoneNbs |-> ?ep2 &*& ep2 != null &*& ep2.length == 20 &*& array_slice(ep2, 0, ep2.length, _) &*& phoneNbs |-> ?p2 &*& p2 != null &*& p2.length == 400 &*& array_slice(p2, 0, p2.length, _) &*& zeros |-> ?z2 &*& z2 != null &*& z2.length == 20 &*& array_slice(z2, 0, z2.length, _) &*& groupnames |-> ?gn2 &*& gn2 != null &*& gn2.length == 100 &*& array_slice(gn2, 0, gn2.length, _) &*& groupnbs |-> ?gnb2 &*& gnb2 != null &*& gnb2.length == 100 &*& array_slice(gnb2, 0, gnb2.length, _) &*& emptyGroups |-> ?eg2 &*& eg2 != null &*& eg2.length == 10 &*& array_slice(eg2, 0, eg2.length, _) &*& filteredNames |-> ?fn2 &*& fn2 != null &*& fn2.length == 400 &*& array_slice(fn2, 0, fn2.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
        {
            short equal = Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + NAME_LENGTH), groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
            
            if(g_found==false && equal == 0 ){
                g_found = true;

                short begin = (short)(i * GROUPNUMBERS_LENGTH);
                short end = (short)(begin + GROUPNUMBERS_LENGTH);

                for(short a=begin;a<end;a++)
                //@ invariant begin <= a &*& a <= end &*& emptyPhoneNbs |-> ?ep3 &*& ep3 != null &*& ep3.length == 20 &*& array_slice(ep3, 0, ep3.length, _) &*& phoneNbs |-> ?p3 &*& p3 != null &*& p3.length == 400 &*& array_slice(p3, 0, p3.length, _) &*& zeros |-> ?z3 &*& z3 != null &*& z3.length == 20 &*& array_slice(z3, 0, z3.length, _) &*& groupnames |-> ?gn3 &*& gn3 != null &*& gn3.length == 100 &*& array_slice(gn3, 0, gn3.length, _) &*& groupnbs |-> ?gnb3 &*& gnb3 != null &*& gnb3.length == 100 &*& array_slice(gnb3, 0, gnb3.length, _) &*& emptyGroups |-> ?eg3 &*& eg3 != null &*& eg3.length == 10 &*& array_slice(eg3, 0, eg3.length, _) &*& filteredNames |-> ?fn3 &*& fn3 != null &*& fn3.length == 400 &*& array_slice(fn3, 0, fn3.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
                {
                    byte openplace = groupnbs[a];
                    
                    if(added == false && openplace == 0){
                        JCSystem.beginTransaction();
                        added = true;
                        groupnbs[a] = contactnb;
                        JCSystem.commitTransaction();
                    }
                }
            }
        }
        //@ close valid();

        if(g_found == false)
            ISOException.throwIt(SW_GROUP_NOT_FOUND);
        if(added == false)
            ISOException.throwIt(SW_GROUP_FULL);
    }

    private void removeContactFromGroup (APDU apdu)
    //@ requires system_inv() &*& valid() &*& apdu != null &*& APDU(apdu, ?buffer) &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures system_inv() &*& valid() &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
    {
        byte[] abuffer = apdu.getBuffer();

        if((short)abuffer[ISO7816.OFFSET_LC] != (NAME_LENGTH + GROUPNAME_LENGTH))
            ISOException.throwIt(ISO7816.SW_DATA_INVALID);

        //@ open valid();
        short length = (short) emptyPhoneNbs.length;

        boolean found = false;
        byte contactnb = 0;
        
        for(short i=0;i<length;i++)
        //@ invariant 0 <= i &*& i <= length &*& emptyPhoneNbs |-> ?ep &*& ep != null &*& ep.length == 20 &*& array_slice(ep, 0, ep.length, _) &*& phoneNbs |-> ?p &*& p != null &*& p.length == 400 &*& array_slice(p, 0, p.length, _) &*& zeros |-> ?z &*& z != null &*& z.length == 20 &*& array_slice(z, 0, z.length, _) &*& groupnames |-> ?gn &*& gn != null &*& gn.length == 100 &*& array_slice(gn, 0, gn.length, _) &*& groupnbs |-> ?gnb &*& gnb != null &*& gnb.length == 100 &*& array_slice(gnb, 0, gnb.length, _) &*& emptyGroups |-> ?eg &*& eg != null &*& eg.length == 10 &*& array_slice(eg, 0, eg.length, _) &*& filteredNames |-> ?fn &*& fn != null &*& fn.length == 400 &*& array_slice(fn, 0, fn.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
        {
            short equal = Util.arrayCompare(abuffer, (short)ISO7816.OFFSET_CDATA, phoneNbs, (short)(i * RECORD_LENGTH), NAME_LENGTH);
            
            if(found==false && equal == 0 ){
                found = true;
                contactnb = (byte)(short)(i+1);
            }
        }

        if(found == false){
            //@ close valid();
            ISOException.throwIt(SW_PERSON_NOT_FOUND);
        }

        short g_length = (short) emptyGroups.length;

        boolean g_found = false;

        for(short i=0;i<g_length;i++)
        //@ invariant 0 <= i &*& i <= g_length &*& emptyPhoneNbs |-> ?ep2 &*& ep2 != null &*& ep2.length == 20 &*& array_slice(ep2, 0, ep2.length, _) &*& phoneNbs |-> ?p2 &*& p2 != null &*& p2.length == 400 &*& array_slice(p2, 0, p2.length, _) &*& zeros |-> ?z2 &*& z2 != null &*& z2.length == 20 &*& array_slice(z2, 0, z2.length, _) &*& groupnames |-> ?gn2 &*& gn2 != null &*& gn2.length == 100 &*& array_slice(gn2, 0, gn2.length, _) &*& groupnbs |-> ?gnb2 &*& gnb2 != null &*& gnb2.length == 100 &*& array_slice(gnb2, 0, gnb2.length, _) &*& emptyGroups |-> ?eg2 &*& eg2 != null &*& eg2.length == 10 &*& array_slice(eg2, 0, eg2.length, _) &*& filteredNames |-> ?fn2 &*& fn2 != null &*& fn2.length == 400 &*& array_slice(fn2, 0, fn2.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
        {
            short equal = Util.arrayCompare(abuffer, (short)(ISO7816.OFFSET_CDATA + NAME_LENGTH), groupnames, (short)(i * GROUPNAME_LENGTH), GROUPNAME_LENGTH);
            
            if(g_found==false && equal == 0 ){
                g_found = true;

                short begin = (short)(i * GROUPNUMBERS_LENGTH);
                short end = (short)(begin + GROUPNUMBERS_LENGTH);

                for(short a=begin;a<end;a++)
                //@ invariant begin <= a &*& a <= end &*& emptyPhoneNbs |-> ?ep3 &*& ep3 != null &*& ep3.length == 20 &*& array_slice(ep3, 0, ep3.length, _) &*& phoneNbs |-> ?p3 &*& p3 != null &*& p3.length == 400 &*& array_slice(p3, 0, p3.length, _) &*& zeros |-> ?z3 &*& z3 != null &*& z3.length == 20 &*& array_slice(z3, 0, z3.length, _) &*& groupnames |-> ?gn3 &*& gn3 != null &*& gn3.length == 100 &*& array_slice(gn3, 0, gn3.length, _) &*& groupnbs |-> ?gnb3 &*& gnb3 != null &*& gnb3.length == 100 &*& array_slice(gnb3, 0, gnb3.length, _) &*& emptyGroups |-> ?eg3 &*& eg3 != null &*& eg3.length == 10 &*& array_slice(eg3, 0, eg3.length, _) &*& filteredNames |-> ?fn3 &*& fn3 != null &*& fn3.length == 400 &*& array_slice(fn3, 0, fn3.length, _) &*& APDU(apdu, buffer) &*& array_slice(buffer, 0, buffer.length, _);
                {
                    byte contactequ