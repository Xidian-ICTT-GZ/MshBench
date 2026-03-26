package be.fedict.eidapplet;

import javacard.framework.*;
import javacard.security.*;
import javacardx.crypto.Cipher;
import org.globalplatform.GPSystem;

public abstract class File {

    private short fileID;
    protected boolean active;

    /*@ predicate file(File this, short fid, boolean active) = 
          this.fileID |-> fid &*& this.active |-> active; @*/

    //@ requires this.fileID |-> _;
    //@ ensures  result == this.fileID;
    public short getFileID()
    {
        return fileID;
    }

    //@ requires this.active |-> _;
    //@ ensures this.active |-> b;
    public void setActive(boolean b)
    {
        active = b;
    }

    //@ requires this.active |-> _;
    //@ ensures  result == this.active;
    public boolean isActive()
    {
        return active;
    }

    /*@ requires this.fileID |-> fid &*& this.active |-> active;
        ensures this.fileID |-> fid &*& this.active |-> active;
      @*/
    public File(short fid)
    {
        fileID = fid;
        active = true;
    }
}

public class DedicatedFile extends File {
    private DedicatedFile parentFile;
    private static final byte MAX_SIBLINGS = 10;
    private File[] siblings;
    private byte number;

    /*@ predicate dedicatedFile(DedicatedFile this, short fid, boolean active, 
                              DedicatedFile parent, 
                              list<File> sibs) = 
          file(this, fid, active) &*&
          this.parentFile |-> parent &*&
          this.siblings |-> siblings &*&
          this.number |-> number &*&
          array_slice(siblings, 0, number, sibs) &*&
          charslice(siblings, number, MAX_SIBLINGS, _) &*&
          number <= MAX_SIBLINGS;
     @*/

    //@ requires this.fileID |-> _;
    //@ requires this.parentFile |-> _;
    //@ requires this.siblings |-> _;
    //@ requires this.number |-> _;
    //@ ensures  result == this.parentFile;
    public DedicatedFile getParent()
    {
        return parentFile;
    }

    /*@ requires this.number |-> n &*& this.siblings |-> sibs &*& n < MAX_SIBLINGS &*& 
                  s != null;
      @ ensures this.number |-> n+1 &*& this.siblings |-> _; 
      @*/
    protected void addSibling(File s)
    {
        if (number < MAX_SIBLINGS) {
            siblings[number++] = s;
        }
    }

    //@ requires this.number |-> n &*& this.siblings |-> sibs &*& (short)0 <= fid;
    //@ ensures result == null || sibs != null;
    public File getSibling(short fid)
    {
        for (byte i = 0; i < number; i++)
        {
            File fl = siblings[i];
            if (fl != null && fl.getFileID() == fid)
            {
                return fl;
            }
        }
        return null;
    }

    //@ requires this.fileID |-> _;
    //@ ensures result == this.fileID;
    public short getFileID()
    {
        return fileID;
    }

    //@ requires this.active |-> _;
    //@ ensures this.active |-> b;
    public void setActive(boolean b)
    {
        active = b;
    }

    //@ requires this.active |-> _;
    //@ ensures  result == this.active;
    public boolean isActive()
    {
        return active;
    }

    //@ requires this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile &*& this.siblings |-> siblings &*& this.number |-> number;
    //@ ensures this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile &*& this.siblings |-> siblings &*& this.number |-> number;
    protected DedicatedFile(short fid)
    {
        super(fid);
        parentFile = null;
        siblings = new File[MAX_SIBLINGS];
        number = 0;
    }

    //@ requires this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile &*& this.siblings |-> siblings &*& this.number |-> number;
    //@ ensures this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile &*& this.siblings |-> siblings &*& this.number |-> number;
    protected DedicatedFile(short fid, DedicatedFile parent)
    {
        super(fid);
        parentFile = parent;
        siblings = new File[MAX_SIBLINGS];
        number = 0;
        parent.addSibling(this);
    }
}

public final class MasterFile extends DedicatedFile {
    private static final short MF_FID = 0x3F00;

    /*@ predicate masterFile(MasterFile this) = dedicatedFile(this, MF_FID, _, _, _); @*/

    //@ requires this.fileID |-> _;
    //@ ensures result == this.parentFile;
    public DedicatedFile getParent()
    {
        return parentFile;
    }

    //@ requires this.fileID |-> _;
    //@ ensures result == super.getSibling(fid);
    public File getSibling(short fid)
    {
        return super.getSibling(fid);
    }

    //@ requires this.fileID |-> _;
    //@ ensures result == this.fileID;
    public short getFileID()
    {
        return fileID;
    }

    //@ requires this.active |-> _;
    //@ ensures this.active |-> b;
    public void setActive(boolean b)
    {
        active = b;
    }

    //@ requires this.active |-> _;
    //@ ensures result == this.active;
    public boolean isActive()
    {
        return active;
    }

    //@ requires this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile &*& this.siblings |-> siblings &*& this.number |-> number;
    //@ ensures this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile &*& this.siblings |-> siblings &*& this.number |-> number;
    protected void addSibling(File s)
    {
        super.addSibling(s);
    }

    //@ requires true;
    //@ ensures true;
    public MasterFile()
    {
        super(MF_FID);
    }
}

public final class ElementaryFile extends File {

    private DedicatedFile parentFile;
    private byte[] data;
    short size;

    /*@ predicate elementaryFile(ElementaryFile this, short fid, boolean active, DedicatedFile parent, byte[] data, short size) =
          file(this, fid, active) &*&
          this.parentFile |-> parent &*&
          this.data |-> data &*&
          this.size |-> size &*&
          array_slice(data, 0, size, _);
      @*/

    //@ requires this.fileID |-> _;
    //@ ensures result == this.parentFile;
    public DedicatedFile getParent()
    {
        return parentFile;
    }

    //@ requires this.data |-> data &*& this.active |-> active;
    //@ ensures this.data |-> data &*& this.active |-> active &*& result == data;
    public byte[] getData()
    {
        if (active == true) {
            return data;
        } else {
            ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
            return null; 
        }
    }

    //@ requires this.size |-> size &*& this.active |-> active;
    //@ ensures this.size |-> size &*& this.active |-> active &*& result == size;
    public short getCurrentSize()
    {
        if (active == true) {
            return size;
        } else {
            ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
        }
        return 0;
    }

    //@ requires this.data |-> data;
    //@ ensures this.data |-> data &*& result == data.length;
    public short getMaxSize()
    {
        return (short) this.data.length;
    }

    //@ requires this.data |-> data &*& this.size |-> size;
    //@ ensures this.data |-> data &*& this.size |-> size;
    public void eraseData(short offset)
    {
        Util.arrayFillNonAtomic(data, offset, (short)(size - offset), (byte) 0);
    }

    //@ requires this.data |-> data &*& this.size |-> size;
    //@ ensures this.data |-> data &*& this.size |-> newSize;
    public void updateData(short dataOffset, byte[] newData, short newDataOffset, short length)
    {
        short newSize = (short) (dataOffset + length);
        size = newSize;
        Util.arrayCopy(newData, newDataOffset, data, dataOffset, length);
    }

    //@ requires this.fileID |-> _;
    //@ ensures result == this.fileID;
    public short getFileID()
    {
        return fileID;
    }

    //@ requires this.active |-> _;
    //@ ensures this.active |-> b;
    public void setActive(boolean b)
    {
        super.setActive(b);
    }

    //@ requires this.active |-> _;
    //@ ensures result == super.isActive();
    public boolean isActive()
    {
        return super.isActive();
    }

    //@ requires this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile &*& this.data |-> data &*& this.size |-> size;
    //@ ensures this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile &*& this.data |-> data &*& this.size |-> size;
    public ElementaryFile(short fid, DedicatedFile parent, byte[] d)
    {
        super(fid);
        parentFile = parent;
        parent.addSibling(this);
        data = d;
        size = (short) d.length;
    }

    //@ requires this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile;
    //@ ensures this.fileID |-> fid &*& this.active |-> active &*& this.parentFile |-> parentFile;
    public ElementaryFile(short fid, DedicatedFile parent, short maxSize)
    {
        super(fid);
        parentFile = parent;
        parent.addSibling(this);
        data = new byte[maxSize];
        size = (short) 0;
    }
}

/*@

predicate fileAccessAllowedSpec(File f, byte mode) =
    f != null &*&
    (f instanceof ElementaryFile ==> true) &*&
    (mode == 1 ==> true) &*&
    (f == EidCard.preferencesFile && EidCard.cardholderPin.isValidated() ==> true) &*&
    (GPSystem.getCardContentState() == GPSystem.APPLICATION_SELECTABLE ==> true)
;

@*/

final class EidCard extends Applet {
    

    //@ predicate state(EidCard this) =
    //@    charslice(this.randomBuffer, 0, 256, _) &*&
    //@    charslice(this.responseBuffer, 0, 128, _) &*&
    //@    file(this.selectedFile, _, _) &*&
    //@    OwnerPIN_pred(this.cardholderPin) &*& OwnersPIN_pred(this.resetPin) &*& OwnersPIN_pred(this.unblockPin) &*& OwnersPIN_pred(this.activationPin);

    //@ requires true;
    //@ ensures true;
    public static void install(byte[] bArray, short bOffset, byte bLength)
    {
        new EidCard();
    }

    //@ requires state(this);
    //@ ensures state(this);
    private void initializeFileSystem()
    {
        masterFile = new MasterFile();

        dirFile = new ElementaryFile(EF_DIR, masterFile, (short)0x25);
        belpicDirectory = new DedicatedFile(DF_BELPIC, masterFile);
        tokenInfo = new ElementaryFile(TOKENINFO, belpicDirectory, (short)0x30);
        objectDirectoryFile = new ElementaryFile(ODF, belpicDirectory, (short)40);
        authenticationObjectDirectoryFile = new ElementaryFile(AODF, belpicDirectory, (short)0x40);
        privateKeyDirectoryFile = new ElementaryFile(PRKDF, belpicDirectory, (short)0xB0);
        certificateDirectoryFile = new ElementaryFile(CDF, belpicDirectory, (short)0xB0);
        idDirectory = new DedicatedFile(DF_ID, masterFile);

        identityFile = new ElementaryFile(IDENTITY, idDirectory, (short)0xD0);
        identityFileSignature = new ElementaryFile(SGN_IDENTITY, idDirectory, (short)0x80);
        addressFile = new ElementaryFile(ADDRESS, idDirectory, (short)117);
        addressFileSignature = new ElementaryFile(SGN_ADDRESS, idDirectory, (short)128);
        caRoleIDFile = new ElementaryFile(CA_ROLE_ID, idDirectory, (short)0x20);
        preferencesFile = new ElementaryFile(PREFERENCES, idDirectory, (short)100);
        selectedFile = masterFile;
    }

    //@ requires selectedFile != null &*& buffer != null &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures true;
    private void eraseBinary(APDU apdu, byte[] buffer)
    {
        if(!fileAccessAllowed(ERASE_BINARY))
        {
            ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
        }
        short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
        JCSystem.beginTransaction();

        if(selectedFile == masterFile)
            ISOException.throwIt(ISO7816.SW_FILE_INVALID);
        short size = ((ElementaryFile)selectedFile).getCurrentSize();
        if(offset > size || offset < 0)
            ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
        ((ElementaryFile)selectedFile).eraseData(offset);
        JCSystem.commitTransaction();
    }

    //@ requires selectedFile != null &*& buffer != null &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures true;
    private void updateBinary(APDU apdu, byte[] buffer)
    {
        if(!fileAccessAllowed(UPDATE_BINARY))
            ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
        short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
        JCSystem.beginTransaction();

        if(selectedFile == masterFile)
            ISOException.throwIt(ISO7816.SW_FILE_INVALID);
        short maxSize = ((ElementaryFile)selectedFile).getMaxSize();
        if(offset > maxSize || offset < 0)
            ISOException.throwIt(ISO7816.SW_WRONG_P1P2);

        short byteRead = apdu.setIncomingAndReceive();
        short lc = (short)(buffer[ISO7816.OFFSET_LC] & 0x00FF);
        if(lc == 0 || byteRead == 0)
            ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
        if(ISO7816.OFFSET_CDATA + lc > buffer.length || offset + lc > maxSize)
            ISOException.throwIt(ISO7816.SW_WRONG_P1P2);

        ((ElementaryFile)selectedFile).updateData(offset, buffer, ISO7816.OFFSET_CDATA, lc);
        JCSystem.commitTransaction();
    }

    //@ requires mode >= 0;
    //@ ensures result == true || result == false;
    private boolean fileAccessAllowed(byte mode)
    {
        if(!(selectedFile instanceof ElementaryFile))
            ISOException.throwIt(ISO7816.SW_COMMAND_NOT_ALLOWED);

        if(mode == READ_BINARY)
            return true;

        if(selectedFile == preferencesFile && cardholderPin.isValidated())
            return true;

        if(GPSystem.getCardContentState() == GPSystem.APPLICATION_SELECTABLE)
            return true;

        return false;
    }

    //@ requires this != null &*& buffer != null &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures true;
    private void readBinary(APDU apdu, byte[] buffer)
    {
        if(!fileAccessAllowed(READ_BINARY))
            ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);

        short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
        if(offset < 0)
            ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);

        short le = apdu.setOutgoing();

        if(selectedFile == masterFile)
            ISOException.throwIt(ISO7816.SW_FILE_INVALID);

        short size = ((ElementaryFile)selectedFile).getCurrentSize();
        if(offset > size)
            ISOException.throwIt(ISO7816.SW_WRONG_P1P2);

        short remaining = (short)(size - offset);
        if(le == 0)
        {
            if(remaining < 256)
            {
                short sw = (short)(ISO7816.SW_CORRECT_LENGTH_00 | remaining);
                ISOException.throwIt(sw);
            }
            else
                le = 256;
        }
        if(le > remaining)
            le = remaining;

        apdu.setOutgoingLength(le);

        ElementaryFile ef = (ElementaryFile)selectedFile;
        byte[] bf = ef.getData();

        apdu.sendBytesLong(bf, offset, le);
    }

    //@ requires this != null &*& buffer != null &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures true;
    private void activateFile(APDU apdu, byte[] buffer)
    {
        if(buffer[ISO7816.OFFSET_P2] != (byte)0x0C)
            ISOException.throwIt(ISO7816.SW_WRONG_P1P2);

        switch(buffer[ISO7816.OFFSET_P1])
        {
            case (byte)0x02:
                selectByFileIdentifier(apdu, buffer);
                break;
            case (byte)0x08:
                selectByPath(apdu, buffer);
                break;
            default:
                ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
                break;
        }

        if(!fileAccessAllowed(UPDATE_BINARY))
            ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);

        JCSystem.beginTransaction();
        selectedFile.setActive(true);
        JCSystem.commitTransaction();
    }

    //@ requires this != null &*& buffer != null &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures true;
    private void deactivateFile(APDU apdu, byte[] buffer)
    {
        if(buffer[ISO7816.OFFSET_P2] != (byte)0x0C)
            ISOException.throwIt(ISO7816.SW_WRONG_P1P2);

        switch(buffer[ISO7816.OFFSET_P1])
        {
            case (byte)0x02:
                selectByFileIdentifier(apdu, buffer);
                break;
            case (byte)0x08:
                selectByPath(apdu, buffer);
                break;
            default:
                ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
                break;
        }

        if(!fileAccessAllowed(UPDATE_BINARY))
            ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);

        JCSystem.beginTransaction();
        selectedFile.setActive(false);
        JCSystem.commitTransaction();
    }

    //@ requires this != null &*& buffer != null &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures true;
    private void selectByFileIdentifier(APDU apdu, byte[] buffer)
    {
        short byteRead = apdu.setIncomingAndReceive();
        short lc = (short)(buffer[ISO7816.OFFSET_LC] & 0x00FF);
        if((lc != 2) || (byteRead != 2))
            ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
        short fid = Util.makeShort(buffer[ISO7816.OFFSET_CDATA], buffer[ISO7816.OFFSET_CDATA + 1]);
        JCSystem.beginTransaction();
        if(fid == MF)
            selectedFile = masterFile;
        else {
            File s = ((DedicatedFile) masterFile).getSibling(fid);
            if(s != null)
                selectedFile = s;
            else {
                s = belpicDirectory.getSibling(fid);
                if(s != null)
                    selectedFile = s;
                else {
                    s = idDirectory.getSibling(fid);
                    if(s != null)
                        selectedFile = s;
                    else
                        ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);
                }
            }
        }
        JCSystem.commitTransaction();
    }

    //@ requires this != null &*& buffer != null &*& array_slice(buffer, 0, buffer.length, _);
    //@ ensures true;
    private void selectByPath(APDU apdu, byte[] buffer)
    {
        short byteRead = apdu.setIncomingAndReceive();
        short lc = (short)(buffer[ISO7816.OFFSET_LC] & 0x00FF);
        if(((lc & 1) == 1) || ((byteRead & 1) == 1))
            ISOException.throwIt(SW_INCONSISTENT_P1P2);
        if(buffer.length < ISO7816.OFFSET_CDATA + lc + 1)
            ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);

        File f = masterFile;
        for(byte i = 0; i < lc; i += 2)
        {
            short fid = Util.makeShort(buffer[(short)(ISO7816.OFFSET_CDATA + i)], buffer[(short)(ISO7816.OFFSET_CDATA + i + 1)]);
            if(i == 0 && fid == MF)
                f = masterFile;
            else {
                if(f instanceof ElementaryFile || f == null)
                    ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);
                f = ((DedicatedFile) f).getSibling(fid);
            }
        }
        if(f == null)
            ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);

        JCSystem.beginTransaction();
        selectedFile = f;
        JCSystem.commitTransaction();
    }

    

    

    //@ requires true;
    //@ ensures true;
    protected EidCard()
    {
        randomBuffer = new byte[256];
        responseBuffer = new byte[128];

        if(EidCard.randomData == null)
            EidCard.randomData = RandomData.getInstance(RandomData.ALG_SECURE_RANDOM);
        if(EidCard.cipher == null)
            EidCard.cipher = Cipher.getInstance(Cipher.ALG_RSA_NOPAD, false);
        Cipher c = Cipher.getInstance(Cipher.ALG_RSA_NOPAD, false);
        if(EidCard.messageBuffer == null)
            EidCard.messageBuffer = JCSystem.makeTransientByteArray((short)128, JCSystem.CLEAR_ON_DESELECT);

        previousApduType = JCSystem.makeTransientByteArray((short)1, JCSystem.CLEAR_ON_DESELECT);
        signatureType = JCSystem.makeTransientByteArray((short)1, JCSystem.CLEAR_ON_DESELECT);

        initializePins();
        initializeFileSystem();
        initializeEmptyLargeFiles();
        initializeKeyPairs();

        register();
    }
}