package be.fedict.eidapplet;

import javacard.security.KeyPair;
import javacard.security.RSAPrivateKey;
import javacard.security.RSAPrivateCrtKey;
import javacard.security.RSAPublicKey;
import javacard.security.RandomData;
import javacardx.crypto.Cipher;
import org.globalplatform.GPSystem;

import javacard.framework.Applet;
import javacard.framework.*;
import javacard.security.PrivateKey;
import javacard.security.PublicKey;

public abstract class File {
	

	
	private short fileID;
	protected boolean active;
	
	public File(short fid) 
  	    
      	    
    	{
		fileID = fid;
		active = true;
		
		
		
	}
	public short getFileID() 
	    
	    
	{
		
		return fileID;
		
	}
	
	public void setActive(boolean b)
	    
	    
	{
		
		active = b;
		
	}
	
	
	public boolean isActive() 
	    
	    
	{
		
		return active;
		
	}
}

public class DedicatedFile extends File {

	

	

	
	private DedicatedFile parentFile;
	
	private static final byte MAX_SIBLINGS = 10;
	private File[] siblings;
	
	private byte number;
	
	protected DedicatedFile(short fid) 
  	    
      	    
	{
		super(fid);
		parentFile = null;
		siblings = new File[MAX_SIBLINGS];
		number = 0;
		
		
	}
	public DedicatedFile(short fid, DedicatedFile parent) 
  	    
      	    
	{
		super(fid);
		parentFile = parent;
		siblings = new File[MAX_SIBLINGS];
		number = 0;
		parent.addSibling(this);
		
		
	}
	public DedicatedFile getParent() 
	    
	    
	{
		
		return parentFile;
		
	}
	
	protected void addSibling(File s) 
  	    
  	    

	{
                
		if (number < MAX_SIBLINGS) {
			
			siblings[number++] = s;
			
			
			
			
			
		}
		
		
		
		
	}

	public File getSibling(short fid) 
  	    
      	    
	{
		
		
		
		for (byte i = 0; i < number; i++) 
		

		{
			File fl = siblings[i];
			
			
			if (fl != null && fl.getFileID() == fid) {
				
				return fl;
				
			}
			
		}
		
		return null;
	}

        
	public short getFileID() 
	    
	    
	{
		
		File thiz = this;
		return fileID;
		
	}
	
	public void setActive(boolean b)
	    
	    
	{
		
		
		File thiz = this;
		
		active = b;
		
		
		
	}
	
	public boolean isActive() 
	    
	    
	{
		
		
		
		return active;
		
		
		
	}
	
	

}

public final class MasterFile extends DedicatedFile {
	
	
	

	private static final short MF_FID = 0x3F00;
	public MasterFile() 
  	    
      	    
	{
		super(MF_FID);
		
	}
	
	
	public DedicatedFile getParent() 
	    
	    
	{
		
		
		
		return parentFile;
		
		
		
	}

	
	public File getSibling(short fid) 
  	    
      	    
	{
		
		
		return super.getSibling(fid);
		
		
	}
	
	
	public short getFileID() 
	    
	    
	{
		
		return fileID;
		
	}
	
	public void setActive(boolean b)
	    
	    
	{
		
		
		
		
		active = b;
		
		
		
		
	}
	
	public boolean isActive() 
	    
	    
	{
		
		
		
		
		return active;
		
		
		
		
	}
	
	protected void addSibling(File s) 
  	    
  	    

 	{
		
		
		
		super.addSibling(s);
		
		
	}
	
	

}

public final class ElementaryFile extends File {
	

	

		
	
	private DedicatedFile parentFile;
	
	private byte[] data;
	
	short size;
	public ElementaryFile(short fid, DedicatedFile parent, byte[] d) 
  	    
      	    
	{
		super(fid);
		parentFile = parent;
		parent.addSibling(this);
		data = d;
		size = (short) d.length;
		
	}
	public ElementaryFile(short fid, DedicatedFile parent, short maxSize) 
  	    
      	    
	{
		super(fid);
		parentFile = parent;
		parent.addSibling(this);
		data = new byte[maxSize];
		size = (short) 0;
		
		
	}
	public byte[] getData() 
  	    
      	    
	{
		if (active == true) {
			return data;
		} else {
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
			
			return null; 
		}
	}
	public short getCurrentSize() 
  	    
      	    
	{	
		
		
		if (active == true) {
			return size;
			
			
		} else {
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		}
	}
	public short getMaxSize() 
  	    
      	    
	{
		
		return (short) this.data.length;
		
	}
	public void eraseData(short offset) 
  	    
      	    
	{
		
		Util.arrayFillNonAtomic(data, offset, (short)(size - offset), (byte) 0);
		
	}
	public void updateData(short dataOffset, byte[] newData, short newDataOffset, short length) 
  	    

      	    
	{
		
		
		size = (short) (dataOffset + length);
		
		Util.arrayCopy(newData, newDataOffset, data, dataOffset, length);
		
	}

	
	public short getFileID() 
	    
	    
	{
		
		return fileID;
		
	}
	
	
	public void setActive(boolean b)
	    
	    
	{
		
		
		super.setActive(b);
		
		
	}
	
	
	public boolean isActive() 
	    
	    
	{
		
		
		boolean b = super.isActive();
		
		
		return b;
	}
	
	

}

public final class EidCard extends Applet {
	

	
	
	private final static byte EIDCARD_CLA_2 = (byte) 0x80;
	private final static byte EIDCARD_CLA_1 = (byte) 0x00;
	
	private final static byte INS_GET_RESPONSE = (byte) 0xC0;
	private final static byte INS_SELECT_FILE = (byte) 0xA4;
	private final static byte INS_ACTIVATE_FILE = (byte) 0x44;
	private final static byte INS_DEACTIVATE_FILE = (byte) 0x04;
	private final static byte INS_READ_BINARY = (byte) 0xB0;
	private final static byte INS_UPDATE_BINARY = (byte) 0xD6;
	private final static byte INS_ERASE_BINARY = (byte) 0x0E;
	private final static byte INS_VERIFY_PIN = (byte) 0x20;
	private final static byte INS_CHANGE_PIN = (byte) 0x24;
	private final static byte INS_UNBLOCK = (byte) 0x2C;
	private final static byte INS_GET_CHALLENGE = (byte) 0x84;
	private final static byte INS_INTERNAL_AUTHENTICATE = (byte) 0x88;

	private final static byte INS_EXTERNAL_AUTHENTICATE = (byte) 0x82;

	private final static byte INS_ENVELOPE = (byte) 0xC2;
	private final static byte INS_PREPARE_SIGNATURE = (byte) 0x22;
	private final static byte INS_GENERATE_SIGNATURE = (byte) 0x2A;
	private final static byte INS_GENERATE_KEYPAIR = (byte) 0x46;
	private final static byte INS_GET_KEY = (byte) 0xE2;
	private final static byte INS_PUT_KEY = (byte) 0xF2;
	private final static byte INS_ERASE_KEY = (byte) 0xF4;
	private final static byte INS_ACTIVATE_KEY = (byte) 0xF6;
	private final static byte INS_DEACTIVATE_KEY = (byte) 0xF8;
	private final static byte INS_GET_CARD_DATA = (byte) 0xE4;
	private final static byte INS_LOG_OFF = (byte) 0xE6;
	private final static byte INS_BLOCK = (byte) 0xE8;
	private byte[] previousApduType; 
	
	
	private final static byte VERIFY_CARDHOLDER_PIN = (byte) 0x01;
	
	private final static byte VERIFY_RESET_PIN = (byte) 0x02;
	private final static byte GENERATE_KEY_PAIR = (byte) 0x03;
	private final static byte OTHER = (byte) 0x00;
	
	

	private final static short SW_CANCELLED = (short) 0xFFFF;
	private final static short SW_ALGORITHM_NOT_SUPPORTED = (short) 0x9484;
	
	
	private final static short SW_WRONG_PIN_0_TRIES_LEFT = (short) 0x63C0;
	private final static short SW_INCONSISTENT_P1P2 = (short) 0x6A87;
	private final static short SW_REFERENCE_DATA_NOT_FOUND = (short) 0x6A88;
	
	private final static short SW_WRONG_LENGTH_00 = (short) 0x6C00;
	
	
	private final static byte OFFSET_PIN_HEADER = ISO7816.OFFSET_CDATA;
	private final static byte OFFSET_PIN_DATA = ISO7816.OFFSET_CDATA + 1;
	
	private final static byte OFFSET_SECOND_PIN_HEADER = ISO7816.OFFSET_CDATA + 8;

	private final static byte OFFSET_SECOND_PIN_DATA = ISO7816.OFFSET_CDATA + 9;

	private final static byte OFFSET_SECOND_PIN_DATA_END = ISO7816.OFFSET_CDATA + 15;
	
	protected final static byte PIN_SIZE = 8;
	protected final static byte CARDHOLDER_PIN = (byte) 0x01;
	protected final static byte CARDHOLDER_PIN_TRY_LIMIT = 3;
	protected final static byte RESET_PIN = (byte) 0x02;
	protected final static byte RESET_PIN_TRY_LIMIT = 10;
	protected final static byte UNBLOCK_PIN = (byte) 0x03;
	protected final static byte UNBLOCK_PIN_TRY_LIMIT = 12;
	protected final static byte ACTIVATE_PIN = (byte) 0x84;
	protected final static byte ACTIVATE_PIN_TRY_LIMIT = 15;
	protected OwnerPIN cardholderPin;
	protected OwnerPIN resetPin;
	protected OwnerPIN unblockPin;
	protected OwnerPIN activationPin;
	
	
	
	
	private byte signatureAlgorithm;
	private final static byte ALG_PKCS1 = (byte) 0x01;
	private final static byte ALG_SHA1_PKCS1 = (byte) 0x02;
	private final static byte ALG_MD5_PKCS1 = (byte) 0x04;
	private final static byte[] PKCS1_HEADER = { (byte) 0x00 };
	private final static byte[] PKCS1_SHA1_HEADER = { 0x00, (byte) 0x30, (byte) 0x21, (byte) 0x30, (byte) 0x09, (byte) 0x06, (byte) 0x05, (byte) 0x2b, (byte) 0x0e, (byte) 0x03, (byte) 0x02, (byte) 0x1a, (byte) 0x05, (byte) 0x00, (byte) 0x04,
			(byte) 0x14 };
	private final static byte[] PKCS1_MD5_HEADER = { (byte) 0x00, (byte) 0x30, (byte) 0x20, (byte) 0x30, (byte) 0x0c, (byte) 0x06, (byte) 0x08, (byte) 0x2a, (byte) 0x86, (byte) 0x48, (byte) 0x86, (byte) 0xf7, (byte) 0x0d, (byte) 0x02, (byte) 0x05,
			(byte) 0x05, (byte) 0x00, (byte) 0x04, (byte) 0x10 };
	private byte[] signatureType; 
	private final static byte NO_SIGNATURE = (byte) 0x00;
	private final static byte BASIC = (byte) 0x81;
	private final static byte AUTHENTICATION = (byte) 0x82;
	private final static byte NON_REPUDIATION = (byte) 0x83;
	private final static byte CA_ROLE = (byte) 0x87;
	
	
	protected static KeyPair basicKeyPair;
	protected static KeyPair authKeyPair;
	protected static KeyPair nonRepKeyPair;
	
	
	
	
	
	private static Cipher cipher;
	private static RandomData randomData;
	
	private static byte[] messageBuffer;
	

	protected final static short MF = (short) 0x3F00;
	protected final static short EF_DIR = (short) 0x2F00;
	protected final static short DF_BELPIC = (short) 0xDF00;
	protected final static short DF_ID = (short) 0xDF01;
	protected MasterFile masterFile;
	protected DedicatedFile belpicDirectory, idDirectory;
	protected ElementaryFile dirFile;
	
	protected final static short ODF = (short) 0x5031;
	protected final static short TOKENINFO = (short) 0x5032;
	protected final static short AODF = (short) 0x5034;
	protected final static short PRKDF = (short) 0x5035;
	protected final static short CDF = (short) 0x5037;
	protected final static short AUTH_CERTIFICATE = (short) 0x5038;
	protected final static short NONREP_CERTIFICATE = (short) 0x5039;
	protected final static short CA_CERTIFICATE = (short) 0x503A;
	protected final static short ROOT_CA_CERTIFICATE = (short) 0x503B;
	protected final static short RRN_CERTIFICATE = (short) 0x503C;
	protected ElementaryFile objectDirectoryFile, tokenInfo, authenticationObjectDirectoryFile, privateKeyDirectoryFile, certificateDirectoryFile, authenticationCertificate, nonRepudiationCertificate, caCertificate, rootCaCertificate, rrnCertificate;
	
	protected final static short IDENTITY = (short) 0x4031;
	protected final static short SGN_IDENTITY = (short) 0x4032;
	protected final static short ADDRESS = (short) 0x4033;
	protected final static short SGN_ADDRESS = (short) 0x4034;
	protected final static short PHOTO = (short) 0x4035;
	protected final static short CA_ROLE_ID = (short) 0x4038;
	protected final static short PREFERENCES = (short) 0x4039;
	protected ElementaryFile identityFile, identityFileSignature, addressFile, addressFileSignature, photoFile, caRoleIDFile, preferencesFile;

	

	
	private final static byte READ_BINARY = (byte) 0x01;

	private final static byte SEARCH_BINARY = (byte) 0x01;
	private final static byte UPDATE_BINARY = (byte) 0x02;
	private final static byte ERASE_BINARY = (byte) 0x02;

	private final static byte WRITE_BINARY = (byte) 0x04;
	

	private final static byte DELETE_CHILD_FILE = (byte) 0x01;

	private final static byte CREATE_EF = (byte) 0x02;

	private final static byte CREATE_DF = (byte) 0x04;
	

	private final static byte DEACTIVATE_FILE = (byte) 0x08;

	private final static byte ACTIVATE_FILE = (byte) 0x10;

	private final static byte TERMINATE_FILE = (byte) 0x20;

	private final static byte DELETE_FILE = (byte) 0x40;
	
	
	private byte[] randomBuffer;
	
	private byte[] responseBuffer;
	
	private File selectedFile;
	
	
	private short internalAuthenticateCounter = 5000;
	

	public static void install(byte[] bArray, short bOffset, byte bLength) 
  	    
      	    
	{
		
		new EidCard();
	}
	
	

	private void initializeFileSystem() 
  	    

      	

	{
		masterFile = new MasterFile();
		

		
		
		
		dirFile = new ElementaryFile(EF_DIR, masterFile, (short) 0x25);
		belpicDirectory = new DedicatedFile(DF_BELPIC, masterFile);
		tokenInfo = new ElementaryFile(TOKENINFO, belpicDirectory, (short) 0x30);
		objectDirectoryFile = new ElementaryFile(ODF, belpicDirectory, (short) 40);
		authenticationObjectDirectoryFile = new ElementaryFile(AODF, belpicDirectory, (short) 0x40);
		privateKeyDirectoryFile = new ElementaryFile(PRKDF, belpicDirectory, (short) 0xB0);
		certificateDirectoryFile = new ElementaryFile(CDF, belpicDirectory, (short) 0xB0);
		idDirectory = new DedicatedFile(DF_ID, masterFile);
		

		
		identityFile = new ElementaryFile(IDENTITY, idDirectory, (short) 0xD0);
		
		identityFileSignature = new ElementaryFile(SGN_IDENTITY, idDirectory, (short) 0x80);
		
		
		addressFile = new ElementaryFile(ADDRESS, idDirectory, (short) 117);
		
		addressFileSignature = new ElementaryFile(SGN_ADDRESS, idDirectory, (short) 128);
		
		caRoleIDFile = new ElementaryFile(CA_ROLE_ID, idDirectory, (short) 0x20);
		
		preferencesFile = new ElementaryFile(PREFERENCES, idDirectory, (short) 100);
		
		selectedFile = masterFile;
		
	}
	
	

	private void eraseBinary(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (!fileAccessAllowed(ERASE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		JCSystem.beginTransaction();
		
		if (selectedFile == masterFile)
			ISOException.throwIt(ISO7816.SW_FILE_INVALID); 
		
		
		short size = ((ElementaryFile)selectedFile).getCurrentSize();
		
		if (offset > size || offset < 0)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		((ElementaryFile) selectedFile).eraseData(offset);
		
		JCSystem.commitTransaction();
	}
	

	private void updateBinary(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (!fileAccessAllowed(UPDATE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		
		
		JCSystem.beginTransaction();
		
		if (selectedFile == masterFile)
			ISOException.throwIt(ISO7816.SW_FILE_INVALID); 
		
		short size = ((ElementaryFile) selectedFile).getMaxSize();
		if (offset > size)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		
		
		short byteRead = apdu.setIncomingAndReceive();
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc == 0) || (byteRead == 0))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		if (offset < 0 || ISO7816.OFFSET_CDATA + lc > buffer.length || offset + lc > size)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		((ElementaryFile) selectedFile).updateData(offset, buffer, ISO7816.OFFSET_CDATA, lc);
		
		JCSystem.commitTransaction();
	}
	

	private boolean fileAccessAllowed(byte mode) 
  	    
      	    
	{
			
		if (!(selectedFile instanceof ElementaryFile))
			ISOException.throwIt(ISO7816.SW_COMMAND_NOT_ALLOWED);
		
		if (mode == READ_BINARY) {
				return true;
		}
		
		
		if ((selectedFile == preferencesFile) && cardholderPin.isValidated()) {
				return true;
		}
		
		
		if (GPSystem.getCardContentState() == GPSystem.APPLICATION_SELECTABLE) {
				return true;			
		}
			
		return false;
	}
	

	private void getCardData(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00 || buffer[ISO7816.OFFSET_P2] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		
		apdu.setOutgoing();
		
		
								
		byte[] data = identityFile.getData(); 
		
		short pos = 1;
		
		short dataLen = (short) data[pos];
		pos = (short) (pos + 1 + dataLen + 1);
		
		if (dataLen <= 0 || dataLen + pos + 2 >= identityFile.getCurrentSize())
			ISOException.throwIt(ISO7816.SW_DATA_INVALID);
		
		dataLen = (short) data[pos];
		pos = (short) (pos + 1);
		
		if (dataLen < 0 || pos + dataLen >= identityFile.getCurrentSize())
			ISOException.throwIt(ISO7816.SW_DATA_INVALID);
		
		
		
		
		
		byte version[] = new byte[] { (byte) 0xA5, (byte) 0x03, (byte) 0x01, (byte) 0x01, (byte) 0x01, (byte) 0x11, (byte) 0x00, (byte) 0x02, (byte) 0x00, (byte) 0x01, (byte) 0x01, (byte) 0x0F };
		byte chipNumber[] = new byte[(short) (dataLen + 12)];
		Util.arrayCopy(data, pos, chipNumber, (short) 0, dataLen);
		Util.arrayCopy(version, (short) 0, chipNumber, dataLen, (short) 12);
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		
		apdu.setOutgoingLength((short) chipNumber.length);
		
		apdu.sendBytesLong(chipNumber, (short) 0, (short) chipNumber.length);
								
		
		
	}
	
	

	private void readBinary(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		
		if (!fileAccessAllowed(READ_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		if (offset < 0)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		
		short le = apdu.setOutgoing();
		
		if (selectedFile == masterFile)
			ISOException.throwIt(ISO7816.SW_FILE_INVALID); 
		
		short size = ((ElementaryFile) selectedFile).getCurrentSize();
		if (offset > size)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		short remaining = (short) (size - offset);
		if (le == 0) {
			if (remaining < 256) {
				
				
				short sw = (short) (ISO7816.SW_CORRECT_LENGTH_00 | remaining);
				ISOException.throwIt(sw);
			} else
				
				le = 256;
		}
		
		if (le > remaining) {
			le = remaining;
		}
		
		apdu.setOutgoingLength(le);
		
		
		
		
		
		
		
		
		ElementaryFile ef = (ElementaryFile)selectedFile;
		byte[] bf = ef.getData();
		
		apdu.sendBytesLong(bf, offset, le);
		
		
	}
	
	

	private void activateFile(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P2] != (byte) 0x0C)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		switch (buffer[ISO7816.OFFSET_P1]) {
		case (byte) 0x02:
			selectByFileIdentifier(apdu, buffer);
			break;
		case (byte) 0x08:
			selectByPath(apdu, buffer);
			break;
		default:
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
			break; 
		}
		
		if (!fileAccessAllowed(UPDATE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		JCSystem.beginTransaction();
		
		
		
		selectedFile.setActive(true);
		
		
		JCSystem.commitTransaction();
	}	
	
	static byte[] dirData;
	static byte[] tokenInfoData;
	static byte[] odfData;
	static byte[] aodfData;
	static byte[] prkdfData;
	static byte[] cdfData;
	static byte[] citizenCaCert;
	static byte[] rrnCert;
	static byte[] rootCaCert;
	static byte[] photoData;  
	
	

	private void clear() 
    	    
      	    
	{
		JCSystem.beginTransaction();
		
		

		
		Util.arrayFillNonAtomic(randomBuffer, (short) 0, (short) 256, (byte) 0);
		Util.arrayFillNonAtomic(responseBuffer, (short) 0, (short) 128, (byte) 0);
		
		selectedFile = masterFile;
		
		cardholderPin.reset();
		

		
		

		JCSystem.commitTransaction();
	}
	

	private void initializeEmptyLargeFiles() 
	    

      	    

	{
		

		caCertificate = new ElementaryFile(CA_CERTIFICATE, belpicDirectory, (short) 1200);
		rrnCertificate = new ElementaryFile(RRN_CERTIFICATE, belpicDirectory, (short) 1200);
		
		rootCaCertificate = new ElementaryFile(ROOT_CA_CERTIFICATE, belpicDirectory, (short) 1200);
		

		photoFile = new ElementaryFile(PHOTO, idDirectory, (short) 3584);
		

		authenticationCertificate = new ElementaryFile(AUTH_CERTIFICATE, belpicDirectory, (short) 1200);
		nonRepudiationCertificate = new ElementaryFile(NONREP_CERTIFICATE, belpicDirectory, (short) 1200);
	}
	
	

	private void initializeKeyPairs() 
  	    
      	    

	{
		

		if (EidCard.basicKeyPair != null && authKeyPair != null && nonRepKeyPair != null) {
			return;
		}
		
		
		basicKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) 1024);
		basicKeyPair.genKeyPair();
		
		authKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
		authKeyPair.genKeyPair();
		
		
	
		
		

		nonRepKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
		nonRepKeyPair.genKeyPair();
	
		
	}
	

	private void selectByFileIdentifier(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		short byteRead = apdu.setIncomingAndReceive();
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 2) || (byteRead != 2))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		short fid = Util.makeShort(buffer[ISO7816.OFFSET_CDATA], buffer[ISO7816.OFFSET_CDATA + 1]);
		JCSystem.beginTransaction();
		
		
		
		if (fid == MF)
			selectedFile = masterFile;		
		else {
			
			
			
			
			
			File s = ((DedicatedFile) masterFile).getSibling(fid);
			
			
			if (s != null) {
				selectedFile = s;
			
			} else {
				s = belpicDirectory.getSibling(fid);
				if (s != null) {
					selectedFile = s;
				} else {
					s = idDirectory.getSibling(fid);
					if (s != null) {
						selectedFile = s;
						
					} else {
						ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);
					}
				}
				
			}
			
		}	
		
		
		JCSystem.commitTransaction();
	}
	

	private void selectByPath(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		short byteRead = apdu.setIncomingAndReceive();
		
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		
		if (((lc & 1) == 1) || ((byteRead & 1) == 1))
			ISOException.throwIt(SW_INCONSISTENT_P1P2);
		if (buffer.length < ISO7816.OFFSET_CDATA + lc + 1)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		
		
		File f = masterFile;
		
		for (byte i = 0; i < lc; i += 2) 
		{
			short fid = Util.makeShort(buffer[(short) (ISO7816.OFFSET_CDATA + i)], buffer[(short) (ISO7816.OFFSET_CDATA + i + 1)]);
			
			if ((i == 0) && (fid == MF))
				f = masterFile;
			else {
			        
				if ((f instanceof ElementaryFile) || f == null)
					ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);
				
				
				

				

				f = ((DedicatedFile) f).getSibling(fid);
				

				

				
			}
		}
		if (f == null)
			ISOException.throwIt(ISO7816.SW_FILE_NOT_FOUND);

		JCSystem.beginTransaction();
		
		
		selectedFile = f;
		
		
		JCSystem.commitTransaction();
	}

	
	

	

	private void initializePins() 
  	    

      	    

      	    
	{
		

		
		byte cardhold[] = new byte[] { (byte) 0x24, (byte) 0x12, (byte) 0x34, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF, (byte) 0xFF };
		cardholderPin = new OwnerPIN(CARDHOLDER_PIN_TRY_LIMIT, PIN_SIZE);
		cardholderPin.update(cardhold, (short) 0, PIN_SIZE);
		

		
		byte unblock[] = new byte[] { (byte) 0x2c, (byte) 0x22, (byte) 0x22, (byte) 0x22, (byte) 0x11, (byte) 0x11, (byte) 0x11, (byte) 0xFF };
		unblockPin = new OwnerPIN(UNBLOCK_PIN_TRY_LIMIT, PIN_SIZE);
		unblockPin.update(unblock, (short) 0, PIN_SIZE);
		

		activationPin = new OwnerPIN(ACTIVATE_PIN_TRY_LIMIT, PIN_SIZE);
		activationPin.update(unblock, (short) 0, PIN_SIZE);
		

		
		byte reset[] = new byte[] { (byte) 0x2c, (byte) 0x33, (byte) 0x33, (byte) 0x33, (byte) 0x11, (byte) 0x11, (byte) 0x11, (byte) 0xFF };
		resetPin = new OwnerPIN(RESET_PIN_TRY_LIMIT, PIN_SIZE);
		resetPin.update(reset, (short) 0, PIN_SIZE);
	}
	
	

	protected EidCard() 
    	
    	
	{
		
		

		randomBuffer = new byte[256];
		responseBuffer = new byte[128];
		
		
		if (EidCard.randomData == null)
			EidCard.randomData = RandomData.getInstance(RandomData.ALG_SECURE_RANDOM);
		if (EidCard.cipher == null)
			EidCard.cipher = Cipher.getInstance(Cipher.ALG_RSA_NOPAD, false);
		Cipher c =  Cipher.getInstance(Cipher.ALG_RSA_NOPAD, false);
		if (EidCard.messageBuffer == null)
			EidCard.messageBuffer = JCSystem.makeTransientByteArray((short) 128, JCSystem.CLEAR_ON_DESELECT);
		
		previousApduType = JCSystem.makeTransientByteArray((short) 1, JCSystem.CLEAR_ON_DESELECT);
		signatureType = JCSystem.makeTransientByteArray((short) 1, JCSystem.CLEAR_ON_DESELECT);
		

		
		
		initializePins();
		
		initializeFileSystem();
		
		initializeEmptyLargeFiles();
		
		initializeKeyPairs();
		
 		
 		
 		
 		
 		
 		
 		
		
		register();
	}
	

	public boolean select() 
            
            
	{
		
		clear();
		return true;
	}
	

	public void deselect() 
    	    
    	    
	{
		clear();
		return;
	}
	

	public void process(APDU apdu) 
            
            
	{
		byte[] buffer = apdu.getBuffer();
		

		JCSystem.beginTransaction();
		
		if ((buffer[ISO7816.OFFSET_INS] != INS_GENERATE_SIGNATURE) && (buffer[ISO7816.OFFSET_INS] != INS_CHANGE_PIN) && (buffer[ISO7816.OFFSET_INS] != INS_GET_KEY))
			setPreviousApduType(OTHER);
		
		JCSystem.commitTransaction();
		
		if (selectingApplet()) {
			return;
		}
		if (buffer[ISO7816.OFFSET_CLA] == EIDCARD_CLA_1)
			
			switch (buffer[ISO7816.OFFSET_INS]) {
			
			
			
			case INS_VERIFY_PIN:
				verifyPin(apdu, buffer);
				break;
			case INS_CHANGE_PIN:
				changePin(apdu, buffer);
				break;
			case INS_UNBLOCK:
				unblock(apdu, buffer);
				break;
			case INS_GET_CHALLENGE:
				getChallenge(apdu, buffer);
				break;
			case INS_PREPARE_SIGNATURE:
				prepareForSignature(apdu, buffer);
				break;
			case INS_GENERATE_SIGNATURE:
				generateSignature(apdu, buffer);
				break;
			case INS_GENERATE_KEYPAIR:
				generateKeyPair(apdu);
				break;
			case INS_INTERNAL_AUTHENTICATE:
				internalAuthenticate(apdu, buffer);
				break;
			case INS_GET_RESPONSE:
				
				
				if (APDU.getProtocol() == APDU.PROTOCOL_T1)
					getResponse(apdu, buffer);
				else
					ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
				break;
			case INS_SELECT_FILE:
				selectFile(apdu, buffer);
				break;
			case INS_ACTIVATE_FILE:
				activateFile(apdu, buffer);
				break;
			case INS_DEACTIVATE_FILE:
				deactivateFile(apdu, buffer);
				break;
			case INS_READ_BINARY:
				readBinary(apdu, buffer);
				break;
			case INS_UPDATE_BINARY:
				updateBinary(apdu, buffer);
				break;
			case INS_ERASE_BINARY:
				eraseBinary(apdu, buffer);
				break;
			default:
				ISOException.throwIt(ISO7816.SW_INS_NOT_SUPPORTED);
				break; 
			}
		else if (buffer[ISO7816.OFFSET_CLA] == EIDCARD_CLA_2)
			switch (buffer[ISO7816.OFFSET_INS]) {
			case INS_GET_KEY:
				getPublicKey(apdu);
				break;
			case INS_PUT_KEY:
				putPublicKey(apdu, buffer);
				break;
			case INS_ERASE_KEY:
				eraseKey(apdu, buffer);
				break;
			case INS_ACTIVATE_KEY:
				activateKey(apdu, buffer);
				break;
			case INS_DEACTIVATE_KEY:
				deactivateKey(apdu, buffer);
				break;
			case INS_GET_CARD_DATA:
				getCardData(apdu, buffer);
				break;
			case INS_LOG_OFF:
				logOff(apdu, buffer);
				break;
			
			
			
			}
		else
			ISOException.throwIt(ISO7816.SW_CLA_NOT_SUPPORTED);
	}
	

	private void verifyPin(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		
		apdu.setIncomingAndReceive();
		
		JCSystem.beginTransaction();
		
		switch (buffer[ISO7816.OFFSET_P2]) {
		case CARDHOLDER_PIN:
			
			setPreviousApduType(VERIFY_CARDHOLDER_PIN);
			
			checkPin(cardholderPin, buffer);
			break;
		case ACTIVATE_PIN:
			
			checkPin(activationPin, buffer);
			
			if (GPSystem.getCardContentState() == GPSystem.APPLICATION_SELECTABLE)
				
				GPSystem.setCardContentState(GPSystem.CARD_SECURED);
			
			
			break;
		case RESET_PIN:
			
			setPreviousApduType(VERIFY_RESET_PIN);
			
			checkPin(resetPin, buffer);
			break;
		case UNBLOCK_PIN:
			
			checkPin(unblockPin, buffer);
			break;
		default:
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
		}
		
		JCSystem.commitTransaction();
	}
	

	private void checkPin(OwnerPIN pin, byte[] buffer) 
  	    
      	    
	{
		if (pin.check(buffer, OFFSET_PIN_HEADER, PIN_SIZE) == true)
			return;
		short tries = pin.getTriesRemaining();
		
		if (tries == 0) {
			
			if (pin == cardholderPin)
				
				GPSystem.setCardContentState(GPSystem.CARD_LOCKED);
			ISOException.throwIt(ISO7816.SW_FILE_INVALID);
		}
		

		short sw = (short) (SW_WRONG_PIN_0_TRIES_LEFT | tries);
		ISOException.throwIt(sw);
	}
	

	private void changePin(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		

		JCSystem.beginTransaction();
		
		
		if (buffer[ISO7816.OFFSET_P2] != (byte) 0x01) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		}
		
		switch (buffer[ISO7816.OFFSET_P1]) {
		case (byte) 0x00:
			setPreviousApduType(OTHER);
			
			JCSystem.commitTransaction();
			userChangePin(apdu, buffer);
			break;
		case (byte) 0x01:
			
			JCSystem.commitTransaction();
			administratorChangePin(apdu, buffer);
			break;
		default:
			setPreviousApduType(OTHER);
			
			JCSystem.commitTransaction();
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
			break; 
		}
		
	}
	

	private void userChangePin(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		
		short byteRead = apdu.setIncomingAndReceive();
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 16) || (byteRead != 16))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		checkPin(cardholderPin, buffer);
		
		if (!isNewPinFormattedCorrectly(buffer, OFFSET_SECOND_PIN_HEADER))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		
		cardholderPin.update(buffer, OFFSET_SECOND_PIN_HEADER, PIN_SIZE);
		
		
		cardholderPin.check(buffer, OFFSET_SECOND_PIN_HEADER, PIN_SIZE);
		
	}
	

	private void administratorChangePin(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		
		

		JCSystem.beginTransaction();
		
		
		if ((!resetPin.isValidated()) || (getPreviousApduType() != VERIFY_RESET_PIN)) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		}
		
		setPreviousApduType(OTHER);
		
		short byteRead = apdu.setIncomingAndReceive();
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 8) || (byteRead != 8))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		if (!isNewPinFormattedCorrectly(buffer, OFFSET_PIN_HEADER))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		
		if (!isNewPinCorrectValue(buffer))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		
		cardholderPin.update(buffer, OFFSET_PIN_HEADER, PIN_SIZE);
		
		JCSystem.commitTransaction();
	}
	

	private boolean isNewPinFormattedCorrectly(byte[] buffer, byte offset) 
  	    
      	    
	{
		
		if ((buffer[offset] >> 4) != 2)
			return false;
		
		
		byte pinLength = (byte) (buffer[offset] & 0x0F);
		
		if (pinLength < 4 || pinLength > 12)
			return false;
		
		
		byte pinLengthInBytes = (byte) (pinLength >> 1);
		
		
		if ((pinLength & (byte) 0x01) == (byte) 0x01)
			pinLengthInBytes++;
		
		byte i = (byte) (offset + PIN_SIZE - 1);
		for (; i > offset + pinLengthInBytes; i--) 
			

		{
			if (buffer[i] != (byte) 0xFF)
				return false;
		}
		
		if ((pinLength & (byte) 0x01) == (byte) 0x01) {
			if ( (byte) (buffer[i] << 4) != (byte) 0xF0)
				return false;
		}
		return true;
	}
	

	private boolean isNewPinCorrectValue(byte[] buffer) 
  	    

      	    
	{
		
		int tmp = buffer[OFFSET_PIN_HEADER];
		if(tmp < 0) { 
		  return false;
		}
		byte pinLength = (byte) (buffer[OFFSET_PIN_HEADER] & 0x0F);
		
		byte oldLength = (byte) (pinLength & 0x01);
		
		byte pinLengthInBytes = (byte) (pinLength >> 1);
		
		byte i;
		for (i = 0; i < pinLengthInBytes; i++) 
			

		{
			if (buffer[OFFSET_PIN_DATA + i] != (randomBuffer[i] & 0x77))
				return false;
		}
		if (oldLength == (byte) 0x01) {
			if ((buffer[OFFSET_PIN_DATA + pinLengthInBytes] >> 4) != ((randomBuffer[i] & 0x7F) >> 4))
				return false;
		}
		return true;
	}
	

	private void logOff(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00 || buffer[ISO7816.OFFSET_P2] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		
		JCSystem.beginTransaction();
		
		setPreviousApduType(OTHER);
		setSignatureType(NO_SIGNATURE);
		cardholderPin.reset();
		resetPin.reset();
		unblockPin.reset();
		activationPin.reset();
		
		JCSystem.commitTransaction();
	}
	

	private void unblock(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00 || buffer[ISO7816.OFFSET_P2] != (byte) 0x01)
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
		
		apdu.setIncomingAndReceive();
		
		
		checkPin(unblockPin, buffer);
		
		cardholderPin.resetAndUnblock();
		
		GPSystem.setCardContentState(GPSystem.CARD_SECURED);
		
	}
	

	private void prepareForSignature(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x41 || buffer[ISO7816.OFFSET_P2] != (byte) 0xB6)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		short byteRead = apdu.setIncomingAndReceive();
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 5) || (byteRead != 5))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		
		if ((buffer[ISO7816.OFFSET_CDATA] != (byte) 0x04) || (buffer[ISO7816.OFFSET_CDATA + 1] != (byte) 0x80) || (buffer[ISO7816.OFFSET_CDATA + 3] != (byte) 0x84))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		
		
		JCSystem.beginTransaction();
		
		switch (buffer[ISO7816.OFFSET_CDATA + 2]) {
		case ALG_SHA1_PKCS1:
			signatureAlgorithm = ALG_SHA1_PKCS1;
			break;
		case ALG_MD5_PKCS1:
			signatureAlgorithm = ALG_MD5_PKCS1;
			break;
		case ALG_PKCS1:
			signatureAlgorithm = ALG_PKCS1;
			break;
		default: 
			ISOException.throwIt(SW_ALGORITHM_NOT_SUPPORTED);
			break; 
		}
		
		switch (buffer[ISO7816.OFFSET_CDATA + 4]) {
		case BASIC:
			setSignatureType(BASIC);
			break;
		case AUTHENTICATION: 
			setSignatureType(AUTHENTICATION);
			break;
		case NON_REPUDIATION: 
			setSignatureType(NON_REPUDIATION);
			break;
		case CA_ROLE:
			setSignatureType(NO_SIGNATURE);
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
			break; 
		default:
			setSignatureType(NO_SIGNATURE);
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			break; 
		}
		
		JCSystem.commitTransaction();
	}
	

	private void generateSignature(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		

		JCSystem.beginTransaction();
		
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x9E || buffer[ISO7816.OFFSET_P2] != (byte) 0x9A) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		}
		
		
		if (getSignatureType() == NO_SIGNATURE) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
		}
		

		
		if ((getSignatureType() == NON_REPUDIATION) && (getPreviousApduType() != VERIFY_CARDHOLDER_PIN)) {
			setPreviousApduType(OTHER);
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		}
		
		setPreviousApduType(OTHER);

		
		if (getSignatureType() == BASIC)
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		if (!cardholderPin.isValidated())
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		
		JCSystem.commitTransaction();
		
		switch (signatureAlgorithm) {
		case ALG_MD5_PKCS1:
			
			generatePkcs1Md5Signature(apdu, buffer);
			
			break;
		case ALG_SHA1_PKCS1:
			
			generatePkcs1Sha1Signature(apdu, buffer);
			
			break;
		case ALG_PKCS1:
			
			generatePkcs1Signature(apdu, buffer);
			
			break;
		}
		
		
		if (APDU.getProtocol() == APDU.PROTOCOL_T1) {
			JCSystem.beginTransaction();
			
			Util.arrayCopy(buffer, (short) 0, responseBuffer, (short) 0, (short) 128);
			
			JCSystem.commitTransaction();
			
			
			
		} else {
			
			apdu.setOutgoingAndSend((short) 0, (short) 128);
		}
	}
	

	private void generatePkcs1Md5Signature(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		short byteRead = apdu.setIncomingAndReceive();
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 16) || (byteRead != 16))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		
		
		if (getSignatureType() == NON_REPUDIATION) {		
			cipher.init((RSAPrivateCrtKey)nonRepKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		if (getSignatureType() == AUTHENTICATION) {
			cipher.init((RSAPrivateCrtKey)authKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		
		JCSystem.beginTransaction();
		
		
		
		
		
		
		
		
		
		
		preparePkcs1ClearText(messageBuffer, ALG_MD5_PKCS1, lc);
		
		Util.arrayCopy(buffer, (short) (ISO7816.OFFSET_CDATA), messageBuffer, (short) (128 - lc), lc);

		
		

		
		JCSystem.commitTransaction();
		
		
		
		
		
		
		cipher.doFinal(messageBuffer, (short) 0, (short) 128, buffer, (short) 0);
		
		

		

	}
	

	private void generatePkcs1Sha1Signature(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		short byteRead = apdu.setIncomingAndReceive();
		
		
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc != 20) || (byteRead != 20))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		
		
		
		if (getSignatureType() == NON_REPUDIATION) {
			
			cipher.init((RSAPrivateCrtKey)nonRepKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		
		if (getSignatureType() == AUTHENTICATION) {
			cipher.init((RSAPrivateCrtKey)authKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		
		
		JCSystem.beginTransaction();
		
		
		
		
		
		

		
		preparePkcs1ClearText(messageBuffer, ALG_SHA1_PKCS1, lc);
		
		Util.arrayCopy(buffer, (short) (ISO7816.OFFSET_CDATA), messageBuffer, (short) (128 - lc), lc);

		
		

		
		JCSystem.commitTransaction();
		
		
		
		
		
		
		cipher.doFinal(messageBuffer, (short) 0, (short) 128, buffer, (short) 0);
		
		
		
	}
	

	private void generatePkcs1Signature(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		short byteRead = apdu.setIncomingAndReceive();
		
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if ((lc > 117) || (byteRead > 117))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		
		if (getSignatureType() == NON_REPUDIATION) {
			cipher.init((RSAPrivateCrtKey)nonRepKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		if (getSignatureType() == AUTHENTICATION) {
			cipher.init((RSAPrivateCrtKey)authKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		}
		
		JCSystem.beginTransaction();
		

		
		
		
		

		
		preparePkcs1ClearText(messageBuffer, ALG_PKCS1, lc);
		
		Util.arrayCopy(buffer, (short) (ISO7816.OFFSET_CDATA), messageBuffer, (short) (128 - lc), lc);
		
		

		
		JCSystem.commitTransaction();
		
		
		
		
		
		
		cipher.doFinal(messageBuffer, (short) 0, (short) 128, buffer, (short) 0);
		
		
		
	}
	

	private void preparePkcs1ClearText(byte[] clearText, short type, short messageLength) 
  	    

      	    

	{
		
		Util.arrayFillNonAtomic(clearText, (short) 0, (short) 128, (byte) 0xff);
		
		Util.arrayFillNonAtomic(clearText, (short) 0, (short) 1, (byte) 0x00);
		Util.arrayFillNonAtomic(clearText, (short) 1, (short) 1, (byte) 0x01);
		
		byte[] header = PKCS1_HEADER;
		if (type == ALG_SHA1_PKCS1)
			header = PKCS1_SHA1_HEADER;
		if (type == ALG_MD5_PKCS1)
			header = PKCS1_MD5_HEADER;
		Util.arrayCopy(header, (short) 0, clearText, (short) (128 - messageLength - header.length), (short) header.length);
	}
	

	private void generateKeyPair(APDU apdu) 
  	    
      	    
	{
		apdu.setIncomingAndReceive();
		
		byte[] buffer = apdu.getBuffer();
		
		if (GPSystem.getCardContentState() != GPSystem.APPLICATION_SELECTABLE)
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		if (lc != (short) 11)
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		byte offset = (ISO7816.OFFSET_CDATA + 0x01);
		
		
		
		
		if (buffer[offset] != (byte) 0x80)
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		
		
		
		
		
		
		JCSystem.beginTransaction();
		
		setPreviousApduType(GENERATE_KEY_PAIR);
		switch (buffer[ISO7816.OFFSET_P2]) {
		case BASIC:
			basicKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
			basicKeyPair.genKeyPair();
			
			break;
		case AUTHENTICATION: 
			authKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
			authKeyPair.genKeyPair();
			
			break;
		case NON_REPUDIATION: 
			nonRepKeyPair = new KeyPair(KeyPair.ALG_RSA_CRT, (short) (1024));
			nonRepKeyPair.genKeyPair();
			
			break;
		default:
			
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			break; 
		}
		
		JCSystem.commitTransaction();
	}
	

	private void getPublicKey(APDU apdu) 
  	    
      	    
	{
		
		
		byte[] buffer = apdu.getBuffer();
		
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		short le = apdu.setOutgoing();
		
		if (le != (short) (5 + 8 + 128))
			ISOException.throwIt((short) (SW_WRONG_LENGTH_00 + (5 + 8 + 128)));
		byte[] tempBuffer = new byte[le];
		tempBuffer[(short) 0] = (byte) 0x02;
		tempBuffer[(short) 1] = (byte) 0x08;
		tempBuffer[(short) 10] = (byte) 0x03;
		tempBuffer[(short) 11] = (byte) 0x81;
		tempBuffer[(short) 12] = (byte) 0x80;
		
		if (buffer[ISO7816.OFFSET_P2] == AUTHENTICATION){
			if (getPreviousApduType() != GENERATE_KEY_PAIR) {
				authKeyPair.getPublic().clearKey();
			        
				JCSystem.beginTransaction();
			        
				setPreviousApduType(OTHER);
			        
				JCSystem.commitTransaction();
			        
				ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
			}
			((RSAPublicKey) authKeyPair.getPublic()).getExponent(tempBuffer, (short) 7);
			((RSAPublicKey) authKeyPair.getPublic()).getModulus(tempBuffer, (short) 13);
		}else if (buffer[ISO7816.OFFSET_P2] == NON_REPUDIATION) { 
			if (getPreviousApduType() != GENERATE_KEY_PAIR) {
				nonRepKeyPair.getPublic().clearKey();
			        
				JCSystem.beginTransaction();
			        
				setPreviousApduType(OTHER);
				
				JCSystem.commitTransaction();
				
				ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
			}			
			((RSAPublicKey) nonRepKeyPair.getPublic()).getExponent(tempBuffer, (short) 7);
			((RSAPublicKey) nonRepKeyPair.getPublic()).getModulus(tempBuffer, (short) 13);
		}else if (buffer[ISO7816.OFFSET_P2] == BASIC) {		
			if (basicKeyPair == null)
				ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			((RSAPublicKey) basicKeyPair.getPublic()).getExponent(tempBuffer, (short) 7);
			((RSAPublicKey) basicKeyPair.getPublic()).getModulus(tempBuffer, (short) 13);
		} else {
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
		}
	        
		JCSystem.beginTransaction();
	        
		setPreviousApduType(OTHER);
		
		JCSystem.commitTransaction();
		
		authKeyPair.getPublic().clearKey();
		nonRepKeyPair.getPublic().clearKey();
		
		apdu.setOutgoingLength(le);
		
		apdu.sendBytesLong(tempBuffer, (short) 0, le);
		
	}
	

	private void putPublicKey(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
	}
	

	private void eraseKey(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		switch (buffer[ISO7816.OFFSET_P2]) {
		case BASIC:
			JCSystem.beginTransaction();
			
			basicKeyPair = null;
			
			JCSystem.commitTransaction();
			break;
		default:
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			break; 
		}
	}
	

	private void activateKey(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		switch (buffer[ISO7816.OFFSET_P2]) {
		case AUTHENTICATION:
			
			break;
		case NON_REPUDIATION:
			
			break;
		default:
			ISOException.throwIt(SW_REFERENCE_DATA_NOT_FOUND);
			break; 
		}
	}
	

	private void deactivateKey(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);
	}
	

	private void internalAuthenticate(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if ((buffer[ISO7816.OFFSET_P1] != ALG_SHA1_PKCS1) || buffer[ISO7816.OFFSET_P2] != BASIC)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		short byteRead = apdu.setIncomingAndReceive();
		
		short lc = (short) (buffer[ISO7816.OFFSET_LC] & 0x00FF);
		
		if ((lc == 0x97) || (byteRead == 0x97))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		if ((lc != 0x16) || (byteRead != 0x16))
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		
		
		if ((buffer[ISO7816.OFFSET_CDATA] != (byte) 0x94) || (buffer[ISO7816.OFFSET_CDATA + 1] != (byte) 0x14))
			ISOException.throwIt(ISO7816.SW_WRONG_DATA);
		
		JCSystem.beginTransaction();
		
		
		
		
		
		

		if (basicKeyPair == null)
			ISOException.throwIt(ISO7816.SW_CONDITIONS_NOT_SATISFIED);

		
		cipher.init(basicKeyPair.getPrivate(), Cipher.MODE_ENCRYPT);
		
		preparePkcs1ClearText(messageBuffer, ALG_SHA1_PKCS1, lc);
		
		Util.arrayCopy(buffer, (short) (ISO7816.OFFSET_CDATA + 2), messageBuffer, (short) 108, (short) 20);
		
		cipher.doFinal(messageBuffer, (short) 0, (short) 128, buffer, (short) 0);
		
		if (APDU.getProtocol() == APDU.PROTOCOL_T1) {
			Util.arrayCopy(buffer, (short) 0, responseBuffer, (short) 0, (short) 128);
			
			
		} else {
			
			apdu.setOutgoingAndSend((short) 0, (short) 128);
		}
		
		
		
		
		
		
		JCSystem.commitTransaction();
	}
	

	private void getResponse(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		
		short offset = Util.makeShort(buffer[ISO7816.OFFSET_P1], buffer[ISO7816.OFFSET_P2]);
		if (offset > responseBuffer.length)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		short le = apdu.setOutgoing();
		
		
		if ((le == 0) || (le == 256))
			le = 128;
		
		apdu.setOutgoingLength(le);
		
		if (offset + le > 128 || offset < 0)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		apdu.sendBytesLong(responseBuffer, offset, le);
		
	}
	

	private void getChallenge(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P1] != (byte) 0x00 || buffer[ISO7816.OFFSET_P2] != (byte) 0x00)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		short le = apdu.setOutgoing();
		
		if (le == 0)
			ISOException.throwIt(ISO7816.SW_WRONG_LENGTH);
		JCSystem.beginTransaction();
		
		RandomData random = EidCard.randomData;
		
		random.generateData(randomBuffer, (short) 0, le);
		
		apdu.setOutgoingLength(le);
		
		apdu.sendBytesLong(randomBuffer, (short) 0, le);
		
		JCSystem.commitTransaction();
	}
	

	private void selectFile(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P2] != (byte) 0x0C)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		switch (buffer[ISO7816.OFFSET_P1]) {
		case (byte) 0x02:
			selectByFileIdentifier(apdu, buffer);
			break;
		case (byte) 0x08:
			selectByPath(apdu, buffer);
			break;
		default:
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
			break; 
		}
	}
	

	private void setPreviousApduType(byte type) 
  	    
      	    
	{
		
		
		
		previousApduType[0] = type;
		
		
	}
	

	private byte getPreviousApduType() 
  	    
  	    
	{
		
		
		
		return previousApduType[0];
		
		
	}
	

	private void setSignatureType(byte type) 
  	    
      	    
	{
		
		
		
		signatureType[0] = type;
		
		
	}
	

	private byte getSignatureType() 
  	    
      	    
	{
		
		
		
		return signatureType[0];
		
		
	}
	

	

	private void deactivateFile(APDU apdu, byte[] buffer) 
  	    
      	    
	{
		
		if (buffer[ISO7816.OFFSET_P2] != (byte) 0x0C)
			ISOException.throwIt(ISO7816.SW_WRONG_P1P2);
		
		switch (buffer[ISO7816.OFFSET_P1]) {
		case (byte) 0x02:
			selectByFileIdentifier(apdu, buffer);
			break;
		case (byte) 0x08:
			selectByPath(apdu, buffer);
			break;
		default:
			ISOException.throwIt(ISO7816.SW_INCORRECT_P1P2);
			break; 
		}
		
		if (!fileAccessAllowed(UPDATE_BINARY))
			ISOException.throwIt(ISO7816.SW_SECURITY_STATUS_NOT_SATISFIED);
		JCSystem.beginTransaction();
		
	  	
		
		selectedFile.setActive(false);
		
		
		JCSystem.commitTransaction();
	}
}