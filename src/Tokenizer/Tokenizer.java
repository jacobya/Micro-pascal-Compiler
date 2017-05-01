package Tokenizer;

public abstract class Tokenizer implements I_Tokenizer {

	protected Token token;
	protected MicroPascalScanner myScanner;
	
	
	public Tokenizer(MicroPascalScanner in) {
		myScanner = in;
	}

}
