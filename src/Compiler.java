import java.io.File;
import java.util.LinkedList;
import java.util.Scanner;

import Parser.NonTerminals;
import Tokenizer.MicroPascalScanner;
import Tokenizer.Token;


public class Compiler {

	public static void main(String[] args) throws java.io.IOException
	{
		File testFile = new File("sample.mp");
		
		
		MicroPascalScanner sc = new MicroPascalScanner(testFile);
		System.out.println("\n\nCompiling using File: "+testFile);
		
		LinkedList<Token> list = new LinkedList<Token>();
		list = sc.getAllTokens();

		System.out.println("\nScanning...\n\n");

		System.out.println(
				"Token List:\n"+
				"  Loc [Line, Col]         Type                     Lexeme\n"+
				"--------------------------------------------------------------------------------------");
		for ( Token current : list ) {
			//System.out.print("  >>  "+"Ln:   "+current.getLineNumber()+"\tCl: "+current.getColumnNumber()+"\t\tType:  "+current.getToken()+"\t\tLex:  "+current.getLexeme());
			System.out.printf("    %1$-14s     %2$-20s     "+current.getLexeme()+"\n","["+current.getLineNumber()+", "+current.getColumnNumber()+"]",current.getToken());
			
		}
		
	//	list.remove(list.size() - 1);
		
		System.out.println("\n\n\nParsing...\n\n");
		NonTerminals.start(list);
		
	}

}
