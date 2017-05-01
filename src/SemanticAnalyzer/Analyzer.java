/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package SemanticAnalyzer;

import SymbolTable.*;
import Tokenizer.Token;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.ArrayList;

/**
 *
 * author n59r768
 */
public class Analyzer {

    private FileWriter writer;
    private String stackTop = "empty";
    private boolean changeNeg = false;
    private boolean changePos = false;
    private String beforeCall = "empty";
    private String first = "empty";
    private String[][] labels = new String[50][3];
    private static int labelNum = 0;
    private static String paramTypes = "";

    //can use this to pass in the file name and create new file
    public Analyzer() {
        File file = new File("Compiled.il");
        try {
            writer = new FileWriter(file);
        } catch (Exception ex) {
            System.out.println("couldn't make writer");
            System.exit(1);
        }

    }
    /*
     Add label for the symbol table. 
     Store label in an array list as a string(0: name, 1:kind, 2:label)
     */

    public void addLabel(SymbolTable symTable) {
        labels[labelNum][0] = symTable.getName();
	if(symTable.getParent() != null){
            labels[labelNum][1] = symTable.getParent().findVariable(symTable.getName()).getKind();
	}
	else{
            labels[labelNum][1] = "program";
	}
            labels[labelNum][2] = "L" + (labelNum + 1);
	labelNum++;
    }
    
//    public void addLabel(String name, int num){
//		labels[labelNum][0] = name + num;
//		labels[labelNum][1] = name;
//		labels[labelNum][2] = "L" + (labelNum + 1);
//		labelNum++;
//	}

    /*
     place a label at current location
     */
    public void placeLabel(String name){
	for(int i = labelNum -1; i >= 0; i--){
            if(labels[i][0].equals(name)){
                ptf(labels[i][2] + ":");
            }
	}
    }

    public void pushAddress(Token var, SymbolTable symTable){
        Row dat = symTable.findVariable(var.getLexeme());
        if(dat == null){
            ptf("PUSH #-1");
            paramTypes += "literal ";
            
        }
        else if(dat.getKind().equals("var")){
            ptf("PUSH D"+dat.getNestingLevel());
            ptf("PUSH #"+dat.getOffset());
            ptf("ADDS");
            paramTypes += "variable ";
        }
        else if(dat.getKind().equals("param")){
            ptf("PUSH D"+dat.getNestingLevel());
            ptf("PUSH #"+dat.getOffset());
            ptf("ADDS");
            paramTypes += "variable ";
        }
        else if(dat.getKind().equals("varParam")){
            ptf("PUSH "+dat.getOffset()+"(D"+dat.getNestingLevel()+")");
        }
    }
    
    public String getStackTop(){
        return stackTop;
    }
    public void functionProcedure(String pType, String paramsKind, SymbolTable symTable, Token call){
        Row callinfo = symTable.findVariable(call.getLexeme());
	String[] paramsPassed = pType.split(" ");
	String[] params = callinfo.getInputParameters().split(" ");
	String[] paramKinds = callinfo.getParameterKinds().split(" ");
	String[] kindsPassed = paramsKind.split(" ");
        
        if(params.length != paramsPassed.length){
            printError("Number of parameters incorrect");
        }
        for(int i =0; i<paramsPassed.length;i++){
            if(!paramsPassed[i].equals(params[i])){
                printError("Parameter type mismatch.");
            }
        }
        for(int i =0; i<paramsPassed.length;i++){
            if(paramsPassed[i].equals(params[i])){
                printError("Parameter type mismatch.");
            }
        }
        for(int i = labelNum-1;i>=0;i--){
            if(labels[i][0].equals("varParam")&&!(kindsPassed[i].equals("variable"))){
                printError("Incorrect kind parameter");
            }
        }
        if(!(params[0].equals(""))){
            ptf("SUB SP #"+params.length*2+" SP");
        }
        
        if(symTable.findVariable(call.getLexeme()).getKind().equals("function")){
            String type = symTable.findVariable(call.getLexeme()).getType();
            if(beforeCall.equals("float")){
                stackTop = type;
                beforeCall = "empty";
            }
            else if(beforeCall.equals("float")){
                if(type.equals("integer")||type.equals("boolean")){
                    stackTop = "float";
                    ptf("CASTSF");
                    beforeCall = "empty";
                }
                else if(type.equals("float")){
                    stackTop = "float";
                    beforeCall = "empty";
                }
                else{
                    printError("param not found" + call.getLineNumber()+","+call.getColumnNumber());
                }
                 
            }
            else if(beforeCall.equals("integer")||beforeCall.equals("boolean")){
                if(type.equals("integer")){
                    stackTop = type;
                    beforeCall = "empty";
                }
                else if(type.equals("boolean")){
                    stackTop = type;
                    beforeCall = "empty";
                }
                else if(type.equals("float")){
                    stackTop = "float";
                    ptf("CASTSF");
                    beforeCall = "empty";
                    
                }
                else{
                    printError("not int, float, bool"+call.getLineNumber()+","+call.getColumnNumber());
                }
            }
        }
    }
    public void branch(String name, String chk){
        if(chk.equals("always")){
            for(int i = labelNum-1;i>=0;i--){
                if(labels[i][0].equals(name)){
                    ptf("BR "+labels[i][2]);
                }
            }
        }
        else if(chk.equals("true")){
            if(!(stackTop.equals("boolean"))){
		printError("incorrect branching" );
            }
            else{
		for(int i = labelNum -1; i >= 0; i--){
                    if(labels[i][0].equals(name)){
                    ptf("BRTS " + labels[i][2]);
                    }
		}
            }
	}
	else if(chk.equals("false")){
            if(!(stackTop.equals("boolean"))){
            	printError("incorrect branching");
            }
            else{
		for(int i = labelNum -1; i >= 0; i--){
                    if(labels[i][0].equals(name)){
			ptf("BRFS " + labels[i][2]);
                    }
		}
            }
	}
	else if(chk.equals("equals")){
	    for(int i = labelNum -1; i >= 0; i--){
		if(labels[i][0].equals(name)){
                    if(stackTop.equals("integer")||stackTop.equals("empty")){
                    ptf("CMPEQS");
                    }
                    else{
                        ptf("CMPEQSF");
                    }
                    ptf("BRTS " + labels[i][2]);
                }
            }
	}
		
    stackTop = "empty";
    }
    
    public void pushCheck(Token var, SymbolTable symTable) {
        Row name = symTable.findVariable(var.getLexeme());
        if (name == null) {
            pushLit(var);
        } else {
            pushVar(var, symTable);
        }
    }

    /*
     push a variable to the stack
     */
    public void pushVar(Token var, SymbolTable symTable) {
        Row name = symTable.findVariable(var.getLexeme());
        if (name.getKind().equals("varParam")) {
            printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
            stackTop = name.getType();
        } else if (stackTop.equals("integer") || stackTop.equals("boolean")) {
            if (name.getType().equals("float")) {
                printToFile("CASTSF");
                printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                stackTop = name.getType();
            } else if (name.getType().equals("boolean") || name.getType().equals("integer")) {
                printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                if (name.getType().equals("integer")) {
                    stackTop = name.getType();
                }
            } else {
                printError("String in statement");
            }
            if (changePos || changeNeg) {
                printToFile("NEGS");
                changePos = false;
                changeNeg = false;
            }
        } else if (stackTop.equals("float")) {
            if (name.getType().equals("boolean") || name.getType().equals("integer")) {
                printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                printToFile("CASTSF");
            } else if (name.getType().equals("float")) {
                printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
            } else {
                printError("String in statement");
            }
            if (changePos || changeNeg) {
                printToFile("NEGS");
                changePos = false;
                changeNeg = false;
            }
        } else {
            if (stackTop.equals("empty")) {
                printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                stackTop = name.getType();
                if (changePos || changeNeg) {

                    if (stackTop.equals("float")) {
                        printToFile("NEGSF");
                    } else {
                        printToFile("NEGS");
                    }
                    changePos = false;
                    changeNeg = false;
                }
            } else if (stackTop.equals("integer") || stackTop.equals("boolean")) {

                if (name.getType().equals("float")) {
                    printToFile("CASTSF");
                    printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    stackTop = name.getType();
                } else if (name.getType().equals("boolean") || name.getType().equals("integer")) {
                    printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    if (name.getType().equals("integer")) {
                        stackTop = name.getType();
                    }
                } else {
                    printError("String in statement");
                }

                if (changePos || changeNeg) {
                    printToFile("NEGS");
                    changePos = false;
                    changeNeg = false;
                }

            } else if (stackTop.equals("float")) {
                if (name.getType().equals("boolean") || name.getType().equals("integer")) {
                    printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    printToFile("CASTSF");
                } else if (name.getType().equals("float")) {
                    printToFile("PUSH " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                } else {
                    printError("String in statement");
                }
                if (changePos || changeNeg) {
                    printToFile("NEGSF");
                    changePos = false;
                    changeNeg = false;
                }

            }

        }
    }

    public void pushLit(Token var) {
        //String varTok;
        if (stackTop.equals("empty")) {
            //varTok = var.getToken();
            switch (var.getToken()) {
                case "MP_STRING_LIT":
                    ptf("PUSH #\"" + var.getLexeme().substring(1, var.getLexeme().length() - 1) + "\"");
                    stackTop = "string";
                    break;
                case "MP_INTEGER_LIT":
                    stackTop = "integer";
                    ptf("push #" + var.getLexeme());
                    break;
                case "MP_FIXED_LIT":
                    stackTop = "float";
                    ptf("PUSH #" + var.getLexeme());
                    break;
                case "MP_TRUE":
                    ptf("PUSH #1");
                    stackTop = "boolean";
                    break;
                case "MP_FALSE":
                    ptf("PUSH #0");
                    stackTop = "boolean";
                    break;
                default:
                    System.out.println("pushlit() failed");
                    break;
            }
            if (changePos || changeNeg) {
                changePos = false;
                changeNeg = false;
                if (stackTop.equals("integer")) {
                    ptf("NEGS");
                } else if (stackTop.equals("float")) {
                    ptf("NEGSF");
                } else {
                    printError("Tried to change a non-number sign. line, col" + var.getLineNumber() + "," + var.getColumnNumber());
                }
            }
        } else if (stackTop.equals("boolean")) {
            if (var.getToken().equals("MP_NOT")) {
                if (stackTop.equals("integer")) {
                    printError("pushlit failed, non-boolean. line, col" + var.getLineNumber() + "," + var.getColumnNumber());
                }
                ptf("PUSH #1");
                ptf("SUBS");
                ptf("NEGS");
            } else {
                printError("illegal operation on a boolean. line, col" + var.getLineNumber() + "," + var.getColumnNumber());
            }
        } else if (stackTop.equals("integer")) {
            //varTok = var.getToken();
            switch (var.getToken()) {
                case "MP_FIXED_LIT":
                case "MP_FLOAT_LIT":
                    ptf("CASTSF");
                    ptf("PUSH #" + var.getLexeme());
                    stackTop = "float";
                    break;
                case "MP_TRUE":
                    if (stackTop.equals("integer")) {
                        printError("Can't cast boolean as int. " + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    ptf("PUSH #1");
                    break;
                case "MP_FALSE":
                    if (stackTop.equals("integer")) {
                        printError("Can't cast boolean as int. " + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    ptf("PUSH #0");
                    break;
                case "MP_INTEGER_LIT":
                    ptf("PUSH #" + var.getLexeme());
                    stackTop = "integer";
                    break;
                default:
                    printError("found " + var.getToken() + " but expected " + "var.getLexeme()");
            }
            if (changeNeg || changePos) {
                ptf("NEGS");
                changeNeg = false;
                changePos = false;
            }
        } else if (stackTop.equals("float")) {
            //varTok = var.getToken();
            switch (var.getToken()) {
                case "MP_FIXED_LIT":
                case "MP_FLOAT_LIT":
                    ptf("PUSH #" + var.getLexeme());
                    break;
                case "MP_TRUE":
                    if (stackTop.equals("integer")) {
                        printError("Can't cast boolean as float. " + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    //ptf("PUSH #1");
                    break;
                case "MP_FALSE":
                    if (stackTop.equals("integer")) {
                        printError("Can't cast boolean as float. " + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    //ptf("PUSH #0");
                    break;
                case "MP_NOT":
                    if (stackTop.equals("integer")) {
                        printError("Can't NOT a non-bool. line, col" + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    break;
                case "MP_INTEGER_LIT":
                    ptf("PUSH #" + var.getLexeme());
                    ptf("CASTSF");
                    break;
                default:
                    printError("found " + var.getToken() + " but expected " + "var.getLexeme()");
                    break;
            }
            if (changeNeg || changePos) {
                ptf("NEGSF");
                changeNeg = false;
                changePos = false;
            }
        }
    }

    public void checkPush(Token var, SymbolTable symTable) {
        Row name = symTable.findVariable(var.getLexeme());
        if (name == null) {
            pushLit(var);
        } else {
            pushVar(var, symTable);
        }
    }

    public void comma() {
        stackTop = "empty";
    }

    public void addVal(Token val) {
        String value = val.getLexeme();
        if (stackTop.equals("integer") || stackTop.equals("boolean")) {
            if (value.equals("to")) {
                ptf("PUSH #1");
                ptf("ADDS");
            } else {
                ptf("PUSH #-1");
                ptf("ADDS");
            }
        } else {
            if (value.equals("to")) {
                ptf("PUSH #1.0");
                ptf("ADDSF");
            } else {
                ptf("PUSH #-1.0");
                ptf("ADDSF");
            }
        }
    }
    
    public void pushReturn(String type){
        beforeCall = stackTop;
        stackTop = "empty";
        if(type.equals("float")){
            ptf("PUSH #0.0");
        }
        else if(type.equals("string")){
            ptf("PUSH #\"\"");
        }
        else{
            ptf("PUSH #0");
        }
    }

    public void pop(Token var, SymbolTable symTable){
        Row name = symTable.findVariable(var.getLexeme());
        if(name == null){
            printError("unable to assign variable:"+symTable.getName()+"line,col " + var.getLineNumber() + "," + var.getColumnNumber());
        }
        else if(name.getKind().equals("varParam")){
            String type;
            switch(stackTop){
                case "boolean":
                    if(name.getType().equals("boolean")){
                    ptf("POP "+ name.getOffset()+"(D"+ name.getNestingLevel()+")");
                    }
                    else{
                    printError("Unable to assign non bool to bool variable. line,col:" + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    break;
                case "integer":
                    type = name.getType();
                    if(type.equals("float")){
                        ptf("CASTSF");
                        ptf("POP "+ name.getOffset()+"(D" + name.getNestingLevel() + ")");
                    }
                    else if(type.equals("integer")||type.equals("boolean")){
                        ptf("POP " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    }
                    else{
                        printError("conversion not possible.line,col:" + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    break;
                case "float":
                    type = name.getType();
                    if(type.equals("float")){
                        ptf("POP " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    }
                    else if(type.equals("integer")||type.equals("boolean")){
                        ptf("CASTSI");
                        ptf("POP " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    }
                    else{
                        printError("conversion not possible.line,col:" + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    break;
                case "string":
                    type = name.getType();
                    if(type.equals("string")){
                        ptf("POP " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    }
                    else{
                        printError("conversion not possible.line,col:" + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    break;
                default:
                    printError("type unknown");
                    break;
            }
            stackTop = "empty";
        }
        else{
            String type;
            switch(stackTop){
                case "boolean":
                    if(name.getType().equals("boolean")){
                        ptf("POP "+ name.getOffset()+"(D"+ name.getNestingLevel()+")");
                    }
                else{
                    printError("Unable to assign non bool to bool variable. line,col:" + var.getLineNumber() + "," + var.getColumnNumber());
                }
                break;
                case "integer":
                    type = name.getType();
                    if(type.equals("float")){
                        ptf("CASTSF");
                        ptf("POP "+ name.getOffset()+"(D" + name.getNestingLevel() + ")");
                    }
                    else if(type.equals("integer")||type.equals("boolean")){
                        ptf("POP " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    }
                    else{
                        printError("conversion not possible.line,col:" + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                    break;
                case "float":
                    type = name.getType();
                    if(type.equals("float")){
                        ptf("POP " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    }
                    else if(type.equals("integer")||type.equals("boolean")){
                        ptf("CASTSI");
                        ptf("POP " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    }
                    else{
                        printError("conversion not possible.line,col:" + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                break;
                case "string":
                    type = name.getType();
                    if(type.equals("string")){
                        ptf("POP " + name.getOffset() + "(D" + name.getNestingLevel() + ")");
                    }
                    else{
                        printError("conversion not possible.line,col:" + var.getLineNumber() + "," + var.getColumnNumber());
                    }
                break;
                default:
                    printError("type unknown");
                    break;
            }
            stackTop = "empty";
        }
    }

    public void makeNegative(){
        if(stackTop.equals("float")){
            ptf("NEGSF");
        }
        else{
            ptf("NEGS");
        }
    }
    
    public void addC(Token temp){
        if(stackTop.equals("integer")||stackTop.equals("empty")){
            if(temp.getLexeme().equals(">")){
                ptf("CMPGTS");
            }
            else if(temp.getLexeme().equals(">=")){
                ptf("CMPGES");
            }
            else if(temp.getLexeme().equals("<")){
                ptf("CMPLTS");
            }
            else if(temp.getLexeme().equals("<=")){
                ptf("CMPLES");
            }
            else if(temp.getLexeme().equals("=")){
                ptf("CMPEQS");
            }
            else if(temp.getLexeme().equals("<>")){
                ptf("CMPNES");
            }
        }
        else if(stackTop.equals("float")){
            if(temp.getLexeme().equals(">")){
                ptf("CMPGTF");
            }
            else if(temp.getLexeme().equals(">=")){
                ptf("CMPGEF");
            }
            else if(temp.getLexeme().equals("<")){
                ptf("CMPLTF");
            }
            else if(temp.getLexeme().equals("<=")){
                ptf("CMPLEF");
            }
            else if(temp.getLexeme().equals("=")){
                ptf("CMPEQF");
            }
            else if(temp.getLexeme().equals("<>")){
                ptf("CMPNEF");
            }
        }
        else {
            printError("error in compare line " + temp.getLineNumber() + " col " + temp.getColumnNumber());
        }
        stackTop = "boolean";
    }
    public void addOperator(Token op, SymbolTable table){
        
        if(stackTop.equals("integer") || stackTop.equals("boolean")){
            if(stackTop.equals("boolean") && first.equals("boolean") && op.getToken().equals("MP_OR")){
		ptf("ORS");
            }
            else if(stackTop.equals("boolean") && first.equals("boolean") && op.getToken().equals("MP_AND")){
            	ptf("ANDS");
            }
            else if(op.getToken().equals("MP_AND")||op.getToken().equals("MP_OR")){
            	printError("Can't use op " + op.getLexeme() + " on type " + stackTop+ op.getLineNumber() +op.getColumnNumber());
            }
            else {
                if(op.getLexeme().equals("+")){
                    ptf("ADDS");
                }
                else if(op.getLexeme().equals("-")){
                    ptf("SUBS");
                }
                else if(op.getToken().equals("MP_DIV")){
                    ptf("DIVS");
                }
                else if(op.getLexeme().equals("*")){
                    ptf("MULS");
                }
                else if(op.getLexeme().equals("mod")){
                    ptf("MODS");
                }
                else{
                    printError("Can't use op " + op.getLexeme() + " on type " + stackTop+ op.getLineNumber() +op.getColumnNumber());
                }
            }
        }
	else if(stackTop.equals("float")){
            if(op.getLexeme().equals("+")){
		ptf("ADDSF");
            }
            else if(op.getLexeme().equals("-")){
		ptf("SUBSF");
            }
            else if(op.getLexeme().equals("/")){
		ptf("DIVSF");
            }
            else if(op.getToken().equals("MP_DIV")){
		ptf("DIVSF");
		ptf("CASTI");
            }
            else if(op.getLexeme().equals("*")){
		ptf("MULSF");
            }
            else if(op.getLexeme().equals("MP_MOD")){
		ptf("MODSF");
            }
            else{
		printError("Can't use op " + op.getLexeme() + " on type " + stackTop+ op.getLineNumber() +op.getColumnNumber());
            }
	}
	else{
            printError("addop "+op.getLineNumber() + " " + op.getColumnNumber());
	}
    }
        
    public void checkSides(){
        first = stackTop;
        stackTop = "empty";
    }
    
    public void rd(ArrayList<Token> vars, SymbolTable symTab) {
        Row current;
        for (int i = 0; i < vars.size(); i++) {
            current = symTab.findVariable(vars.get(i).getLexeme());
            if (current == null) {
                System.out.println("Can't read var " + vars.get(i).getLexeme() + " line:"
                        + vars.get(i).getLineNumber() + " col:" + vars.get(i).getColumnNumber());
                System.exit(1);
            } else if (current.getKind().equals("varParam")) {
                String temp = current.getType();
                if (temp.equals("integer") || temp.equals("boolean")) {
                    printToFile("RD " + current.getOffset() + "(D" + current.getNestingLevel() + ")");
                } else if (temp.equals("float")) {
                    printToFile("RDF " + current.getOffset() + "(D" + current.getNestingLevel() + ")");
                } else {
                    printToFile("RDS " + current.getOffset() + "(D" + current.getNestingLevel() + ")");
                }
            } else {
                String temp = current.getType();
                if (temp.equals("integer") || temp.equals("boolean")) {
                    printToFile("RD " + current.getOffset() + "(D" + current.getNestingLevel() + ")");
                } else if (temp.equals("float")) {
                    printToFile("RDF " + current.getOffset() + "(D" + current.getNestingLevel() + ")");
                } else {
                    printToFile("RDS " + current.getOffset() + "(D" + current.getNestingLevel() + ")");
                }
            }
        }
    }

    public void wrts() {
        System.out.println("WRTS");
        printToFile("WRTS");
        stackTop = "empty";

    }

    public void wrtln() {
        System.out.println("WRTLN");
        printToFile("WRTLN #\"\"");
        stackTop = "empty";
    }

    public void atEnd() {
        System.out.println("HLT");
        try {
            printToFile("HLT");
            writer.close();
        } catch (Exception ex) {
            System.out.println("couldn't write hlt command");
        }

    }
    
    public void beginStatement(SymbolTable symTable){
	int i;
        for(i = labelNum-1; i >= 0; i--){
            if(labels[i][0].equals(symTable.getName())){
		ptf(labels[i][2] + ":");
		ptf("PUSH D" + symTable.getNestingLevel());
		ptf("MOV SP D" + symTable.getNestingLevel());
		ptf("ADD SP #" + symTable.getSize() + " SP");
		break;
            }
	}
	if(labels[i][1].equals("function")||labels[i][1].equals("procedure")){
            String[] params = symTable.getParameters().split(" ");
            String[] paramKinds = symTable.getParameterKinds().split(" ");
            for(int j = params.length; j > 0; j--){
                if(paramKinds[j-1].equals("param")){
                	ptf("MOV " + ((j - params.length - 3) - (params.length - j + 1)) + "(D" + symTable.getNestingLevel() + ") " + j + "(D" + symTable.getNestingLevel() + ")");
                 }
                else if(paramKinds[j-1].equals("varParam")){
                    ptf("MOV " + ((j - params.length - 3) - (params.length - j)) + "(D" + symTable.getNestingLevel() + ") " + j + "(D" + symTable.getNestingLevel() + ")");
                }
            }
        }
    }
    
    public void endStatement(SymbolTable symTable){
        if(symTable.getParent() != null && symTable.getParent().findVariable(symTable.getName()).getKind() == "function"){
            String[] params = symTable.getParameters().split(" ");
            ptf("MOV " + (symTable.findVariable(symTable.getName()).getOffset()) + "(D" + symTable.getNestingLevel() + ") " + (-3 - (2*params.length)) + "(D" + symTable.getNestingLevel() + ")" );
	}
	ptf("SUB SP #" + symTable.getSize() + " SP");
	ptf("POP D" + symTable.getNestingLevel());
	for(int i = labelNum - 1; i >= 0; i--){
            if(labels[i][0].equals(symTable.getName())&&!(labels[i][1].equals("program"))){
            ptf("RET");
            }
        }
    }

    /*
     so I dont have to type printToFile......
     */
    private void ptf(String cmd) {
        printToFile(cmd);
    }
    /*
     Writes text to file for ouput.
     */

    public void printToFile(String machineCode) {
        try {
            System.out.println("writing code to file");
            writer.write(machineCode + "\n");
        } catch (Exception ex) {
            System.out.println("could not write machine code to file");
        }

    }

    private void printError(String msg) {
        System.out.println("Error: Symantic Analizer:" + msg);
        try {
            writer.close();
        } catch (IOException ex) {
            System.out.println("couldn't print error");
        }
        System.exit(1);
    }
    
//    public void addStepVal(Token stepVal){
//		String value = stepVal.getLexeme();
//		if(stackTop.equals("integer")|| stackTop.equals("boolean")){
//			if(value.equals("to")){
//				ptf("PUSH #1");
//				ptf("ADDS");
//			}
//			else{
//				ptf("PUSH #-1");
//				ptf("ADDS");
//			}
//		}
//		else{
//			if(value.equals("to")){
//				ptf("PUSH #1.0");
//				ptf("ADDSF");
//			}
//			else{
//				ptf("PUSH #-1.0");
//				ptf("ADDSF");
//			}
//		}
//		
//	}
//    public void forCheck(Token controlVar, String exit, SymbolTable symTab){
//		
//		Row info = symTab.findVariable(controlVar.getLexeme());
//		
//		for(int i = labelNum - 1; i > 0; i--){
//			if(labels[i][0].equals(exit)){
//				if(info.getType().equals("integer")){
//					ptf("BEQ " + info.getOffset() + "(D" + info.getNestingLevel() + ") -1(SP) " + labels[i][2]);
//				}
//				
//				else if(info.getType().equals("float")){
//					ptf("BEQF " + info.getOffset() + "(D" + info.getNestingLevel() + ") -1(SP) " + labels[i][2]);
//				}
//				
//				else{
//					printError("Trying to compare items in loop that aren't either a float or int Line:" + controlVar.getLineNumber() + " col:" + controlVar.getColumnNumber());
//				}
//			}
//		}
//	}
//    public void popSpecial(Token variable, SymbolTable symTab){
//		Row info = symTab.findVariable(variable.getLexeme());
//		
//		if (info.getType().equals("integer")){
//			ptf("CASTSI");
//			ptf("POP " + info.getOffset() + "(D" + info.getNestingLevel() + ")");
//		}
//		else{
//			ptf("CASTSF");
//			ptf("POP " + info.getOffset() + "(D" + info.getNestingLevel() + ")");
//		}
//	}
//    public void stepValue(Token Tokenvalue){
//		String value = Tokenvalue.getLexeme();
//		if(stackTop.equals("integer")|| stackTop.equals("boolean")){
//			if(value.equals("to")){
//				ptf("PUSH #1");
//			}
//			else{
//				ptf("PUSH #-1");
//			}
//		}
//		else{
//			if(value.equals("to")){
//				ptf("PUSH #1.0");
//			}
//			else{
//				ptf("PUSH #-1.0");
//			}
//		}
//	}
}
