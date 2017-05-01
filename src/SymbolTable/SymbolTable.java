package SymbolTable;

import java.util.LinkedList;
import java.util.ListIterator;

/**
 *
 * @author Jon Koenes
 */
public class SymbolTable {

    LinkedList<Row> items = new LinkedList<>();
    LinkedList<SymbolTable> children = new LinkedList<>();
    SymbolTable parent;
    int nestLevel;
    int size = 1;
    String tableName;

    //main constructor needs a parent, the nesting level, and the name of the table
    private SymbolTable(SymbolTable in_parent, int in_nest, String name) {
        parent = in_parent;
        nestLevel = in_nest;
        tableName = name;
    }

    public SymbolTable(String in_name) {
        parent = null;
        nestLevel = 0;
        tableName = in_name;
    }

    public String getName() {
        return tableName;
    }
    
    public int getNestingLevel() {
        return nestLevel;
    }

    public SymbolTable getParent() {
        return parent;
    }

    public int getSize() {
        return size;
    }

    public void setName(String name) {
        tableName = name;
    }

    public void setNestingLevel(int level) {
        nestLevel = level;
    }

    public void setParent(SymbolTable newParent) {
        parent = newParent;
    }
    

    /*
     Every variable has size 1, so size is increased by one each time we make a new row, 
     with 1 being the starting size to save room for the display register value later
     */
    public void addRow(String ID, String kind, String type, String returnValues, String inputParameters) {
	
	//check whether the variable name has been used already or not
    	Row currentRow;
        ListIterator<Row> it = items.listIterator();

        while (it.hasNext()) {
            currentRow = it.next();
            if (currentRow.getID().equals(ID) || (ID.equals(tableName) && !(kind.equals("retVar")))) {//checks if the variable name exists, or whether you've accidentally replaced the return variable
                printTableFromHere();
                System.out.println("Error\nThe identifier " + ID + " already exists in the table " + tableName);
                System.exit(1);
            }
        }
    	//passed tests, add it
        Row newRow = new Row(ID, kind, type, size++, 1, returnValues, inputParameters, nestLevel, "");
        items.add(newRow);
    }
    /*
     * this method is to add a row for function calls and parameter calls, because their size
     * is different from the size of a variable
     */
    public void addFunctionOrParameterRow(String ID, String kind, String type, String returnValues, String inputParameters, int in_size, String paramKinds) {
	
	//check whether the variable name has been used already or not
    	Row currentRow;
        ListIterator<Row> it = items.listIterator();

        while (it.hasNext()) {
            currentRow = it.next();
            if (currentRow.getID().equals(ID) || (ID.equals(tableName) && !(kind.equals("retVar")))) {//checks if the variable name exists, or whether you've accidentally replaced the return variable
                printTableFromHere();
                System.out.println("Error\nThe identifier " + ID + " already exists in the table " + tableName);
                System.exit(1);
            }
        }
    	//passed tests, add it
        Row newRow = new Row(ID, kind, type, size++, in_size, returnValues, inputParameters, nestLevel, paramKinds);
        items.add(newRow);
    }

    /*
     This method will find and return the row for information regarding an ID, following 
     the scope hierarchy. If no row with that particular ID is found, then null is returned
     */
    public Row findVariable(String id) {

        Row returnRow;
        ListIterator<Row> it = items.listIterator();

        while (it.hasNext()) {
            returnRow = it.next();
            if (returnRow.getID().equals(id)) {
                return returnRow;
            }
        }
        //the row we're looking for isn't in our list, we'll check our parent
        if (parent == null) { //have no parent, so variable doesn't exist
            return null;
        } else {
            return parent.findVariable(id);
        }
    }

    public SymbolTable makeNewTable(String name) {
        SymbolTable newTable = new SymbolTable(this, nestLevel + 1, name);
        children.add(newTable);
        return newTable;
    }
    
    /*
     * Finds all the items of kind "Parameter" and returns the list as a string
     * This function is used in getting a list of parameter for inserting functions and parameters into the symbol tables
     */
    public String getParameters(){
    	 Row current;
         ListIterator<Row> myitems = items.listIterator();

         String retString = "";
         while (myitems.hasNext()) {//prints items of current table
             current = myitems.next();
             if(current.getKind().equals("param") || current.getKind().equals("varParam")){
            	 retString += current.getType() + " ";
             }
         }
         if(retString.length() > 0) retString = retString.substring(0, retString.length() - 1);//This it to get rid of the trailing space
         
         return retString;
    }
    
    public String getParameterKinds(){
   	 Row current;
     ListIterator<Row> myitems = items.listIterator();

     String retString = "";
     while (myitems.hasNext()) {//prints items of current table
         current = myitems.next();
         if(current.getKind().equals("param") || current.getKind().equals("varParam")){
        	 retString += current.getKind() + " ";
         }
     }
     if(retString.length() > 0) retString = retString.substring(0, retString.length() - 1);//This it to get rid of the trailing space
     
     return retString;
    }


    /*
     method will print from current table down, including all children, but no parent
     */
    public void printTableFromHere() {

        Row current;
        ListIterator<Row> myitems = items.listIterator();
        
        System.out.println("\nTable: " + tableName + " NestingLevel: " + nestLevel + "  ---------------------------------------------------------------------------------");
        System.out.println("            ID         Kind      Type    Offset  Size    ReturnValues                                  InputParam");


        while (myitems.hasNext()) {//prints items of current table
            current = myitems.next();
            current.printRow();
        }

        SymbolTable currentTable;
        ListIterator<SymbolTable> childs = children.listIterator();
        while (childs.hasNext()) {//tell the children to print

        	currentTable = childs.next();
        	currentTable.printTableFromHere();
        }
    }

    /*
     prints entire symbol table tree
     */
    public void printTableFromTop() {

        if (parent != null) { //keeps traveling up the tree until we reach root parent
            parent.printTableFromTop();
        } 
        
        else { //we've are at the "root" table
            
            Row current;
            ListIterator<Row> myitems = items.listIterator();
            
            System.out.println("\nTable: " + tableName + " NestingLevel: " + nestLevel + "  ---------------------------------------------------------------------------------");
            System.out.println("            ID         Kind      Type    Offset  Size    ReturnValues                                  InputParam");
            
            while (myitems.hasNext()) {//prints items of current table
                current = myitems.next();
                current.printRow();
            }

            SymbolTable currentTable;
            ListIterator<SymbolTable> childs = children.listIterator();
            while (childs.hasNext()) {//tell the children to print
            	currentTable = childs.next();
            	currentTable.printTableFromHere();
            }
        }

    }

    /*
     prints only this symbol table
     */
    public void print() {
        Row current;
        ListIterator<Row> myitems = items.listIterator();

        while (myitems.hasNext()) {//prints items of current table
            current = myitems.next();
            current.printRow();
        }
    }
    
    public SymbolTable moveToChild(String name){
    	SymbolTable current;
    	ListIterator<SymbolTable> childs = children.listIterator();
    	while(childs.hasNext()){
    		current = childs.next();
    		if(current.getName().equals(name)){
    			return current;
    		}
    	}
    	return null;
    }

}
