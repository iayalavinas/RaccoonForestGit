package ilp.iav.caosd.uma;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;




public class ILPProblem {
	private List<Integer> variables,nonIntegerVariables;
	private HashMap<Object, Integer> mNamesToID;
	private HashMap<Integer, Object> mIDToName;
	private ObjectiveFunction objectiveFunction;
	private HashMap<Integer, Bounding> boundingConstraints;
	private List<LinearConstraint> constraints, equalityConstraints;
	private AtomicInteger mIDFactory = new AtomicInteger(1);

	public ILPProblem() {
		variables = new ArrayList<Integer>();
		mNamesToID = new HashMap<Object, Integer>();
		mIDToName = new HashMap<Integer, Object>();
		constraints = new LinkedList<LinearConstraint>();
		boundingConstraints = new HashMap<Integer, Bounding>();
		equalityConstraints = new LinkedList<LinearConstraint>();
		objectiveFunction = new ObjectiveFunction();
		nonIntegerVariables=new ArrayList<Integer>();
	}
	
	public void addNonIntegerVariable(Integer index) {
		nonIntegerVariables.add(index);
	}

	public Boolean isRegistered(Object key) {
		return mNamesToID.containsKey(key);
	}
	
	public Object[] getProblemObject(){
		return mIDToName.values().toArray();
	}

	public Boolean isBounded(Integer id) {
		return boundingConstraints.containsKey(id);
	}

	public Boolean addConstraint(LinearConstraint lc) {
		return constraints.add(lc);
	}

	public Boolean addConstraintList(List<LinearConstraint> lc) {
		return constraints.addAll(lc);
	}

	public Boolean addEqualityConstraint(LinearConstraint lc) {
		return equalityConstraints.add(lc);
	}

	public Boolean addEqualityConstraintList(List<LinearConstraint> lc) {
		return equalityConstraints.addAll(lc);
	}
	
	public List<Integer> getVariables(){
		return variables;
	}
	
	/*public HashMap<Integer, Object> getMIDToName(){
		return mIDToName;
	}*/
	public Object getNameFromID(Integer id) {
		return mIDToName.get(id);
	}

	public void printProblem() {
		System.out.println("Your ILP problem has " + variables.size() + " variables, " + "" + constraints.size()
				+ " linear constraints, " + equalityConstraints.size() + " equality constraints " + "and "
				+ boundingConstraints.size() + " bounding constraints.");
		// función objetivo
		if (objectiveFunction != null) {
			System.out.println("La función objetivo es: " + objectiveFunction.toString());
		}
		// Hay una variable que está en bounding constraint pero no está en variables
		System.out.println("The problem constraints are: ");
		for (int i = 0; i < constraints.size(); i++) {
			System.out.println(constraints.get(i).toString());
		}
		System.out.println("The problem equality constraints are: ");
		for (int i = 0; i < equalityConstraints.size(); i++) {
			System.out.println(equalityConstraints.get(i).toString());
		}
		System.out.println("The problem bounding constraints are: ");
		Iterator<Integer> iter = boundingConstraints.keySet().iterator();
		while (iter.hasNext()) {
			Integer aux = iter.next();
			System.out.println(aux + ":" + boundingConstraints.get(aux).toString());
		}
	}

	public void printVariablesIds() {
		Iterator<Object> iter = mNamesToID.keySet().iterator();
		while (iter.hasNext()) {
			Object key = iter.next();
			System.out.println(key.toString() + ":" + mNamesToID.get(key).toString());
		}
	}

	private int getNextID() {
		return mIDFactory.getAndIncrement();
	}

	public int getID(Object name) {
		return mNamesToID.get(name);
	}

	public int getIndex(Object var) {
		int res = -1;
		if (mNamesToID.containsKey(var)) {
			res = mNamesToID.get(var);
		} else {
			if ((var instanceof Integer)) {
				/*if ((Integer) var == 0) {
					System.out.println("Añadimos el nombre 0");
				}*/
			}
			res = getNextID();
			mIDToName.put(res, var);
			mNamesToID.put(var, res);
			variables.add(res);
		}
		return res;
	}

	public void addBoundingConstraint(int index, int lower, int upper) {
		// System.out.println("2: Se añade el bounding " + lower + " y " + upper + "
		// para" + index);
		if (lower == 0) {
			boundingConstraints.put(index, new Bounding(lower, upper));
		} else {
			Integer upperBound = upper - lower + 1;
			boundingConstraints.put(index, new Bounding(0, upperBound));
		}
	}

	public void generateIntLinProg(String fileName) {
		try {
			// System.out.println("Vamos a imprimir "+objectiveFunction.toString());
			PrintWriter pw = new PrintWriter(new FileWriter(fileName + ".m"));
			pw.println("% This is a automatically generated file");
			pw.println("tic");
			printObjectiveFunction(pw);
			// especificamos que todas las variables son enteras.
			String intConString = "intcon = [";
			for (int i = 0; i < variables.size(); i++) {
				Integer var=i+1;
				if(!nonIntegerVariables.contains(var)) {
					intConString = intConString + var + ",";
				}
			}
			// se modifica el final de la cadena
			intConString = intConString.substring(0, intConString.length() - 1) + "];";
			pw.println(intConString);
			printConstraints(pw, true);
			printConstraints(pw, false);
			printBoundings(pw);
			pw.println("x = intlinprog(f,intcon,A,b,Aeq,beq,lb,ub);");
			pw.println("csvwrite(\""+fileName.substring(0, fileName.length())+"-res.txt\",x)");
			pw.println("toc");
			pw.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	// los problemas de intlinprog son de minimización, por lo tanto la función
	// objetivos
	// tiene que estar multiplicada por -1.
	private void printObjectiveFunction(PrintWriter pw) {
		String objFuncString = "f = [";
		for (int i = 0; i < variables.size(); i++) {
			if (objectiveFunction.containsIndex(variables.get(i))) {
				objFuncString = objFuncString + objectiveFunction.getWeight(variables.get(i)) * (-1) + ";";
			} else {
				objFuncString = objFuncString + "0;";
			}
		}
		// modificamos el final de la cadena
		objFuncString = objFuncString.substring(0, objFuncString.length() - 1) + "];";
		// System.out.println(objFuncString);
		pw.println(objFuncString);
	}

	private void printConstraints(PrintWriter pw, Boolean inequality) {
		String aVector, bVector;
		List<LinearConstraint> toPrint;
		if (inequality) {
			aVector = "A = [";
			bVector = "b = [";
			toPrint = constraints;
		} else {
			aVector = "Aeq = [";
			bVector = "beq = [";
			toPrint = equalityConstraints;
		}
		for (int pIndex = 0; pIndex < toPrint.size(); pIndex++) {
			for (int vIndex = 0; vIndex < variables.size(); vIndex++) {
				if (toPrint.get(pIndex).containsIndex(variables.get(vIndex))) {
					// se imprime el peso
					aVector = aVector + toPrint.get(pIndex).getWeight(variables.get(vIndex)) + ",";
					// System.out.println("Se añade a A
					// "+toPrint.get(pIndex).getWeight(variables.get(vIndex)));
				} else {
					// 0
					aVector = aVector + "0,";
					// System.out.println("Se añade un 0");
				}
			}
			aVector = aVector.substring(0, aVector.length() - 1) + ";";
			bVector = bVector + toPrint.get(pIndex).getConstant() + ";";
		}
		aVector = aVector.substring(0, aVector.length() - 1) + "];";
		bVector = bVector.substring(0, bVector.length() - 1) + "];";
		pw.println(aVector);
		pw.println(bVector);
	}

	private void printBoundings(PrintWriter pw) {
		pw.println("lb = zeros(" + variables.size() + ",1);");
		String upperBoundString = "ub = [";
		for (int i = 0; i < variables.size(); i++) {
			Bounding bounding = boundingConstraints.get(variables.get(i));
			if (bounding == null) {
				System.out.println("Null bounding for variable " + mIDToName.get(variables.get(i)));
			}
			int upperBound = bounding.getMax();
			upperBoundString = upperBoundString + upperBound + ";";
		}
		upperBoundString = upperBoundString.substring(0, upperBoundString.length() - 1) + "];";
		pw.println(upperBoundString);
	}
	
	public void setObjectiveFunction(List<Term> terms) {
		objectiveFunction = new ObjectiveFunction();
		objectiveFunction.setTerms(terms);
	}
}
