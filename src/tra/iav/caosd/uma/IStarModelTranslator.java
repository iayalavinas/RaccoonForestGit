package tra.iav.caosd.uma;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.StringTokenizer;

import ilp.iav.caosd.uma.Comparator;
import ilp.iav.caosd.uma.ILPProblem;
import ilp.iav.caosd.uma.LinearConstraint;
import ilp.iav.caosd.uma.Term;
import istar.iav.caosd.uma.Actor;
import istar.iav.caosd.uma.Agent;
import istar.iav.caosd.uma.Contribution;
import istar.iav.caosd.uma.Dependency;
import istar.iav.caosd.uma.GoalTaskElement;
import istar.iav.caosd.uma.IStarEntity;
import istar.iav.caosd.uma.IStarModel;
import istar.iav.caosd.uma.IntentionalElement;
import istar.iav.caosd.uma.Refinement;

public class IStarModelTranslator {

	private ILPProblem problem;
	private IStarModel model;
	private Double bigM = 1000000000000000d;

	public IStarModelTranslator(ILPProblem p, IStarModel m) {
		problem = p;
		model = m;
	}

	public void translate() {
		HashMap<String, Actor> actorList = model.getActorList();
		Iterator<Actor> actorIterator = actorList.values().iterator();
		while (actorIterator.hasNext()) {
			Actor actor = actorIterator.next();
			// we add actor to the log structures
			Integer id = problem.getIndex(actor.getId());
			problem.addBoundingConstraint(id, 0, 100);
			// refinements
			addRefinements(actor);
			// contributions
			addContributions(actor);
			// actor constraint
			addActorConstraint(actor);
			// TO-DO
			// needed-by
			// qualifications

		}
		// add social dependencies
		addDependencies(model);
	}

	private void addRefinements(Actor act) {
		Iterator<Refinement> refinementIterator = act.getRefinementList().values().iterator();
		// System.out.println("Refinements para "+act.getText());
		List<LinearConstraint> aux;

		while (refinementIterator.hasNext()) {
			Refinement ref = refinementIterator.next();
			if (!ref.getAndRefinements().isEmpty()) {
				List<GoalTaskElement> children = ref.getAndRefinements();
				// se consigue el identificador del primer elemento
				Integer x_1Index = problem.getIndex(children.get(0).getId());
				if (!problem.isBounded(x_1Index)) {
					problem.addBoundingConstraint(x_1Index, 0, 100);
				}
				for (int i = 0; i < children.size() - 1; i++) {
					IntentionalElement alfa = new IntentionalElement(ref.getParent().getId() + "_alfa_" + i, "alfa");
					IntentionalElement fakeY = new IntentionalElement(ref.getParent().getId() + "_y_" + i, "alfa");
					// se añaden a la lista de identificadores
					int alfaIndex = problem.getIndex(alfa.getId());
					if (!problem.isBounded(alfaIndex)) {
						problem.addBoundingConstraint(alfaIndex, 0, 100);
					}
					int fakeYIndex = problem.getIndex(fakeY.getId());
					// se mete en la lista de variables binarias
					problem.addBoundingConstraint(fakeYIndex, 0, 1);
					// cogemos el índice de la siguiente variable
					GoalTaskElement x2 = children.get(i + 1);
					int x2Index = problem.getIndex(x2.getId());
					if (!problem.isBounded(x2Index)) {
						problem.addBoundingConstraint(x2Index, 0, 100);
					}
					// se añaden las constraints al problema
					aux = getAndConstraint(alfaIndex, fakeYIndex, x_1Index, x2Index);
					problem.addConstraintList(aux);
					// se asigna alfa al al siguiente x1
					x_1Index = alfaIndex;
					// for(int j=0;j<aux.size();j++) { System.out.println(aux.get(j).toString()); }
				}
				// se a�aden las restricciones asociadas a la variable real
				IntentionalElement fakeY = new IntentionalElement(ref.getParent().getId() + "_y_last", "alfa");
				int fakeYIndex = problem.getIndex(fakeY.getId());
				// se mete en la lista de variables binarias
				problem.addBoundingConstraint(fakeYIndex, 0, 1);
				int xIndex = problem.getIndex(ref.getParent().getId());
				int x_2Index = problem.getIndex(children.get(children.size() - 1).getId());
				if (!problem.isBounded(xIndex)) {
					problem.addBoundingConstraint(xIndex, 0, 100);
				}
				if (!problem.isBounded(x_2Index)) {
					problem.addBoundingConstraint(x_2Index, 0, 100);
				}
				aux = getAndConstraint(xIndex, fakeYIndex, x_1Index, x_2Index);

				// for(int j=0;j<aux.size();j++) { System.out.println(aux.get(j).toString()); }
				problem.addConstraintList(aux);

				// System.out.println("**********************************");
			} else {
				List<GoalTaskElement> children = ref.getOrRefinements();
				int x1Index = problem.getIndex(children.get(0).getId());
				if (!problem.isBounded(x1Index)) {
					problem.addBoundingConstraint(x1Index, 0, 100);
				}
				for (int i = 0; i < children.size() - 1; i++) {
					IntentionalElement alfa = new IntentionalElement(ref.getParent().getId() + "_alfa_" + i, "alfa");
					IntentionalElement fakeY = new IntentionalElement(ref.getParent().getId() + "_y_" + i, "alfa");
					// se añaden a la lista de identificadores
					int alfaIndex = problem.getIndex(alfa.getId());
					if (!problem.isBounded(alfaIndex)) {
						problem.addBoundingConstraint(alfaIndex, 0, 100);
					}
					int fakeYIndex = problem.getIndex(fakeY.getId());
					// se mete en la lista de variables binarias
					problem.addBoundingConstraint(fakeYIndex, 0, 1);
					// cogemos el índice de la siguiente variable
					GoalTaskElement x2 = children.get(i + 1);
					int x2Index = problem.getIndex(x2.getId());
					if (!problem.isBounded(x2Index)) {
						problem.addBoundingConstraint(x2Index, 0, 100);
					}
					// se añaden las constraints al problema
					aux = getOrConstraints(alfaIndex, fakeYIndex, x1Index, x2Index);
					/*
					 * for(int j=0;j<aux.size();j++) { System.out.println(aux.get(j).toString()); }
					 */
					problem.addConstraintList(aux);
					// se asigna alfa al al siguiente x1
					x1Index = alfaIndex;
				}
				// se a�aden las restricciones asociadas a la variable real
				IntentionalElement fakeY = new IntentionalElement(ref.getParent().getId() + "_y_last", "alfa");
				int fakeYIndex = problem.getIndex(fakeY.getId());
				// se mete en la lista de variables binarias
				problem.addBoundingConstraint(fakeYIndex, 0, 1);
				int xIndex = problem.getIndex(ref.getParent().getId());
				int x2Index = problem.getIndex(children.get(children.size() - 1).getId());

				if (!problem.isBounded(xIndex)) {
					problem.addBoundingConstraint(xIndex, 0, 100);
				}
				if (!problem.isBounded(x2Index)) {
					problem.addBoundingConstraint(x2Index, 0, 100);
				}
				aux = getOrConstraints(xIndex, fakeYIndex, x1Index, x2Index);
				problem.addConstraintList(aux);
				/*
				 * for(int j=0;j<aux.size();j++) { System.out.println(aux.get(j).toString()); }
				 * System.out.println("**********************************");
				 */
			}
		}
	}

	private void addContributions(Actor act) {
		Iterator<String> keyContIterator = act.getContributionList().keySet().iterator();
		List<LinearConstraint> res = new LinkedList<LinearConstraint>();
		List<Term> termList = new LinkedList<Term>();
		while (keyContIterator.hasNext()) {
			Contribution contribution = act.getContributionList().get(keyContIterator.next());
			// se busca el índice del objetivo contribución, si es que existe.
			int qualityIndex = problem.getIndex(contribution.getTarget().getId());
			// System.out.println("Indice quality: " + qualityIndex + " " +
			// contribution.getTarget().getText());
			if (!problem.isBounded(qualityIndex)) {
				problem.addBoundingConstraint(qualityIndex, 0, 100);
			}
			int index;
			// make
			List<IntentionalElement> contList = contribution.getMakeList();
			for (int i = 0; i < contList.size(); i++) {
				index = problem.getIndex(contList.get(i).getId());
				if (!problem.isBounded(index)) {
					problem.addBoundingConstraint(index, 0, 100);
				}
				termList.add(new Term(-1d, index));
			}
			// help
			contList = contribution.getHelpList();
			for (int i = 0; i < contList.size(); i++) {
				index = problem.getIndex(contList.get(i).getId());
				if (!problem.isBounded(index)) {
					problem.addBoundingConstraint(index, 0, 100);
				}
				termList.add(new Term(-0.75d, index));
			}
			// hurt
			contList = contribution.getHurtList();
			for (int i = 0; i < contList.size(); i++) {
				index = problem.getIndex(contList.get(i).getId());
				if (!problem.isBounded(index)) {
					problem.addBoundingConstraint(index, 0, 100);
				}
				termList.add(new Term(-0.5d, index));
			}
			// normalización de valores
			Double maxQuality = getMaxQuality(termList);
			// System.out.println(maxQuality);
			Double factor = 100 / maxQuality;
			for (int i = 0; i < termList.size(); i++) {
				termList.get(i).setWeight(termList.get(i).getWeight() * factor);
			}
			termList.add(new Term(1d, qualityIndex));
			LinearConstraint toAdd = new LinearConstraint(termList, 0, Comparator.Equal);
			res.add(toAdd);
			termList = new LinkedList<Term>();
		}
		problem.addEqualityConstraintList(res);
	}

	private void addActorConstraint(Actor act) {
		// se obtienen los elementos ra�ces
		Iterator<String> keyIterator = act.getWants().keySet().iterator();
		List<IntentionalElement> rootElements = new LinkedList<IntentionalElement>();
		while (keyIterator.hasNext()) {
			IntentionalElement ie = act.getWants().get(keyIterator.next());
			if (act.isRootElement(ie.getId())) {
				rootElements.add(ie);
			}
		}
		// se genera el peso
		Double weight = -1d / rootElements.size();
		List<Term> termList = new LinkedList<Term>();
		// se obtiene el indice del agente
		int actorIndex = problem.getIndex(act.getId());
		if (!problem.isBounded(actorIndex)) {
			problem.addBoundingConstraint(actorIndex, 0, 100);
		}
		termList.add(new Term(1d, actorIndex));
		for (int i = 0; i < rootElements.size(); i++) {
			int index = problem.getIndex(rootElements.get(i).getId());
			if (!problem.isBounded(index)) {
				problem.addBoundingConstraint(index, 0, 100);
			}
			termList.add(new Term(weight, index));
		}
		LinearConstraint actorConstraint = new LinearConstraint(termList, 0, Comparator.Equal);
		problem.addEqualityConstraint(actorConstraint);
	}

	private void addDependencies(IStarModel ism) {
		Integer dependerEle, dependum, dependeeEle;

		for (int i = 0; i < ism.getDependencyList().size(); i++) {
			Dependency dep = ism.getDependencyList().get(i);
			// se asignan los índices
			// depender element
			dependerEle = problem.getIndex(dep.getDependerEle().getId());
			dependeeEle = problem.getIndex(dep.getDependeeEle().getId());
			dependum = problem.getIndex(dep.getDependum().getId());
			// se crean las constraints
			List<Term> termList = new LinkedList<Term>();
			termList.add(new Term(1d, dependerEle));
			termList.add(new Term(-1d, dependum));
			LinearConstraint lc1 = new LinearConstraint(termList, 0, Comparator.LowerOrEqual);
			// System.out.println("LC1: "+lc1.toString());
			problem.addConstraint(lc1);
			termList = new LinkedList<Term>();
			termList.add(new Term(1d, dependum));
			termList.add(new Term(-1d, dependeeEle));
			LinearConstraint lc2 = new LinearConstraint(termList, 0, Comparator.LowerOrEqual);
			// System.out.println("LC2: "+lc2.toString());
			problem.addConstraint(lc2);
			// si los elementos no están en la lista de boudings se actualizan
			if (!problem.isBounded(dependerEle)) {
				problem.addBoundingConstraint(dependerEle, 0, 100);
			}
			if (!problem.isBounded(dependeeEle)) {
				problem.addBoundingConstraint(dependeeEle, 0, 100);
			}
			if (!problem.isBounded(dependum)) {
				problem.addBoundingConstraint(dependum, 0, 100);
			}
		}
	}

	private Double getMaxQuality(List<Term> termList) {
		Double res = 0d;
		// System.out.println("termList.size() " + termList.size());
		for (int i = 0; i < termList.size(); i++) {
			res = res + Math.abs(termList.get(i).getWeight()) * 100;
		}
		return res;
	}

	private List<LinearConstraint> getAndConstraint(int alfaIndex, int yIndex, int x1Index, int x2Index) {
		List<LinearConstraint> res = new LinkedList<LinearConstraint>();
		// System.out.println("ANDConstraint indexes: "+alfaIndex+" "+yIndex+"
		// "+x1Index+" "+x2Index);
		// generamos las restricciones.
		// R1: -x1+x2-My<=0
		List<Term> terms = new LinkedList<Term>();
		terms.add(new Term(-1d, x1Index));
		terms.add(new Term(1d, x2Index));
		terms.add(new Term(-bigM, yIndex));
		res.add(new LinearConstraint(terms, 0, Comparator.LowerOrEqual));
		// R2: x1-x2+My<=M
		terms = new LinkedList<Term>();
		terms.add(new Term(1d, x1Index));
		terms.add(new Term(-1d, x2Index));
		terms.add(new Term(bigM, yIndex));
		res.add(new LinearConstraint(terms, bigM.intValue(), Comparator.LowerOrEqual));
		// R3: alfa-x1 <=0
		terms = new LinkedList<Term>();
		terms.add(new Term(1d, alfaIndex));
		terms.add(new Term(-1d, x1Index));
		res.add(new LinearConstraint(terms, 0, Comparator.LowerOrEqual));
		// R4: alfa-x2<=0
		terms = new LinkedList<Term>();
		terms.add(new Term(1d, alfaIndex));
		terms.add(new Term(-1d, x2Index));
		res.add(new LinearConstraint(terms, 0, Comparator.LowerOrEqual));
		// R5:-alfa+x1+My<=M
		terms = new LinkedList<Term>();
		terms.add(new Term(-1d, alfaIndex));
		terms.add(new Term(1d, x1Index));
		terms.add(new Term(bigM, yIndex));
		res.add(new LinearConstraint(terms, bigM.intValue(), Comparator.LowerOrEqual));
		// R6: -alfa+x2-My<=0
		terms = new LinkedList<Term>();
		terms.add(new Term(-1d, alfaIndex));
		terms.add(new Term(1d, x2Index));
		terms.add(new Term(-bigM, yIndex));
		res.add(new LinearConstraint(terms, 0, Comparator.LowerOrEqual));
		return res;
	}

	private List<LinearConstraint> getOrConstraints(int alfaIndex, int yIndex, int x1Index, int x2Index) {
		List<LinearConstraint> res = new LinkedList<LinearConstraint>();
		// System.out.println("ORConstraint indexes: "+alfaIndex+" "+yIndex+"
		// "+x1Index+" "+x2Index);
		// generamos las restricciones.
		// R1: x1-x2-My<=0
		List<Term> terms = new LinkedList<Term>();
		terms.add(new Term(1d, x1Index));
		terms.add(new Term(-1d, x2Index));
		terms.add(new Term(-bigM, yIndex));
		res.add(new LinearConstraint(terms, 0, Comparator.LowerOrEqual));
		// R2: -x1+x2+My<=M
		terms = new LinkedList<Term>();
		terms.add(new Term(-1d, x1Index));
		terms.add(new Term(1d, x2Index));
		terms.add(new Term(bigM, yIndex));
		res.add(new LinearConstraint(terms, bigM.intValue(), Comparator.LowerOrEqual));
		// R3: -alfa+x1 <=0
		terms = new LinkedList<Term>();
		terms.add(new Term(-1d, alfaIndex));
		terms.add(new Term(1d, x1Index));
		res.add(new LinearConstraint(terms, 0, Comparator.LowerOrEqual));
		// R4: -alfa+x2<=0
		terms = new LinkedList<Term>();
		terms.add(new Term(-1d, alfaIndex));
		terms.add(new Term(1d, x2Index));
		res.add(new LinearConstraint(terms, 0, Comparator.LowerOrEqual));
		// R5:alfa-x1+My<=M
		terms = new LinkedList<Term>();
		terms.add(new Term(1d, alfaIndex));
		terms.add(new Term(-1d, x1Index));
		terms.add(new Term(bigM, yIndex));
		res.add(new LinearConstraint(terms, bigM.intValue(), Comparator.LowerOrEqual));
		// R6: alfa-x2-My<=0
		terms = new LinkedList<Term>();
		terms.add(new Term(1d, alfaIndex));
		terms.add(new Term(-1d, x2Index));
		terms.add(new Term(-bigM, yIndex));
		res.add(new LinearConstraint(terms, 0, Comparator.LowerOrEqual));
		return res;
	}

	// genera el modelo de objetivos coloreado y etiquetado.
	public void generateLabelledGoalModel(String resFile, String inputGoalModel, String labelledGoalModel) {
		Map<String, Integer> satLevelMap = getGoalModelRes(resFile);
		BufferedReader reader = null;
		PrintWriter pw = null;

		try {
			File inputFile = new File(inputGoalModel);
			reader = new BufferedReader(new FileReader(inputFile));
			pw = new PrintWriter(new FileWriter(new File(labelledGoalModel)));
			String line;
			Integer satLevel = null;
			while ((line = reader.readLine()) != null) {
				// se escribe la línea en el fichero de salida
				if (line.contains("\"display\": {},")) {
					pw.println("\"display\": {");
				} else {
					pw.println(line);
				}
				if (line.contains("\"id\":")) {
					// obtenemos el identificador
					StringTokenizer tokenizer = new StringTokenizer(line);
					// el primer toke es "id":
					tokenizer.nextToken();
					// el segunto token es el id rodeado de comillas
					String id = tokenizer.nextToken();
					// le quitamos el caracter del principio y del final.ç
					id = id.substring(1, id.length() - 2);
					// hay registrado algún nivel de satisfacción para este elemento intecional
					if (satLevelMap.containsKey(id)) {
						satLevel = satLevelMap.get(id);
					} else {
						// System.out.println("No hay nivel de satisfacción asociado a "+id);
						satLevel = null;
					}
				} else if (line.contains("\"customProperties\"") && satLevel != null) {
					line = reader.readLine();
					while (line.endsWith(",")) {
						pw.println(line);
						line = reader.readLine();
					}
					pw.println(line + ",");
					pw.println("\t\t    \"satLevel\": " + satLevel);
					// coloreamos el documento
				} else if (line.contains("display")) {
					modifyDisplayInformation(reader, pw, satLevelMap, line);
					// cuando el programa vuelve de esta rutina ha pintado la línea "tool":
					// "pistar.2.1.0",
				}

			}
			pw.println("");
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			if (reader != null)
				try {
					reader.close();
					pw.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
		}
	}

	// Devuelve el nivel de satisfacción del elemento intencional identificado con
	// el String
	private Map<String, Integer> getGoalModelRes(String file) {
		HashMap<String, Integer> res = new HashMap<String, Integer>();
		BufferedReader br;
		try {
			br = new BufferedReader(new FileReader(file));
			String texto = br.readLine();
			// cada posición de la lista resList se corresponde al valor de la variable
			// guardada en esa posición.
			HashMap<Integer, Integer> resList = new HashMap<Integer, Integer>();// <Index,Value>
			int index = 0;
			while (texto != null && index < problem.getVariables().size()) {
				if (texto.startsWith("-")) {
					texto = texto.substring(1);
				}
				Double number = Double.parseDouble(texto);
				Integer var = problem.getVariables().get(index);
				resList.put(var, number.intValue());
				// System.out.println(var+":"+texto);
				texto = br.readLine();
				index++;
			}
			for (int j = 0; j < problem.getVariables().size(); j++) {
				// Se extrae el nombre del objeto en su estructura.
				// Object name = problem.getMIDToName().get(problem.getVariables().get(j));
				Object name = problem.getNameFromID(problem.getVariables().get(j));
				if (name instanceof String) {
					// se obtiene el elemento intencional
					IStarEntity entity = model.getEntity((String) name);
					if (entity != null) {
						res.put(entity.getId(), resList.get(problem.getVariables().get(j)));
					}
				}
			}
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return res;
	}

	private String generateColorLabel(Integer satLevel) {
		String res = "";

		if (satLevel == 0) {
			res = "\t \"backgroundColor\": \"#FA1805\"";// rojo
		} else if (satLevel > 0 && satLevel <= 25) {
			res = "\t \"backgroundColor\": \"#BC5722\"";// naranja oscuro
		} else if (satLevel > 25 && satLevel < 50) {
			res = "\t \"backgroundColor\": \"#FF762E\"";// naranja claro
		} else if (satLevel == 50) {
			res = "\t \"backgroundColor\": \"#FFFFFF\"";
		} else if (satLevel > 50 && satLevel <= 75) {
			res = "\t \"backgroundColor\": \"#F5FF9F\"";// amarillo claro
		} else if (satLevel > 75 && satLevel <= 99) {
			res = "\t \"backgroundColor\": \"#D8FF22\"";// amarillo oscuro
		} else {
			res = "\t \"backgroundColor\": \"#77FF12 \"";// verde
		}

		return res;
	}

	private void modifyDisplayInformation(BufferedReader reader, PrintWriter printer, Map<String, Integer> satLevelMap,
			String lastLine) {
		Integer satLevel = null;
		List<String> custElem = new LinkedList<String>();
		try {
			String line = reader.readLine();
			String prevLine = new StringTokenizer(line).nextToken();
			// lo primero que lee esta función es siempre un identificador
			if (!lastLine.contains("\"display\": {},")) {
				while (!prevLine.equals("}") || !line.contains("},")) {
					System.out.println(line);
					if (line.contains("}")) {
						if (prevLine.contains("\"y\":")) {
							printer.println(line);
						} else {
							printer.println("\t },");
						}
					} else {
						if (!line.contains("backgroundColor"))
							printer.println(line);
					}
					if (line.contains(": {")) {
						// se extrae el identificador.
						StringTokenizer tokenizer = new StringTokenizer(line);
						String id = tokenizer.nextToken();
						id = id.substring(1, id.length() - 2);
						// ¿Hay un valor de satisfacción asociado a este id?
						if (satLevelMap.containsKey(id)) {
							custElem.add(id);
							satLevel = satLevelMap.get(id);
							printer.println(generateColorLabel(satLevel) + ",");
						}
					}
					prevLine = new StringTokenizer(line).nextToken();
					line = reader.readLine();
				}
			}
			// hemos llegado al final de la sección display, pero aún no hemos escrito el
			// caracter que la cierra
			// añadimos los elementos de los que no hemos proporcionado información de
			// representación.
			List<String> keyList = new LinkedList<String>();
			keyList.addAll(satLevelMap.keySet());
			List<String> pendingKeys = new LinkedList<String>();// Lista de elementos que tenemos que colorear
			for (int i = 0; i < keyList.size(); i++) {
				if (!custElem.contains(keyList.get(i))) {
					pendingKeys.add(keyList.get(i));
				}
			}
			for (int i = 0; i < pendingKeys.size() - 1; i++) {
				printer.println('"' + pendingKeys.get(i) + '"' + ": {");
				// System.out.println(pendingKeys.get(i));
				printer.println(generateColorLabel(satLevelMap.get(pendingKeys.get(i))));
				printer.println("},");
			}
			// se imprime el último elemento, que tiene que tener un cierre sin ,
			printer.println('"' + pendingKeys.get(pendingKeys.size() - 1) + '"' + ": {");
			printer.println(generateColorLabel(satLevelMap.get(pendingKeys.get(pendingKeys.size() - 1))));
			printer.println("}");
			// se cierra la sección display
			printer.println("},");
			// se pinta la línea de tool y el antes de salir.
			line = reader.readLine();
			printer.println(line);
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	public void setEveryActorObjectiveFunction() {
		HashMap<String, Actor> actorList = model.getActorList();
		Iterator<String> actorIterator = actorList.keySet().iterator();
		List<Integer> actorIndexList = new LinkedList<Integer>();

		while (actorIterator.hasNext()) {
			Actor actor = actorList.get(actorIterator.next());
			if (actor instanceof Agent) {
				// no hacemos nada...
			} else {
				Integer actorIndex = problem.getIndex(actor.getId());// .get(actor.getId());
				actorIndexList.add(actorIndex);
			}
		}
		Double weight = (1d / actorIndexList.size());
		// se generan los términos
		List<Term> terms = new LinkedList<Term>();
		for (int i = 0; i < actorIndexList.size(); i++) {
			terms.add(new Term(weight, actorIndexList.get(i)));
		}
		// se genera la función objetivo
		problem.setObjectiveFunction(terms);
	}

	public HashMap<String, Actor> getActorMap() {
		return model.getActorList();
	}

	// El nivel de satisfacción de un agente se mide como la suma ponderada de sus
	// elementos raíz
	public void setObjectiveFunctionForAgent(String id) {
		// 1. localizar al agente
		Actor actor = model.getActor(id);
		// 2. Localizar el índice de la variable que representa su satisfacción en el
		// modelo
		Integer actorIndex = problem.getID(actor.getId());
		List<Term> terms = new LinkedList<Term>();
		terms.add(new Term(1d, actorIndex));
		// 3. Generamos la función objetivo
		problem.setObjectiveFunction(terms);
	}

}
