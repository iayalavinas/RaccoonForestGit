package istar.iav.caosd.uma;

import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;
import java.util.Set;

import org.json.simple.JSONArray;
import org.json.simple.JSONObject;
import org.json.simple.parser.JSONParser;
import org.json.simple.parser.ParseException;



public class IStarModel {
	private String modelFileName;
	private HashMap<String,Actor> actorList=new HashMap<String,Actor>();
	private HashMap<String, IStarEntity> entityList = new HashMap<String, IStarEntity>();
	private List<Dependency> dependencyList = new LinkedList<Dependency>();
	private HashMap<String, Refinement> refinementList = new HashMap<String, Refinement>();
	private  HashMap<String, Contribution> contributionList = new HashMap<String, Contribution>();
	
	public HashMap<String,Actor> getActorList(){
		return actorList;
	}
	
	public Actor getActor(String id) {
		return actorList.get(id);
	}

	public void parseModel(String modelFile) {
		modelFileName=modelFile;
		JSONParser parser = new JSONParser();
		try {
			JSONObject istarRoot = (JSONObject) parser.parse(new FileReader(modelFile));
			// adding actors and its intentional elements
			JSONArray actorArray = (JSONArray) istarRoot.get("actors");
			String id, text, type;
			for (Object jObj : actorArray) {
				JSONObject actor = (JSONObject) jObj;
				id = (String) actor.get("id");
				text = (String) actor.get("text");
				type = (String) actor.get("type");
				if (type.equals("istar.Agent")) {
					Agent ag = new Agent(id, text);
					entityList.put(id, ag);
					actorList.put(id, ag);
					addInternalNodes(actor, ag, entityList);
				} else if (type.equals("istar.Role")) {
					Role ro = new Role(id, text);
					entityList.put(id, ro);
					actorList.put(id,ro);
					addInternalNodes(actor, ro, entityList);
				} else if (type.equals("istar.Actor")) {
					Actor act = new Actor(id, text);
					entityList.put(id, act);
					actorList.put(id,act);
					addInternalNodes(actor, act, entityList);
				}
				// System.out.println(id+" "+text+" "+type);
			}
			// adding social dependencies
			JSONArray dependencyArray = (JSONArray) istarRoot.get("dependencies");
			for (Object jObj : dependencyArray) {
				JSONObject dependency = (JSONObject) jObj;
				id = (String) dependency.get("id");
				text = (String) dependency.get("text");
				type = (String) dependency.get("type");
				Dependency depen = new Dependency(id, text);
				// System.out.println(id+" "+text+" "+type);
				IntentionalElement ie = null;
				if (type.equals("istar.Goal")) {
					ie = new Goal(id, text);
				} else if (type.equals("istar.Task")) {
					ie = new Task(id, text);
				} else if (type.equals("istar.Quality")) {
					ie = new Quality(id, text);
				} else if (type.equals("istar.Resource")) {
					ie = new Resource(id, text);
				}
				depen.setDependum(ie);
				String source = (String) dependency.get("source");
				depen.setDependerEle(entityList.get(source));
				String target = (String) dependency.get("target");
				depen.setDependeeEle(entityList.get(target));
				// puede suceder que el depender o el dependee sean actores en lugar de
				// intentional elements
				IStarEntity aux = entityList.get(source);
				if (aux instanceof Actor) {
					depen.setDepender((Actor) aux);
				} else {
					Actor depender = getOwner(source, entityList);
					depen.setDepender(depender);
				}
				aux = entityList.get(target);
				if (aux instanceof Actor) {
					depen.setDependee((Actor) aux);
				} else {
					Actor dependee = getOwner(target, entityList);
					depen.setDependee(dependee);
				}
				dependencyList.add(depen);
				entityList.put(id, depen);
			}
			// adding links
			JSONArray linkArray = (JSONArray) istarRoot.get("links");
			for (Object jObj : linkArray) {
				JSONObject link = (JSONObject) jObj;
				id = (String) link.get("id");
				type = (String) link.get("type");

				// System.out.println(id+" "+type);
				// A la hora de asignar enlaces tenemos que tener en cuenta que piStar no
				// permite
				// configuraciones incorrectas. No tenemos que hacer comprobaciones adicionales.
				if (type.equals("istar.ContributionLink")) {
					String label = (String) link.get("label");
					addContribution((String) link.get("target"), (String) link.get("source"), label);
				} else if ((type.equals("istar.AndRefinementLink")) || (type.equals("istar.OrRefinementLink"))) {
					addRefinement((String) link.get("target"), (String) link.get("source"), type);
				} else if (type.equals("istar.ParticipatesInLink")) {
					Actor source = (Actor) entityList.get((String) link.get("source"));
					Actor target = (Actor) entityList.get((String) link.get("target"));
					source.addParticipatesIn(target);
				} else if (type.equals("istar.DependencyLink")) {
					// estas dependencias ya las hemos recogidos con los dependency
					// aqu� las ignoramos
				} else if (type.equals("istar.IsALink")) {
					Actor source = (Actor) entityList.get((String) link.get("source"));
					Actor target = (Actor) entityList.get((String) link.get("target"));
					source.addIs(target);
				} else if (type.equals("istar.QualificationLink")) {
					IntentionalElement ie = (IntentionalElement) entityList.get((String) link.get("target"));
					Quality qua = (Quality) entityList.get((String) link.get("source"));
					if (ie instanceof GoalTaskElement) {
						((GoalTaskElement) ie).addQualification(qua);
					} else {
						((Resource) ie).addQualification(qua);
					}
				}else if(type.equals("istar.NeededByLink")) {
					// The source is the resource and the target is the task
					Task task=(Task)entityList.get((String)link.get("target"));
					Resource res=(Resource)entityList.get((String)link.get("source"));
					task.addNeededResource(res);
				}
			}

		} catch (IOException | ParseException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	// actualiza un quality para indicar sus contribuciones.
	private  void addContribution(String qualityId, String source, String label) {
		Contribution cont;
		// Est�n registradas las contribuciones a esta quality?
		if (contributionList.containsKey(qualityId)) {
			cont = contributionList.get(qualityId);
		} else {
			Quality quality = (Quality) entityList.get(qualityId);
			cont = new Contribution(quality);
		}
		IntentionalElement intElem = (IntentionalElement) entityList.get(source);
		if (label.equals("hurt")) {
			cont.addHurtContribution(intElem);
		} else if (label.equals("make")) {
			cont.addMakeContribution(intElem);
		} else if (label.equals("help")) {
			cont.addHelpContribution(intElem);
		} else {
			cont.addBreakContribution(intElem);
		}
		contributionList.put(qualityId, cont);
		
		// actualizamos esta contribuci�n en su actor
		Actor actor=getIntentionOwner(qualityId);
		actor.getContributionList().put(qualityId, cont);
	}

	private  void addRefinement(String target, String source, String type) {
		Refinement refi;
		// est� ya registrado este objetivo?
		if (refinementList.containsKey(target)) {
			refi = refinementList.get(target);
		} else {
			// obtenemos la referencia a ese objetivo.
			GoalTaskElement gte = (GoalTaskElement) entityList.get(target);
			refi = new Refinement(gte);
		}
		// recuperamos la referencia a la fuente del refinamiento.
		GoalTaskElement gte = (GoalTaskElement) entityList.get(source);
		if (type.equals("istar.AndRefinementLink")) {
			refi.addAndRefinement(gte);
		} else {
			refi.addOrRefinement(gte);
		}
		refinementList.put(target, refi);
		// recuperamos al actor due�o de este intentional element
		Actor actor=getIntentionOwner(target);
		actor.getRefinementList().put(target, refi);
		
	}

	private  Actor getOwner(String id, HashMap<String, IStarEntity> entityList) {
		Actor res = null;
		Boolean end = false;
		Set<String> keyList = entityList.keySet();
		Iterator<String> iter = keyList.iterator();

		while (iter.hasNext() && !end) {
			String key = iter.next();
			IStarEntity entity = entityList.get(key);
			if (entity instanceof Actor) {
				if (((Actor) entity).wants(id)) {
					res = (Actor) entity;
					end = true;
				}
			}
		}
		return res;
	}

	// add intentional elements in the bounding of the actor. Update the entitylist with these elements
	private  void addInternalNodes(JSONObject actor, Actor ag, HashMap<String, IStarEntity> el) {

		JSONArray nodeArray = (JSONArray) actor.get("nodes");
		String id, text, type;
		for (Object jObj : nodeArray) {
			JSONObject intentionalElem = (JSONObject) jObj;
			id = (String) intentionalElem.get("id");
			text = (String) intentionalElem.get("text");
			type = (String) intentionalElem.get("type");
			// System.out.println(id+" "+text+" "+type);
			if (type.equals("istar.Goal")) {
				Goal g = new Goal(id, text);
				ag.putIntentionalElement(g);
				el.put(id, g);
			} else if (type.equals("istar.Task")) {
				Task t = new Task(id, text);
				ag.putIntentionalElement(t);
				el.put(id, t);
			} else if (type.equals("istar.Quality")) {
				Quality q = new Quality(id, text);
				ag.putIntentionalElement(q);
				el.put(id, q);
			} else if (type.equals("istar.Resource")) {
				Resource r = new Resource(id, text);
				ag.putIntentionalElement(r);
				el.put(id, r);
			}

		}
	}
	
	// el grado de satisfacci�n de un modelo, es la suma ponderada del grado de satisfacci�n de sus agentes
	public void generateIntLinProg(String fileName) {
		
		List<List<Double>> a=new LinkedList<List<Double>>();
		List<Double> b=new LinkedList<Double>();
		List<List<Double>> aeq=new LinkedList<List<Double>>();
		List<Double> beq=new LinkedList<Double>();
		HashMap<IStarEntity,Integer> indexMap=new HashMap<IStarEntity,Integer>();
		Integer index=0;
		List<Integer> agentIndex=new LinkedList<Integer>();// �ndice de los agentes
		List<Integer> binaryIndex=new LinkedList<Integer>();
		
		Iterator<String> keyIterator=entityList.keySet().iterator();
		while(keyIterator.hasNext()) {
			String key=keyIterator.next();
			IStarEntity ise=entityList.get(key);	

			if(ise instanceof Agent) {
				// actualizamos el sistema de �ndices.
				//indexMap.put(ise, index);
				//index++;
				
				updateIndexMap((Agent)ise,indexMap);
				agentIndex.add(indexMap.get(ise));
				generateRefinements((Agent)ise,indexMap,a,b,binaryIndex);
				generateContributions((Agent)ise,indexMap,aeq,beq);
				generateAgentConstraint((Agent)ise, aeq, beq, indexMap);
			}
		}
		// completamos con zeros todas las filas de a
		for(int i=0;i<a.size();i++) {
			completeWithZeros(a.get(i),indexMap.size());
		}
		// se genera la funci�n objetivo
		// suma ponderada del nivel de satisfacci�n de cada uno de los agentes.
		// todos los agente tienen el mismo peso.
		List<Double> objectiveFunction=getZeroList(indexMap.size());
		Double weight=(-1d)*(1/agentIndex.size());
		for(int i=0;i<agentIndex.size();i++) {
			objectiveFunction.set(agentIndex.get(i), weight);
		}
		// Se imprime el fichero.
		try {
			PrintWriter pw = new PrintWriter(new FileWriter(fileName+".m"));
			pw.println("% This is a automatically generated file for the iStar model "+modelFileName);
			printObjectiveFunctionIntcon(objectiveFunction, pw);
			// imprimimos A y b
			if(a.size()==0) {
				a.add(getZeroList(indexMap.size()));
				b.add(0d);			
			}
			printABvectors(a, b, pw,"A","b");
			// imprimimos Aeq y Beq
			if(aeq.size()==0) {
				aeq.add(getZeroList(indexMap.size()));
				beq.add(0d);
			}
			printABvectors(aeq, beq, pw,"Aeq","beq");
			// boundings
			pw.println("lb = zeros("+objectiveFunction.size()+",1);");
			String ub="ub = [";
			for(int i=0;i<objectiveFunction.size();i++) {
				if(binaryIndex.contains(i)) {
					ub=ub+"1;";
				}else {
					ub=ub+"100;";
				}
			}
			// se modifica el final de cadena
			ub=ub.substring(0,ub.length()-1)+"];";
			pw.println(ub);
			// llamamos a la funci�n
			pw.println("x = intlinprog(f,intcon,A,b,Aeq,beq,lb,ub);");
			pw.println("% guide to interpret results (intentional_element,index)");
			//HashMap<IntentionalElement,Integer> indexMap=new HashMap<IntentionalElement,Integer>();
			Iterator<IStarEntity> resultsIter=indexMap.keySet().iterator();
			while(resultsIter.hasNext()) {
				IStarEntity iteratorKey=resultsIter.next();
				pw.println("% ("+iteratorKey.getText()+","+indexMap.get(iteratorKey)+")");
			}
			pw.close();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}	
	}
	
	public List<Dependency> getDependencyList(){
		return dependencyList;
	}
	
	// genera la restricci�n que modelo el nivel de satisfacci�n de un agente.
	private void generateAgentConstraint(Agent ag,List<List<Double>> aEq,List<Double> bEq,HashMap<IStarEntity,Integer> indexMap) {
		// se obtienen los elementos ra�ces
		Iterator<String> keyIterator=ag.getWants().keySet().iterator();
		List<IntentionalElement> rootElements=new LinkedList<IntentionalElement>();
		while(keyIterator.hasNext()) {
			IntentionalElement ie=ag.getWants().get(keyIterator.next());
			if(ag.isRootElement(ie.getId())) {
				//System.out.println("Se a�ade el elemento "+ie.getText()+" cuyo �ndice es "+indexMap.get(ie));
				rootElements.add(ie);
			}
		}
		// se genera el peso
		Double weight=-1d/rootElements.size();
		List<Double> aEqRow=getZeroList(indexMap.size());
		aEqRow.set(indexMap.get(ag), 1d);
		for(int i=0;i<rootElements.size();i++) {
			//System.out.println(rootElements.get(i).getText()+":"+indexMap.get(rootElements.get(i)));
			aEqRow.set(indexMap.get(rootElements.get(i)), weight);
		}
		aEq.add(aEqRow);
		bEq.add(0d);
	}
	
	private void printObjectiveFunctionIntcon(List<Double> objFunc,PrintWriter pw) {
		String objFuncString="f = [";
		String intConString="intcon = [";
		for(int i=0;i<objFunc.size();i++) {
			if(objFunc.get(i)!=0) {
				objFuncString=objFuncString+" "+objFunc.get(i)+";";
			}else {
				objFuncString=objFuncString+objFunc.get(i)+";";
			}
			intConString=intConString+(i+1)+",";
		}
		// modificamos el final de la cadena
		objFuncString=objFuncString.substring(0,objFuncString.length()-1)+"];";
		intConString=intConString.substring(0,intConString.length()-1)+"];";
		pw.println(objFuncString);
		pw.println(intConString);
	}
	
	private void generateContributions(Agent ag,HashMap<IStarEntity,Integer> indexMap,List<List<Double>> aEq,
			List<Double> bEq) {

		Iterator<String> keyContIterator=ag.getContributionList().keySet().iterator();
		while(keyContIterator.hasNext()) {
			// inicializamos la lista.
			List<Double> aeqRow=getZeroList(indexMap.size());
			Contribution contribution=ag.getContributionList().get(keyContIterator.next());
			int index=indexMap.get(contribution.getTarget());
			// se pone la ra�z a 1
			aeqRow.set(index,1d);
			// make
			List<IntentionalElement> contList=contribution.getMakeList();
			for(int i=0;i<contList.size();i++) {
				index=indexMap.get(contList.get(i));
				aeqRow.set(index, -1d);
			}
			// help
			contList=contribution.getHelpList();
			for(int i=0;i<contList.size();i++) {
				index=indexMap.get(contList.get(i));
				aeqRow.set(index, -0.75d);
			}
			// hurt
			contList = contribution.getHurtList();
			for (int i = 0; i < contList.size(); i++) {
				index = indexMap.get(contList.get(i));
				aeqRow.set(index, -0.25d);
			}
			// el break es a 0, as� que no lo ponemos aqu�.
			// se a�ade la fila a la lista
			aEq.add(aeqRow);
			bEq.add(0d);
		}
	}
	
	private void updateIndexMap(Agent ag,HashMap<IStarEntity,Integer> indexMap) {
		indexMap.put(ag, indexMap.size());	
		Iterator<IntentionalElement> wantsIterator=ag.getWants().values().iterator();
		while(wantsIterator.hasNext()) {
			IntentionalElement aux=wantsIterator.next();
			indexMap.put(aux, indexMap.size());
			//System.out.println(aux.getText()+":"+indexMap.get(aux));
		}
	}
	
	private void generateRefinements(Agent ag,HashMap<IStarEntity,Integer> indexMap,List<List<Double>> a,
			List<Double> b,List<Integer> binaryIndex) {
		
		Iterator<String> refIterator=ag.getRefinementList().keySet().iterator();
		Double bigM=1000000000000000d;
		
		while(refIterator.hasNext()) {
			// TO-DO: las variables y solo pueden tomar los valores 0 y 1.
			Refinement refToAdd=ag.getRefinementList().get(refIterator.next());
			// se a�ade AND refinement
			if(!refToAdd.getAndRefinements().isEmpty()) {
				List<GoalTaskElement> children=refToAdd.getAndRefinements();
				// esta variable es sustituida en las siguientes restricciones por el alfa
				int x1Index=indexMap.get(children.get(0));
				for(int i=0;i<children.size()-2;i++) {
					IntentionalElement alfa=new IntentionalElement(refToAdd.getParent().getId()+"_alfa_"+i,"alfa");
					IntentionalElement fakeY=new IntentionalElement(refToAdd.getParent().getId()+"_y_"+i,"alfa");
					// se actualiza el map de �ndices
					indexMap.put(alfa, indexMap.size());
					int alfaIndex=indexMap.size()-1;
					indexMap.put(fakeY, indexMap.size());
					binaryIndex.add(indexMap.size()-1);
					int yIndex=indexMap.size()-1;
					int x2Index=indexMap.get(children.get(i+1));
					// generamos las restricciones.
					List<List<Double>> andConstraints=getAndConstraints(alfaIndex, yIndex, x1Index, x2Index, indexMap);
					// se a�aden las aes (la �ltima lista son las b)
					for(int j=0;j<andConstraints.size()-1;j++) {
						a.add(andConstraints.get(j));
					}
					// se a�ade la b
					for(int j=0;j<andConstraints.get(andConstraints.size()-1).size();j++) {
						b.add(andConstraints.get(andConstraints.size()-1).get(j));
					}
					// se asigna alfa al al siguiente x1
					x1Index=alfaIndex;
					
				}
				// se a�aden las restricciones asociadas a la variable real
				IntentionalElement fakeY=new IntentionalElement(refToAdd.getParent().getId()+"_y_last","alfa");
				indexMap.put(fakeY, indexMap.size());
				int yIndex=indexMap.size()-1;
				binaryIndex.add(indexMap.size()-1);
				int xIndex=indexMap.get(refToAdd.getParent());
				int x2Index=indexMap.get(children.get(children.size()-1));
				List<List<Double>> andConstraints=getAndConstraints(xIndex, yIndex, x1Index, x2Index, indexMap);
				// se a�aden las aes (la �ltima lista son las b)
				for(int j=0;j<andConstraints.size()-1;j++) {
					a.add(andConstraints.get(j));
				}
				// se a�ade la b
				for(int j=0;j<andConstraints.get(andConstraints.size()-1).size();j++) {
					b.add(andConstraints.get(andConstraints.size()-1).get(j));
				}			
			// se a�ade OR refinement
			}else{
				List<GoalTaskElement> children=refToAdd.getOrRefinements();
				// esta variable es sustituida en las siguientes restricciones por el alfa
				int x1Index=indexMap.get(children.get(0));
				for(int i=0;i<children.size()-2;i++) {
					IntentionalElement alfa=new IntentionalElement(refToAdd.getParent().getId()+"_alfa_"+i,"alfa_"+i);
					IntentionalElement fakeY=new IntentionalElement(refToAdd.getParent().getId()+"_y_"+i,"y_"+i);
					// se actualiza el map de �ndices
					indexMap.put(alfa, indexMap.size());
					int alfaIndex=indexMap.size()-1;
					indexMap.put(fakeY, indexMap.size());
					binaryIndex.add(indexMap.size()-1);
					int yIndex=indexMap.size()-1;
					int x2Index=indexMap.get(children.get(i+1));
					// generamos las restricciones.
					List<List<Double>> orConstraints=getOrConstraints(alfaIndex, yIndex, x1Index, x2Index, indexMap);
					// se a�aden las aes (la �ltima lista son las b)
					for(int j=0;j<orConstraints.size()-1;j++) {
						a.add(orConstraints.get(j));
					}
					// se a�ade la b
					for(int j=0;j<orConstraints.get(orConstraints.size()-1).size();j++) {
						b.add(orConstraints.get(orConstraints.size()-1).get(j));
					}
					// se asigna alfa al al siguiente x1
					x1Index=alfaIndex;
					
				}
				// se a�aden las restricciones asociadas a la variable real
				IntentionalElement fakeY=new IntentionalElement(refToAdd.getParent().getId()+"_y_last","y_last");
				indexMap.put(fakeY, indexMap.size());
				binaryIndex.add(indexMap.size()-1);
				int yIndex=indexMap.size()-1;
				int xIndex=indexMap.get(refToAdd.getParent());
				int x2Index=indexMap.get(children.get(children.size()-1));
				List<List<Double>> orConstraints=getAndConstraints(xIndex, yIndex, x1Index, x2Index, indexMap);
				// se a�aden las aes (la �ltima lista son las b)
				for(int j=0;j<orConstraints.size()-1;j++) {
					a.add(orConstraints.get(j));
				}
				// se a�ade la b
				for(int j=0;j<orConstraints.get(orConstraints.size()-1).size();j++) {
					b.add(orConstraints.get(orConstraints.size()-1).get(j));
				}			
			}
			
		}
		
	}
	
	
	
	// el grado de satisfacci�n de un agente, es la suma ponderada del grado de satisfacci�n de sus ra�ces.
	public void generateAgentsIntlinProg() {
				
		try {			
			// buscamos en la entityList los elementos que sean agentes.
			Iterator<String> keyIterator=entityList.keySet().iterator();
			String key;
			while(keyIterator.hasNext()) {
				key=keyIterator.next();
				// v0 -> 
				IStarEntity ise=entityList.get(key);
				Random rand=new Random();
				if(ise instanceof Agent) {
					// generate agent script
					String fileName=ise.getText().replace(" ","").replace(".","");
					PrintWriter pw=new PrintWriter(new FileWriter(fileName+".m"));//+"_"+rand.nextInt(1000)+".m"));
					pw.println("% This is a automatically generated file for the iStar model "+modelFileName);
					generateAgentScript(pw,(Agent)ise);
					pw.close();
				}				
			}
			
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}	
	}
	
	// genera un script para el ogente
	private void generateAgentScript(PrintWriter pw,Agent ag) {
		// generaci�n de la funci�n objetivo:
		// debemos encontrar los objetivos ra�z
		// recorremos la lista de elementos intencionales
		
		Iterator<String> keyIterator=ag.getWants().keySet().iterator();
		List<IntentionalElement> rootElements=new LinkedList<IntentionalElement>();
		while(keyIterator.hasNext()) {
			IntentionalElement ie=ag.getWants().get(keyIterator.next());
			if(ag.isRootElement(ie.getId())) {
				rootElements.add(ie);
			}
		}
		//System.out.println("Hemos conseguido "+rootElements.size()+" elementos ra�z.");
		// Funci�n objetivo
		Iterator<IntentionalElement> wantsIterator=ag.getWants().values().iterator();
		Integer index=0;
		// IndexMap es un registro para asignar �ndices a todos los elementos del modelo
		// es de gran importancia para componer las restricciones lineales.
		HashMap<IStarEntity,Integer> indexMap=new HashMap<IStarEntity,Integer>();
		List<Double> objectiveFunction=new LinkedList<Double>();
		Double value=1d/rootElements.size();
		while(wantsIterator.hasNext()) {
			IntentionalElement aux=wantsIterator.next();
			if(rootElements.contains(aux)) {
				objectiveFunction.add(value);
			}else {
				objectiveFunction.add(0d);
			}
			//System.out.println("Se introduce "+aux.getText()+" en la posici�n "+index);
			indexMap.put(aux, index);
			index++;
		}
		// generacion A;b
		List<List<Double>> a=new LinkedList<List<Double>>();
		List<Double> b=new LinkedList<Double>();
		// variables binarias del problema
		List<Integer> binaryVariables=new LinkedList<Integer>();
		generateRefinements(ag, indexMap, a, b, binaryVariables);
		
		// generaci�n de los Aeqs
		List<List<Double>> aeq=new LinkedList<List<Double>>();
		List<Double> beq=new LinkedList<Double>();
		generateContributions(ag, indexMap, aeq, beq);
		
		// completamos con zeros para que todas las listas tengan el mismo tama�o.
		// hemos a�adido variables extra cuando hemos trabajado con los refinements
		// funci�n objetivo
		completeWithZeros(objectiveFunction,indexMap.size());
		// A
		for(int i=0;i<a.size();i++) {
			completeWithZeros(a.get(i),indexMap.size());
		}
		// imprimimos
		// funci�n objetivo e intcon -> maximizamos minimizando la funci�n multiplicada por -1
		// restricci�n intcon, todas las variables son enteras.
		printObjectiveFunctionIntcon(objectiveFunction, pw);
		
		// imprimimos A y b
		if(a.size()==0) {
			a.add(getZeroList(indexMap.size()));
			b.add(0d);			
		}
		printABvectors(a, b, pw,"A","b");
		// imprimimos Aeq y beq
		if(aeq.size()==0) {
			aeq.add(getZeroList(indexMap.size()));
			beq.add(0d);
		}
		printABvectors(aeq, beq, pw,"Aeq","beq");
		// boundings
		pw.println("lb = zeros("+objectiveFunction.size()+",1);");
		String ub="ub = [";
		for(int i=0;i<objectiveFunction.size();i++) {
			if(binaryVariables.contains(i)) {
				ub=ub+"1;";
			}else {
				ub=ub+"100;";
			}
		}
		// se modifica el final de cadena
		ub=ub.substring(0,ub.length()-1)+"];";
		pw.println(ub);
		// llamamos a la funci�n
		pw.println("x = intlinprog(f,intcon,A,b,Aeq,beq,lb,ub);");
		pw.println("% guide to interpret results (intentional_element,index)");
		//HashMap<IntentionalElement,Integer> indexMap=new HashMap<IntentionalElement,Integer>();
		Iterator<IStarEntity> resultsIter=indexMap.keySet().iterator();
		while(resultsIter.hasNext()) {
			IStarEntity iteratorKey=resultsIter.next();
			pw.println("% ("+iteratorKey.getText()+","+indexMap.get(iteratorKey)+")");
		}
		
	}
	
	private void printABvectors(List<List<Double>> a, List<Double> b, PrintWriter pw, String aName, String bName) {
		// inequidades A
		String aString = aName + " = [";
		for (int i = 0; i < a.size(); i++) {
			List<Double> aux = a.get(i);
			for (int j = 0; j < aux.size(); j++) {
				aString = aString + aux.get(j) + ",";
			}
			aString = aString.substring(0, aString.length() - 1) + ";";
		}
		// modificamos el final de la cadena e imprimimo
		aString = aString.substring(0, aString.length() - 1) + "];";
		pw.println(aString);
		// b
		String bString = bName + " = [";
		for (int i = 0; i < b.size(); i++) {
			bString = bString + b.get(i) + ";";
		}
		// moficamos el final de la cadena e imprimimo
		bString = bString.substring(0, bString.length() - 1) + "];";
		pw.println(bString);
	}
	
	private void completeWithZeros(List<Double> list,int size) {
		for(int i=list.size();i<size;i++) {
			list.add(0d);
		}
	}
	
	private List<List<Double>> getAndConstraints(int xIndex,int yIndex,int x1Index,int x2Index,HashMap<IStarEntity,Integer> indexMap){
		List<List<Double>> a=new LinkedList<List<Double>>();
		List<Double> aRow=getZeroList(indexMap.size());
		List<Double> b=new LinkedList<Double>();
		Double bigM=1000000000000000d;
		
		// generamos las restricciones.
		// R1: -x1+x2-My<=0
		aRow.set(x1Index, -1d);
		aRow.set(x2Index, 1d);
		aRow.set(yIndex, bigM*(-1));
		a.add(aRow);
		b.add(0d);
		//R2: x1-x2+My<=M
		aRow=getZeroList(indexMap.size());
		aRow.set(x1Index, 1d);
		aRow.set(x2Index, -1d);
		aRow.set(yIndex, bigM);
		a.add(aRow);
		b.add(bigM);
		// R3: alfa-x1 <=0
		aRow=getZeroList(indexMap.size());
		aRow.set(xIndex, 1d);
		aRow.set(x1Index, -1d);
		a.add(aRow);
		b.add(0d);
		// R4: alfa-x2<=0
		aRow=getZeroList(indexMap.size());
		aRow.set(xIndex, 1d);
		aRow.set(x2Index, -1d);
		a.add(aRow);
		b.add(0d);
		//R5:-alfa+x1+My<=M
		aRow=getZeroList(indexMap.size());
		aRow.set(xIndex, -1d);
		aRow.set(x1Index, 1d);
		aRow.set(yIndex, bigM);
		a.add(aRow);
		b.add(bigM);
		// R6: -alfa+x2-My<=0
		aRow=getZeroList(indexMap.size());
		aRow.set(xIndex, -1d);
		aRow.set(x2Index, 1d);
		aRow.set(yIndex, (-1)*bigM);
		a.add(aRow);
		b.add(0d);
		
		a.add(b);
		return a;
	}
	
	private List<List<Double>> getOrConstraints(int xIndex,int yIndex,int x1Index,int x2Index,HashMap<IStarEntity,Integer> indexMap){
		List<List<Double>> a=new LinkedList<List<Double>>();
		List<Double> aRow=getZeroList(indexMap.size());
		List<Double> b=new LinkedList<Double>();
		Double bigM=1000000000000000d;
		
		// generamos las restricciones.
		// R1: x1-x2-My<=0
		aRow.set(x1Index, 1d);
		aRow.set(x2Index, -1d);
		aRow.set(yIndex, bigM*(-1));
		a.add(aRow);
		b.add(0d);
		//R2: -x1+x2+My<=M
		aRow=getZeroList(indexMap.size());
		aRow.set(x1Index, -1d);
		aRow.set(x2Index, 1d);
		aRow.set(yIndex, bigM);
		a.add(aRow);
		b.add(bigM);
		// R3: -alfa+x1 <=0
		aRow=getZeroList(indexMap.size());
		aRow.set(xIndex, -1d);
		aRow.set(x1Index, 1d);
		a.add(aRow);
		b.add(0d);
		// R4: -alfa+x2<=0
		aRow=getZeroList(indexMap.size());
		aRow.set(xIndex, -1d);
		aRow.set(x2Index, 1d);
		a.add(aRow);
		b.add(0d);
		//R5:alfa-x1-My<=0
		aRow=getZeroList(indexMap.size());
		aRow.set(xIndex, 1d);
		aRow.set(x1Index, -1d);
		aRow.set(yIndex, (-1)*bigM);
		a.add(aRow);
		b.add(0d);
		// R6: alfa-x2+My<=M
		aRow=getZeroList(indexMap.size());
		aRow.set(xIndex, 1d);
		aRow.set(x2Index, -1d);
		aRow.set(yIndex, bigM);
		a.add(aRow);
		b.add(bigM);
		
		a.add(b);
		return a;
	}
	
	private List<Double> getZeroList(int size){
		List<Double> res=new LinkedList<Double>();
		for(int i=0;i<size;i++) {
			res.add(0d);
		}
		return res;
	}
	
	public Actor getIntentionOwner(String target) {
		
		Actor res=null;
		Iterator<String> idActorIterator=actorList.keySet().iterator();
		while(idActorIterator.hasNext()) {
			Actor actor=actorList.get(idActorIterator.next());
			if(actor.hasIntentionalElement(target)) {
				res=actor;
			}
		}
		return res;
		
	}
	
	public IStarEntity getEntity(String id) {
		return entityList.get(id);
	}

}


