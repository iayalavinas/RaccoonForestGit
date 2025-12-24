package iav.caosd.uma;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import de.vill.main.UVLModelFactory;
import de.vill.model.Feature;
import de.vill.model.FeatureModel;
import ilp.iav.caosd.uma.ILPProblem;
import istar.iav.caosd.uma.Actor;
import istar.iav.caosd.uma.IStarModel;
import mf.iav.caosd.uma.MappingModel;
import tra.iav.caosd.uma.FilterTranslator;
import tra.iav.caosd.uma.IStarModelTranslator;
import tra.iav.caosd.uma.MappingFunctionTranslator;
import tra.iav.caosd.uma.UVLTranslator;

public class Driver {

	public static void main(String[] args) {

		try {
			/*
			 * Path filePath = Paths.get("bike.uvl"); String content = new
			 * String(Files.readAllBytes(filePath)); UVLModelFactory uvlModelFactory = new
			 * UVLModelFactory(); FeatureModel featureModel=uvlModelFactory.parse(content);
			 * Feature root=featureModel.getRootFeature(); ILPProblem problem=new
			 * ILPProblem(); UVLTranslator translator=new UVLTranslator(featureModel,
			 * problem); translator.translateModel(); IStarModel ism=new IStarModel();
			 * ism.parseModel("initialModel.txt"); IStarModelTranslator starTrans=new
			 * IStarModelTranslator(problem, ism); starTrans.translate();
			 */
//			problem.printVariablesIds();
//			problem.printProblem();
			Scanner stdIn = new Scanner(System.in);
			Boolean exit = false;
			do {
				ILPProblem problem = new ILPProblem();
				
				// se carga el modelo de objetivos
				System.out.println("Type the name of your goal model file.");
				String goalModelFile = stdIn.nextLine();
				IStarModel ism = new IStarModel();
				ism.parseModel(goalModelFile);
				IStarModelTranslator starTrans = new IStarModelTranslator(problem, ism);
				starTrans.translate();
				
				// se carga el modelo de variabilidad
				System.out.println("Type the name of your variability model file.");
				String featureModelFile = stdIn.nextLine();
				Path filePath = Paths.get(featureModelFile);
				String content = new String(Files.readAllBytes(filePath));
				UVLModelFactory uvlModelFactory = new UVLModelFactory(); 
				FeatureModel featureModel=uvlModelFactory.parse(content);
				Feature root=featureModel.getRootFeature();
				UVLTranslator uVLTranslator=new UVLTranslator(featureModel,problem,featureModelFile); 
				uVLTranslator.translateModel();
				//problem.printProblem();
				
				// se carga el modelo de mapping
				System.out.println("Type the name of your mapping model file.");
				String mappingeModelFile = stdIn.nextLine();
				MappingModel mapModel=new MappingModel(problem);
				mapModel.translate(mappingeModelFile);
				MappingFunctionTranslator mapTrans=new MappingFunctionTranslator(problem);
				mapTrans.loadConstraints(mapModel.getMappingList());
				
				//se carga el filtro si existe
				System.out.println("Do you have a filter file (yes/no)?");
				String answer = stdIn.nextLine();
				if(answer.equalsIgnoreCase("yes")) {
					System.out.println("Introduce the name of the filter file");
					String filterFile=stdIn.nextLine();
					FilterTranslator filterTrans=new FilterTranslator(problem);
					filterTrans.translate(filterFile);
				}
				
				// seleccionar la función objetivo
				System.out.println("Which kind of objective function do you want to generate for all agents (0) or for just one of them (1)?");
				String option=stdIn.nextLine();
				String scriptName="unknown";
				if(option.equals("0")) {
					starTrans.setEveryActorObjectiveFunction();
					scriptName="allAgents";
					problem.generateIntLinProg(scriptName);
				}else if(option.equals("1")) {
					System.out.println("The model actors are: ");
					HashMap<String,Actor> actorMap=starTrans.getActorMap();
					Iterator<String> actorIterator = actorMap.keySet().iterator();
					int counter=1;
					List<String> actorList=new LinkedList<String>();
					while(actorIterator.hasNext()) {
						String currentKey=actorIterator.next();
						Actor currentActor=actorMap.get(currentKey);
						actorList.add(currentKey);
						System.out.println(counter+" -> "+currentActor.getText());
						counter++;
					}				
					System.out.println("Type the number of the actor that you want to optimize.");
					Integer actorPos=Integer.parseInt(stdIn.nextLine());
					starTrans.setObjectiveFunctionForAgent(actorList.get(actorPos-1));
					scriptName="singleAgent";
					problem.generateIntLinProg(scriptName);
				}else {
					System.out.println("I do not understand your option.");
				}
				
				// generate MatLab problem
				System.out.println("We have generated the script "+scriptName+".m");
				System.out.println("Run the file in matlab and save the generated file in this workspace.");
				System.out.println("Type the name of the generated file.");
				String vectorFile=stdIn.nextLine();
				starTrans.generateLabelledGoalModel(vectorFile,goalModelFile, "collored-"+goalModelFile); 
				//uVLTranslator.writeConfigurationToFile(vectorFile,featureModelFile+".json", featureModelFile);
				String uvlConfFile= featureModelFile.substring(0,featureModelFile.length()-4)+"-conf.json";
				uVLTranslator.writeConfiguration(vectorFile,uvlConfFile);
				System.out.println("We have generated the files "+"collored-"+goalModelFile+" and "+uvlConfFile);
				
				
				System.out.println("Do your want to continue (yes/no)?.");
				String input = stdIn.nextLine();
				exit=input.equalsIgnoreCase("no");
			} while (!exit);
		} catch (IOException e) {
			e.printStackTrace();
		}
	}
	
	

}
