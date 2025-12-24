package iav.caosd.uma;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import de.vill.main.UVLModelFactory;
import de.vill.model.Feature;
import de.vill.model.FeatureModel;
import ilp.iav.caosd.uma.ILPProblem;
import istar.iav.caosd.uma.IStarModel;
import mf.iav.caosd.uma.MappingModel;
import tra.iav.caosd.uma.IStarModelTranslator;
import tra.iav.caosd.uma.MappingFunctionTranslator;
import tra.iav.caosd.uma.UVLTranslator;

/**
 * This ismain class to run the script generation experiments
 * */

public class ScriptGenerationExperiments {

	public static void main(String[] args) throws IOException {
		ILPProblem problem;
		IStarModel ism;
		Path filePath;
		UVLModelFactory uvlModelFactory = new UVLModelFactory();
		FeatureModel featureModel;
		UVLTranslator uVLTranslator;
		MappingModel mapModel;
		IStarModelTranslator starTrans;
		Long time_ini,time_fin,time_total;
		PrintWriter pw = new PrintWriter(new FileWriter("busy_script_generation_time.csv"));
		//char[] letters= {'a','b','c','d','e','f','g','h','i','j'};
		

		for (int i = 1; i <= 10; i++) {
			System.out.println("Generating problem " +i);
			String line="";
			for (int j = 0; j < 10; j++) {
				System.out.println("Repetition "+j);
				time_ini=System.currentTimeMillis();
				// ILP Problem
				problem = new ILPProblem();
				// Goal Model
				ism = new IStarModel();
				System.out.println("Parsing goal model");
				ism.parseModel("gm_10.txt");
				starTrans = new IStarModelTranslator(problem, ism);
				starTrans.translate();
				// Feature model
				String fmFile=".\\busy\\busy_" + i + ".uvl";
				filePath = Paths.get(fmFile);
				String content = new String(Files.readAllBytes(filePath));
				uvlModelFactory = new UVLModelFactory();
				System.out.println("Parsing feature model");
				featureModel = uvlModelFactory.parse(content);
				uVLTranslator = new UVLTranslator(featureModel, problem,fmFile);
				uVLTranslator.translateModel();
				// Mapping file
				mapModel = new MappingModel(problem);
				mapModel.translate(".\\busy\\b_"+i+ ".map");
				MappingFunctionTranslator mapTrans = new MappingFunctionTranslator(problem);
				mapTrans.loadConstraints(mapModel.getMappingList());
				// script
				starTrans.setEveryActorObjectiveFunction();
				System.out.println("Generating script");
				problem.generateIntLinProg(".\\busy\\busy_problem_" +i);
				time_fin=System.currentTimeMillis();
				time_total=time_fin-time_ini;
				line=line+time_total+";";
			}
			pw.println(line);		
		}
		pw.close();
	}

}
