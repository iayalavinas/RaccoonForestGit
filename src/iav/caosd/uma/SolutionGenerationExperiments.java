package iav.caosd.uma;

import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import de.vill.main.UVLModelFactory;
import de.vill.model.FeatureModel;
import ilp.iav.caosd.uma.ILPProblem;
import istar.iav.caosd.uma.IStarModel;
import mf.iav.caosd.uma.MappingModel;
import tra.iav.caosd.uma.IStarModelTranslator;
import tra.iav.caosd.uma.MappingFunctionTranslator;
import tra.iav.caosd.uma.UVLTranslator;

public class SolutionGenerationExperiments {
	public static void main(String[] args) throws IOException {
		PrintWriter pw = new PrintWriter(new FileWriter("cdl_solution_generation_time.csv"));
		ILPProblem problem;
		IStarModel ism;
		Path filePath;
		UVLModelFactory uvlModelFactory = new UVLModelFactory();
		FeatureModel featureModel;
		UVLTranslator uVLTranslator;
		MappingModel mapModel;
		IStarModelTranslator starTrans;
		Long time_ini, time_fin, time_total;
		//char[] letters= {'a','b','c','d','e','f','g','h','i','j'};

		for (int i = 1; i <=10; i++) {
			// ILP Problem
			System.out.println("Problema "+i);
			problem = new ILPProblem();
			// Goal Model
			ism = new IStarModel();
			ism.parseModel("gm_10.txt");
			starTrans = new IStarModelTranslator(problem, ism);
			starTrans.translate();
			// Feature model
			String fmFile = ".\\cdl\\cdl_" + i + ".uvl";
			filePath = Paths.get(fmFile);
			String content = new String(Files.readAllBytes(filePath));
			uvlModelFactory = new UVLModelFactory();
			featureModel = uvlModelFactory.parse(content);
			uVLTranslator = new UVLTranslator(featureModel, problem, fmFile);
			uVLTranslator.translateModel();
			// Mapping file
			mapModel = new MappingModel(problem);
			mapModel.translate(".\\cdl\\c_"+i+ ".map");
			MappingFunctionTranslator mapTrans = new MappingFunctionTranslator(problem);
			mapTrans.loadConstraints(mapModel.getMappingList());
			// script
			//starTrans.setEveryActorObjectiveFunction();
			//problem.generateIntLinProg("busy_box_problem_" + i);
			String line = "";
			for (int j = 0; j < 10; j++) {
				System.out.println("Repetition "+j);
				String matlabFile=".\\cdl\\cdl_problem_" +i + "-res.txt";
				time_ini = System.currentTimeMillis();
				starTrans.generateLabelledGoalModel(matlabFile, "gm_10.txt",
						".\\cdl\\collored-cdl_gm_" + i + ".txt");
				String featureModelFile = fmFile;
				String uvlConfFile = featureModelFile.substring(0, featureModelFile.length() - 4) + "-conf.json";
				uVLTranslator.writeConfiguration(matlabFile, uvlConfFile);
				time_fin = System.currentTimeMillis();
				time_total = time_fin - time_ini;
				line = line + time_total + ";";
			}
			pw.println(line);

		}
		pw.close();
	}
}
