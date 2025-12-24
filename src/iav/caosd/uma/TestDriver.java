package iav.caosd.uma;

import java.io.IOException;
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

public class TestDriver {

	public static void main(String[] args) throws IOException {
		String goalModelFile="gm_h.txt";
		String featureModelFile="model_h.uvl";
		String mappingeModelFile="h.map";
		String resFile="allAgents-res.txt";
		String filterFile="divercarefilter.fil";
		
		ILPProblem problem = new ILPProblem();
		
		IStarModel ism = new IStarModel();
		ism.parseModel(goalModelFile);
		IStarModelTranslator starTrans = new IStarModelTranslator(problem, ism);
		starTrans.translate();
		
		Path filePath = Paths.get(featureModelFile);
		String content = new String(Files.readAllBytes(filePath));
		UVLModelFactory uvlModelFactory = new UVLModelFactory(); 
		FeatureModel featureModel=uvlModelFactory.parse(content);
		Feature root=featureModel.getRootFeature();
		UVLTranslator uVLTranslator=new UVLTranslator(featureModel,problem,featureModelFile); 
		uVLTranslator.translateModel();
		
		MappingModel mapModel=new MappingModel(problem);
		mapModel.translate(mappingeModelFile);
		MappingFunctionTranslator mapTrans=new MappingFunctionTranslator(problem);
		mapTrans.loadConstraints(mapModel.getMappingList());
		
		String scriptName="allAgents";
		problem.generateIntLinProg(scriptName);
		
		starTrans.generateLabelledGoalModel(resFile,goalModelFile, "collored-"+goalModelFile); 
		uVLTranslator.writeConfiguration(resFile, "model_h-conf.json");
	}

}
