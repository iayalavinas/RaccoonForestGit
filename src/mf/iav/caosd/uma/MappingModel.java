package mf.iav.caosd.uma;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import de.vill.model.Feature;
import ilp.iav.caosd.uma.ILPProblem;

public class MappingModel {
	private ILPProblem problem;
	private List<MappingFunction> mappingList = new LinkedList<MappingFunction>();

	public List<MappingFunction> getMappingList() {
		return mappingList;
	}

	public MappingModel(ILPProblem p) {
		problem = p;
	}

	public void translate(String fileName) {
		File mapModelFile = new File(fileName);
		try {
			Scanner myReader = new Scanner(mapModelFile);
			while (myReader.hasNextLine()) {
				String line = myReader.nextLine();
				processLine(line);
			}
			myReader.close();
		} catch (FileNotFoundException e) {
			e.printStackTrace();
		}
	}

	// "intentional element" = w_1*feature_1+w_2*feature_2+....+w_n*feature_n
	// Only correct lines are processed. If it is not correct, they are ignored
	private void processLine(String line) {
		String[] equalityElements = line.split("=");
		if (equalityElements.length == 2) {
			// the origin of the expression should be registered in the problem
			if (problem.isRegistered(equalityElements[0])) {
				MappingFunction mf = new MappingFunction();
				Integer intentionalElementId = problem.getID(equalityElements[0]);
				mf.setEntity(intentionalElementId);
				// obtenemos el resto de las expresiones, si alguna no está registrada, no se
				// añade la función
				String[] weightedFeatures;
				if (equalityElements[1].contains("+")) {
					weightedFeatures = equalityElements[1].split("\\+");
				} else {
					weightedFeatures = new String[1];
					weightedFeatures[0] = equalityElements[1];
				}
				if (weightedFeatures.length >= 1) {
					Boolean error = false;
					int index = 0;
					while (index < weightedFeatures.length && !error) {
						String[] termArray = weightedFeatures[index].split("\\*");
						if (termArray.length != 2) {
							error = true;
							System.err.println("The term " + weightedFeatures[index] + " does not follow the format.");
						} else {
							try {
								Double weight = Double.parseDouble(termArray[0]);
								Feature feature = getFeatureFromName(termArray[1]);
								if (feature != null) {
									Integer termId = problem.getID(feature);
									mf.addFeature(weight, termId);
									// si hemos llegado hasta aquí, añadimos la función.
									//mappingList.add(mf);
								} else {
									List<Feature> clons = getClons(termArray[1]);
									if (clons == null) {
										error = true;
										System.err.println("The term " + termArray[1] + " is not registered.");
									} else {
										// se actualiza el peso dividiéndolo por el número de clones
										weight = weight / clons.size();
										for (int i = 0; i < clons.size(); i++) {
											Integer termId = problem.getID(clons.get(i));
											mf.addFeature(weight, termId);
										}
									}
									
								}
							} catch (NumberFormatException nfe) {
								error = true;
								System.err.println("The  " + termArray[0] + " cannot be cast to a number.");
							}
						}
						index++;
					}
					// añadimos la función de mapeo a la lista.
					if(!error) {
						System.out.println("Se añade "+mf.toString());
						mappingList.add(mf);
					}
				} else {
					System.err.println("The expression " + equalityElements[1] + " does not follow the format.");
				}

			} else {
				System.err.println("Element " + equalityElements[0] + " is not registered in the problem. ");
			}
		} else {
			System.err.println("The line " + line + " does not follow the format.");
		}
	}

	private Feature getFeatureFromName(String featureName) {
		Feature fet = null;
		Object[] problemObjects = problem.getProblemObject();
		Boolean end = false;
		int index = 0;
		if(featureName.startsWith("\"")) {
			featureName=featureName.replaceAll("[\"\r\n]", "");
		}

		while (!end && index < problemObjects.length) {
			if (problemObjects[index] instanceof Feature) {
				Feature candidate = (Feature) problemObjects[index];
				if (candidate.getFeatureName().equals(featureName)) {
					end = true;
					fet = candidate;
				}
			}
			index++;
		}
		return fet;
	}

	// Si la característica es un clon, devuelve la lista de clones, si no devuelve
	// null
	private List<Feature> getClons(String featureName) {
		if(featureName.startsWith("\"")) {
			featureName=featureName.replaceAll("[\"\r\n\t]", "");
			featureName=featureName.trim();
		}
		List<Feature> res = new LinkedList<Feature>();
		Object[] problemObjects = problem.getProblemObject();
		for (int i = 0; i < problemObjects.length; i++) {
			if (problemObjects[i] instanceof Feature) {
				Feature candidate = (Feature) problemObjects[i];
				if (candidate.getFeatureName().startsWith(featureName)) {
					res.add(candidate);
				}
			}
		}
		return (res.size() <= 1 ? null : res);
	}

}
