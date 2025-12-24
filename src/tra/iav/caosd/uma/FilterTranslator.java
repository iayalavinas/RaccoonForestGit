package tra.iav.caosd.uma;

import java.io.File;
import java.io.FileNotFoundException;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;

import ctr.iav.caosd.uma.Filter;
import de.vill.model.Feature;
import ilp.iav.caosd.uma.ILPProblem;

public class FilterTranslator {
	private ILPProblem problem;

	public FilterTranslator(ILPProblem p) {
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

	private void processLine(String line) {
		String[] equalityElements = line.split("=");
		if (equalityElements.length == 2) {
			Integer value = null;
			try {
				value = Integer.parseInt(equalityElements[1]);
			} catch (NumberFormatException nfe) {
				System.err.println("The value " + equalityElements[1] + " cannot transformed into a number.");
			}
			if (value != null) {
				if (problem.isRegistered(equalityElements[0])) {
					// es un elemento intencional o es una característica?
					Integer id = problem.getID(equalityElements[0]);
					Filter fil = new Filter(id, value);
					problem.addEqualityConstraint(fil.getLinearConstraint());
				} else {
					// Si no está registrado podría ser una característica o una clonable.
					Feature fea = getFeatureFromName(equalityElements[0]);
					if (fea != null) {
						Integer id=problem.getID(fea);
						Filter fil = new Filter(id, value);
						problem.addEqualityConstraint(fil.getLinearConstraint());
					} else {
						List<Feature> feaList = getClons(equalityElements[0]);
						if (feaList.size() > 0) {
							// tenemos que conseguir los ids de esas clonables
							for (int i = 0; i < feaList.size(); i++) {
								Integer id = problem.getID(feaList.get(i));
								Filter fil = new Filter(id, value);
								problem.addEqualityConstraint(fil.getLinearConstraint());
							}
						} else {
							System.err.println("Element " + equalityElements[0] + " is not registered in the problem.");
						}
					}
				}
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
		if (featureName.startsWith("\"")) {
			featureName = featureName.replaceAll("[\"\r\n]", "");
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
		if (featureName.startsWith("\"")) {
			featureName = featureName.replaceAll("[\"\r\n\t]", "");
			featureName = featureName.trim();
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
