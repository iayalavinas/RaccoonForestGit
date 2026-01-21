package tra.iav.caosd.uma;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Random;

import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;
import org.logicng.transformations.cnf.TseitinTransformation;

import de.vill.model.Feature;
import de.vill.model.FeatureModel;
import de.vill.model.FeatureType;
import de.vill.model.Group;
import de.vill.model.Group.GroupType;
import de.vill.model.constraint.AndConstraint;
import de.vill.model.constraint.Constraint;
import de.vill.model.constraint.EqualEquationConstraint;
import de.vill.model.constraint.EquivalenceConstraint;
import de.vill.model.constraint.ExpressionConstraint;
import de.vill.model.constraint.GreaterEqualsEquationConstraint;
import de.vill.model.constraint.GreaterEquationConstraint;
import de.vill.model.constraint.ImplicationConstraint;
import de.vill.model.constraint.LiteralConstraint;
import de.vill.model.constraint.LowerEqualsEquationConstraint;
import de.vill.model.constraint.LowerEquationConstraint;
import de.vill.model.constraint.NotConstraint;
import de.vill.model.constraint.NotEqualsEquationConstraint;
import de.vill.model.constraint.OrConstraint;
import de.vill.model.constraint.ParenthesisConstraint;
import de.vill.model.expression.Expression;
import de.vill.model.expression.LiteralExpression;
import de.vill.model.expression.NumberExpression;
import ilp.iav.caosd.uma.Comparator;
import ilp.iav.caosd.uma.ILPProblem;
import ilp.iav.caosd.uma.LinearConstraint;
import ilp.iav.caosd.uma.Term;

public class UVLTranslator {

	private List<String> ignoreList = new ArrayList<String>(
			Arrays.asList("mandatory", "or", "alternative", "features", "optional", ""));
	private FeatureModel model;
	private ILPProblem problem;
	private String featureModelFile;
	private Double bigM = 1000000000000000d;
	private List<Constraint> temporalConstraintList = new LinkedList<Constraint>();
	// Estructura que almacena el identificador (nombre) que se le ha asignado a una
	// característica clonada.
	private HashMap<String, Feature> clonedFeatureRegistry = new HashMap<String, Feature>();
	// Estructura que guarda la corresponencia entre un clon y la característica de
	// la que ha sido clonado.
	private HashMap<Feature, Feature> clonAndClonableRegistry = new HashMap<Feature, Feature>();
	// Estructura que guarda una característica clonable y todos sus clones.
	private HashMap<Feature, List<Feature>> clonableAndClonListRegistry = new HashMap<Feature, List<Feature>>();

	public UVLTranslator(FeatureModel m, ILPProblem i, String file) {
		model = m;
		problem = i;
		featureModelFile = file;
	}
	
	public ILPProblem getProblem() {
		return problem;
	}

	private Boolean isClon(Feature fea) {
		return clonAndClonableRegistry.containsKey(fea);
	}

	// convierte el modelo en una serie de restricciones lineales.
	public void translateModel() {

		List<Feature> featureList = new LinkedList<Feature>();
		int index;

		featureList.add(model.getRootFeature());

		getFeatures(model.getRootFeature(), featureList);

		// se añaden las características
		System.out.println("Trasnlating features...");
		for (int i = 0; i < featureList.size(); i++) {
			// se añade la característica raíz
			if (model.getRootFeature().equals(featureList.get(i))) {
				// se obtiene su índice y se añade si es necesiario.
				index = problem.getIndex(featureList.get(i));
				List<Term> listTerm = new LinkedList<Term>();
				// hay que poner esa constraint a 1 de manera obligatoria
				listTerm.add(new Term(1d, index));
				problem.addEqualityConstraint(new LinearConstraint(listTerm, 1, Comparator.Equal));
			}
			// las clonables o descendientes de clonables se ignoran porque ya han sido
			// añadidas como hijas de otra características.
			if (isClonable(featureList.get(i))) {
				Feature clonable = featureList.get(i);
				List<Feature> clonList;
				// ¿Está registrada en el problema?
				if (!clonableAndClonListRegistry.containsKey(featureList.get(i))) {
					Integer upperBound = Integer.parseInt(featureList.get(i).getUpperBound());
					clonList = new LinkedList<Feature>();
					// se registran los clones en la estructura.
					for (int k = 1; k <= upperBound; k++) {
						// se crea una característica clonada
						Feature clonedFeature = clonable.clone();
						clonedFeature.setFeatureName(clonable.getFeatureName() + "_" + k);
						// se añade a la lista
						clonList.add(clonedFeature);
						clonAndClonableRegistry.put(clonedFeature, clonable);
						// se registra en el problema, si no ha sido registrado ya.
						index = problem.getIndex(clonedFeature);
						if (isNumerical(clonedFeature)) {
							addBoundingConstraints(index, clonedFeature);
						} else {
							problem.addBoundingConstraint(index, 0, 1);
						}
					}
					// se registra en la estructura
					clonableAndClonListRegistry.put(clonable, clonList);
				} else {
					clonList = clonableAndClonListRegistry.get(featureList.get(i));
				}
				if (clonable.getChildren().size() > 0) {
					// clonamos la rama.
					// clonable, clon
					for (int k = 0; k < clonList.size(); k++) {
						addClonedBranch(clonable, clonList.get(k));
					}
				}
			} else if (!isClonable(featureList.get(i)) && !hasClonableAncestor(featureList.get(i))) {
				index = problem.getIndex(featureList.get(i));
				// es numerica
				if (isNumerical(featureList.get(i))) {
					addBoundingConstraints(index, featureList.get(i));
				} else {
					problem.addBoundingConstraint(index, 0, 1);
				}
				// paternity
				addIndependentChildren(featureList.get(i), index);
				// mandatory features
				addMandatoryChildren(featureList.get(i));
				addGroups(featureList.get(i));
			}
		}
		// traducción de crostree constraints
		temporalConstraintList.addAll(model.getConstraints());
		// replace clonables with clons
		replaceClonables();
		// se transforma en CNF
		System.out.println("Trasnlating constraints...");
		/*
		 * transformInCNF();
		 * 
		 * System.out.println("Transform in linear constraints..."); // pasamos las
		 * restricciones al modelo transformInLinearConstraints();
		 */
		transformInLCwithLogicNG();
	}

	private void transformInLCwithLogicNG() {
		Formula temp, transformed;
		FormulaFactory f = new FormulaFactory();
		TseitinTransformation tseitinTrans = new TseitinTransformation();
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof ExpressionConstraint) {
				// TO-DO: Transforamcion de expression constraint entre características a
				// expresión lineal
				// transformExpressionConstraint((ExpressionConstraint)temporalConstraintList.get(i));
			} else {
				// System.out.println("Antes: "+temporalConstraintList.get(i));
				temp = translateFormula(temporalConstraintList.get(i), f);
				transformed = temp.transform(tseitinTrans);
				// System.out.println("Despues: "+transformed);
				// el resultado es una conjunción de OR
				// debemos obtener todas las conjunciones y meterlas una a una.
				transformInLC(transformed.toString());
			}
		}

	}

	private void transformInLC(String formula) {
		int numNegatives = 0;
		String varId;
		Feature fea;
		int index;
		Boolean neg = false;
		LinearConstraint linearCons;

		String[] disjunc = formula.split("&");

		// cada una de las disyunciones es una linear constraint
		for (int i = 0; i < disjunc.length; i++) {

			disjunc[i] = disjunc[i].trim();
			if (disjunc[i].startsWith("("))
				disjunc[i] = disjunc[i].substring(1, disjunc[i].length() - 1);
			// System.out.println("Se procesa "+disjunc[i]);
			String[] vars = disjunc[i].split("\\|");
			// System.out.println("Vamos a examinar "+vars.length);
			List<Term> termList = new LinkedList<Term>();

			for (int j = 0; j < vars.length; j++) {
				// System.out.println("Termino "+vars[j]);
				vars[j] = vars[j].trim();
				// variable negada
				if (vars[j].startsWith("~")) {
					numNegatives++;
					varId = vars[j].substring(1);
				} else {
					varId = vars[j];
					neg = true;
				}
				fea = getFeatureFromString(varId);
				if (fea != null) {
					index = problem.getIndex(fea);
				} else {
					LiteralConstraint litCons = new LiteralConstraint(varId);
					index = getIndexFromLiteralConstraint(litCons);
				}
				if (neg) {
					termList.add(new Term(-1d, index));
				} else {
					termList.add(new Term(1d, index));
				}
				neg = false;
			}
			linearCons = new LinearConstraint(termList, -1 + numNegatives, Comparator.LowerOrEqual);
			// System.out.println("Restricción resultante "+linearCons.toString());
			problem.addConstraint(linearCons);
			numNegatives = 0;
		}
	}

	private Formula translateFormula(Constraint cons, FormulaFactory factory) {
		Formula res = null;
		if (cons instanceof AndConstraint) {
			AndConstraint and = (AndConstraint) cons;
			res = factory.and(translateFormula(and.getLeft(), factory), translateFormula(and.getRight(), factory));
		} else if (cons instanceof EquivalenceConstraint) {
			EquivalenceConstraint equi = (EquivalenceConstraint) cons;
			res = factory.equivalence(translateFormula(equi.getLeft(), factory),
					translateFormula(equi.getRight(), factory));
		} else if (cons instanceof ImplicationConstraint) {
			ImplicationConstraint imp = (ImplicationConstraint) cons;
			res = factory.implication(translateFormula(imp.getLeft(), factory),
					translateFormula(imp.getRight(), factory));
		} else if (cons instanceof LiteralConstraint) {
			LiteralConstraint lit = (LiteralConstraint) cons;
			// por ahora se dejaría así.
			res = factory.variable(lit.getFeature().getFeatureName());
		} else if (cons instanceof NotConstraint) {
			NotConstraint not = (NotConstraint) cons;
			res = factory.not(translateFormula(not.getContent(), factory));
		} else if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			res = factory.or(translateFormula(orCons.getLeft(), factory), translateFormula(orCons.getRight(), factory));
		} else if (cons instanceof ParenthesisConstraint) {
			ParenthesisConstraint par = (ParenthesisConstraint) cons;
			res = translateFormula(par.getContent(), factory);
		}
		return res;
	}

	private void transformInLinearConstraints() {
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof ExpressionConstraint) {
				// TO-DO: Transforamcion de expression constraint entre características a
				// expresión lineal
				// transformExpressionConstraint((ExpressionConstraint)temporalConstraintList.get(i));
			} else {
				List<Term> termList = new LinkedList<Term>();
				transformInLinearConstraints(temporalConstraintList.get(i), termList);
				Integer acum = numberOfPostiveTerms(termList);
				LinearConstraint lc = new LinearConstraint(termList, -1 + acum, Comparator.LowerOrEqual);
				problem.addConstraint(lc);
			}
		}
	}

	private int numberOfPostiveTerms(List<Term> list) {
		int res = 0;
		for (int i = 0; i < list.size(); i++) {
			Term term = list.get(i);
			if (term.getWeight() > 0) {
				res++;
			}
		}
		return res;
	}

	private void transformInLinearConstraints(Constraint cons, List<Term> termList) {

		if (cons instanceof LiteralConstraint) {
			// se obtiene el indice del líteral
			LiteralConstraint lit = (LiteralConstraint) cons;
			// puede ser una fake constraint
			int index = (lit.getFeature() != null ? problem.getIndex(lit.getFeature())
					: problem.getIndex(lit.getLiteral()));
			termList.add(new Term(-1d, index));
		} else if (cons instanceof NotConstraint) {
			NotConstraint notCons = (NotConstraint) cons;
			if (notCons.getContent() instanceof LiteralConstraint) {
				// se obtiene el indice del líteral
				LiteralConstraint lit = (LiteralConstraint) notCons.getContent();
				// puede ser una fake constraint
				int index = (lit.getFeature() != null ? problem.getIndex(lit.getFeature())
						: problem.getIndex(lit.getLiteral()));
				termList.add(new Term(1d, index));
			}
		} else if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof LiteralConstraint) {
				LiteralConstraint litCons = (LiteralConstraint) orCons.getLeft();
				// puede ser una fake constraint
				int index = (litCons.getFeature() != null ? problem.getIndex(litCons.getFeature())
						: problem.getIndex(litCons.getLiteral()));
				termList.add(new Term(-1d, index));
			} else if (orCons.getLeft() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) orCons.getLeft();
				if (notCons.getContent() instanceof LiteralConstraint) {
					// se obtiene el indice del líteral
					LiteralConstraint lit = (LiteralConstraint) notCons.getContent();
					// puede ser una fake constraint
					int index = (lit.getFeature() != null ? problem.getIndex(lit.getFeature())
							: problem.getIndex(lit.getLiteral()));
					termList.add(new Term(1d, index));
				}
			} else if (orCons.getLeft() instanceof OrConstraint) {
				OrConstraint intOrCons = (OrConstraint) orCons.getLeft();
				transformInLinearConstraints(intOrCons, termList);
			}
			if (orCons.getRight() instanceof LiteralConstraint) {
				LiteralConstraint litCons = (LiteralConstraint) orCons.getRight();
				// puede ser una fake constraint
				int index = (litCons.getFeature() != null ? problem.getIndex(litCons.getFeature())
						: problem.getIndex(litCons.getLiteral()));
				termList.add(new Term(-1d, index));
			} else if (orCons.getRight() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) orCons.getRight();
				if (notCons.getContent() instanceof LiteralConstraint) {
					// se obtiene el indice del líteral
					LiteralConstraint lit = (LiteralConstraint) notCons.getContent();
					// puede ser una fake constraint
					int index = (lit.getFeature() != null ? problem.getIndex(lit.getFeature())
							: problem.getIndex(lit.getLiteral()));
					termList.add(new Term(1d, index));
				}
			} else if (orCons.getRight() instanceof OrConstraint) {
				OrConstraint intOrCons = (OrConstraint) orCons.getRight();
				transformInLinearConstraints(intOrCons, termList);
			}

		}

	}

	private Boolean existClonable(Constraint cons) {
		Boolean res = false;
		if (cons instanceof LiteralConstraint) {
			LiteralConstraint lit = (LiteralConstraint) cons;
			if (!isClon(lit.getFeature()) && (isClonable(lit.getFeature()) || hasClonableAncestor(lit.getFeature()))) {
				res = true;
			}
		} else if (cons instanceof NotConstraint) {
			res = existClonable(((NotConstraint) cons).getContent());
		} else if (cons instanceof ParenthesisConstraint) {
			res = existClonable(((ParenthesisConstraint) cons).getContent());
		} else if (cons instanceof AndConstraint) {
			AndConstraint and = (AndConstraint) cons;
			res = existClonable(and.getLeft());
			if (!res) {
				res = existClonable(and.getRight());
			}
		} else if (cons instanceof OrConstraint) {
			OrConstraint orC = (OrConstraint) cons;
			res = existClonable(orC.getLeft());
			if (!res) {
				res = existClonable(orC.getRight());
			}
		} else if (cons instanceof ImplicationConstraint) {
			ImplicationConstraint imp = (ImplicationConstraint) cons;
			res = existClonable(imp.getLeft());
			if (!res) {
				res = existClonable(imp.getRight());
			}
		}
		return res;
	}

	private Boolean existClonable() {
		Boolean res = false;
		int index = 0;

		while (!res && index < temporalConstraintList.size()) {
			if (temporalConstraintList.get(index) instanceof LiteralConstraint) {
				LiteralConstraint lit = (LiteralConstraint) temporalConstraintList.get(index);
				if (!isClon(lit.getFeature())
						&& (isClonable(lit.getFeature()) || hasClonableAncestor(lit.getFeature()))) {
					res = true;
				}
			} else {
				res = existClonable(temporalConstraintList.get(index));
			}
			index++;
		}
		return res;
	}

	private void removeClonable(Constraint cons, LiteralConstraint lit) {
		if (!isClon(lit.getFeature()) && (isClonable(lit.getFeature()) || hasClonableAncestor(lit.getFeature()))) {
			OrConstraint aux = generateClonDisjunction(lit.getFeature());
			cons.replaceConstraintSubPart(lit, aux);
		}
	}

	private void removeClonable(Constraint cons) {
		if (cons instanceof NotConstraint) {
			NotConstraint notCons = (NotConstraint) cons;
			if (notCons.getContent() instanceof LiteralConstraint) {
				removeClonable(notCons, (LiteralConstraint) notCons.getContent());
			} else {
				removeClonable(notCons.getContent());
			}
		} else if (cons instanceof ParenthesisConstraint) {
			ParenthesisConstraint parCons = (ParenthesisConstraint) cons;
			if (parCons.getContent() instanceof LiteralConstraint) {
				removeClonable(parCons, (LiteralConstraint) parCons.getContent());
			} else {
				removeClonable(parCons.getContent());
			}
		} else if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof LiteralConstraint) {
				removeClonable(orCons, (LiteralConstraint) orCons.getLeft());
			} else {
				removeClonable(orCons.getLeft());
			}
			if (orCons.getRight() instanceof LiteralConstraint) {
				removeClonable(orCons, (LiteralConstraint) orCons.getRight());
			} else {
				removeClonable(orCons.getRight());
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof LiteralConstraint) {
				removeClonable(andCons, (LiteralConstraint) andCons.getLeft());
			} else {
				removeClonable(andCons.getLeft());
			}
			if (andCons.getRight() instanceof LiteralConstraint) {
				removeClonable(andCons, (LiteralConstraint) andCons.getRight());
			} else {
				removeClonable(andCons.getRight());
			}
		} else if (cons instanceof ImplicationConstraint) {
			ImplicationConstraint impCons = (ImplicationConstraint) cons;
			if (impCons.getLeft() instanceof LiteralConstraint) {
				removeClonable(impCons, (LiteralConstraint) impCons.getLeft());
			} else {
				removeClonable(impCons.getLeft());
			}
			if (impCons.getRight() instanceof LiteralConstraint) {
				removeClonable(impCons, (LiteralConstraint) impCons.getRight());
			} else {
				removeClonable(impCons.getRight());
			}
		}
	}

	private void replaceClonable() {
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof LiteralConstraint) {
				LiteralConstraint lit = (LiteralConstraint) temporalConstraintList.get(i);
				if (!isClon(lit.getFeature())
						&& (isClonable(lit.getFeature()) || hasClonableAncestor(lit.getFeature()))) {
					OrConstraint aux = generateClonDisjunction(lit.getFeature());
					temporalConstraintList.set(i, aux);
				}
			} else {
				removeClonable(temporalConstraintList.get(i));
			}
		}
	}

	private void replaceClonables() {
		while (existClonable()) {
			replaceClonable();

		}
	}

	private void transformInCNF() {
		// iteramos en el modelo hasta que quitamos los paréntesis
		while (existParenthesis()) {
			removeParenthesis();
		}

		// iteramos en el modelos hasta que sustituimos todas las expresiones
		// aritméticas por variables
		// TO-DO: ¿Cómo sacamos al aritmética de la expresión lógica?

		// aplicamos el algoritmo de la CNF
		// 1. Eliminar todas las implicaciones usando A->B = !A||B y
		// A<->B=(A->B)&&(B->A)
		// System.out.println("Se eliminan los equivalence constraints.");
		while (existEquivalenceConstraint()) {
			removeEquivalenceConstraint();
		}

		// System.out.println("Se eliminan las implicaciones");
		while (existImpicationContraint()) {
			removeImplicationConstraint();
		}

		// 2.Trasladar negaciones aplicando las leyes de Morgan
		// System.out.println("Se aplican las leyes de Morgan");
		while (existNotAndNotOr()) {
			removeNotAnd();
			removeNotOr();
		}

		// 3. Eliminar negaciones dobles
		// System.out.println("Se quitan las negaciones dobles.");
		while (existDoubleNegation()) {
			removeDoubleNegation();
		}

		// 4. Aplicar la ley distributiva
		// System.out.println("Se aplica la ley distributiva");
		while (existDistributableExpression()) {
			applyDistributiveProperty();
		}

		// 5. Partir las expresiones usando los AND
		// System.out.println("Se parten las expresiones usando AND");
		while (existAnd()) {
			splitAndConstraint();
		}

	}

	private void printConstraints() {
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			System.out.println(temporalConstraintList.get(i));
		}
	}

	private void applyDistributiveProperty(OrConstraint orCons, Constraint cons) {

		AndConstraint andCons = (orCons.getLeft() instanceof AndConstraint ? (AndConstraint) orCons.getLeft()
				: (AndConstraint) orCons.getRight());
		if ((orCons.getLeft() instanceof LiteralConstraint) || (orCons.getRight() instanceof LiteralConstraint)) {
			LiteralConstraint litCons = (orCons.getLeft() instanceof LiteralConstraint
					? (LiteralConstraint) orCons.getLeft()
					: (LiteralConstraint) orCons.getRight());
			OrConstraint orCons1 = new OrConstraint(litCons, andCons.getLeft());
			OrConstraint orCons2 = new OrConstraint(litCons, andCons.getRight());
			AndConstraint newAndCons = new AndConstraint(orCons1, orCons2);
			cons.replaceConstraintSubPart(orCons, newAndCons);
		} else {
			NotConstraint notCons = (orCons.getLeft() instanceof NotConstraint ? (NotConstraint) orCons.getLeft()
					: (NotConstraint) orCons.getRight());
			OrConstraint orCons1 = new OrConstraint(notCons, andCons.getLeft());
			OrConstraint orCons2 = new OrConstraint(notCons, andCons.getRight());
			AndConstraint newAndCons = new AndConstraint(orCons1, orCons2);
			cons.replaceConstraintSubPart(orCons, newAndCons);
		}
	}

	// estoy rehaciendo este método.
	private void applyDistributiveProperty(Constraint cons) {

		if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof OrConstraint) {
				if (isDistributable((OrConstraint) orCons.getLeft())) {
					applyDistributiveProperty((OrConstraint) orCons.getLeft(), orCons);
				} else {
					applyDistributiveProperty(orCons.getLeft());
				}
			} else {
				applyDistributiveProperty(orCons.getLeft());
			}
			if (orCons.getRight() instanceof OrConstraint) {
				if (isDistributable((OrConstraint) orCons.getRight())) {
					applyDistributiveProperty((OrConstraint) orCons.getRight(), orCons);
				} else {
					applyDistributiveProperty(orCons.getRight());
				}
			} else {
				applyDistributiveProperty(orCons.getRight());
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof OrConstraint) {
				if (isDistributable((OrConstraint) andCons.getLeft())) {
					applyDistributiveProperty((OrConstraint) andCons.getLeft(), andCons);
				} else {
					applyDistributiveProperty(andCons.getLeft());
				}
			} else {
				applyDistributiveProperty(andCons.getLeft());
			}
			if (andCons.getRight() instanceof OrConstraint) {
				if (isDistributable((OrConstraint) andCons.getRight())) {
					applyDistributiveProperty((OrConstraint) andCons.getRight(), andCons);
				} else {
					applyDistributiveProperty(andCons.getRight());
				}
			} else {
				applyDistributiveProperty(andCons.getRight());
			}
		}

	}

	private void applyDistributiveProperty() {
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof OrConstraint) {
				OrConstraint orCons = (OrConstraint) temporalConstraintList.get(i);
				if (isDistributable(orCons)) {
					AndConstraint andCons = (orCons.getLeft() instanceof AndConstraint
							? (AndConstraint) orCons.getLeft()
							: (AndConstraint) orCons.getRight());
					if ((orCons.getLeft() instanceof LiteralConstraint)
							|| (orCons.getRight() instanceof LiteralConstraint)) {
						LiteralConstraint litCons = (orCons.getLeft() instanceof LiteralConstraint
								? (LiteralConstraint) orCons.getLeft()
								: (LiteralConstraint) orCons.getRight());

						OrConstraint orCons1 = new OrConstraint(litCons, andCons.getLeft());
						OrConstraint orCons2 = new OrConstraint(litCons, andCons.getRight());
						AndConstraint newAndCons = new AndConstraint(orCons1, orCons2);
						temporalConstraintList.set(i, newAndCons);
					} else {
						NotConstraint notCons = (orCons.getLeft() instanceof NotConstraint
								? (NotConstraint) orCons.getLeft()
								: (NotConstraint) orCons.getRight());
						OrConstraint orCons1 = new OrConstraint(notCons, andCons.getLeft());
						OrConstraint orCons2 = new OrConstraint(notCons, andCons.getRight());
						AndConstraint newAndCons = new AndConstraint(orCons1, orCons2);
						temporalConstraintList.set(i, newAndCons);
					}

				} else {
					applyDistributiveProperty(temporalConstraintList.get(i));
				}
			} else {
				applyDistributiveProperty(temporalConstraintList.get(i));
			}
		}
	}

	private Boolean isDistributable(OrConstraint cons) {
		Boolean res = (((cons.getLeft() instanceof LiteralConstraint) || isNotLiteral(cons.getLeft()))
				&& (cons.getRight() instanceof AndConstraint))

				|| (((cons.getRight() instanceof LiteralConstraint) || (isNotLiteral(cons.getRight())))
						&& (cons.getLeft() instanceof AndConstraint));

		return res;
	}

	private Boolean isNotLiteral(Constraint cons) {
		Boolean res = false;
		if (cons instanceof NotConstraint) {
			res = ((NotConstraint) cons).getContent() instanceof LiteralConstraint;
		}
		return res;

	}

	private Boolean existDistributableExpression(Constraint cons) {
		Boolean res = false;

		if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			res = isDistributable(orCons);
			if (!res) {
				res = (existDistributableExpression(orCons.getLeft()))
						|| (existDistributableExpression(orCons.getRight()));
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andConstraint = (AndConstraint) cons;
			res = (existDistributableExpression(andConstraint.getLeft()))
					|| (existDistributableExpression(andConstraint.getRight()));
		}
		return res;
	}

	private Boolean existDistributableExpression() {
		Boolean res = false;
		int index = 0;
		while (!res && index < temporalConstraintList.size()) {
			if (temporalConstraintList.get(index) instanceof OrConstraint) {
				OrConstraint orCons = (OrConstraint) temporalConstraintList.get(index);
				res = isDistributable(orCons);
			} else {
				res = existDistributableExpression(temporalConstraintList.get(index));
			}
			/*
			 * if (res) System.out.println(temporalConstraintList.get(index));
			 */
			index++;
		}

		return res;
	}

	private void splitAndConstraint() {
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof AndConstraint) {
				AndConstraint andCons = (AndConstraint) temporalConstraintList.get(i);
				temporalConstraintList.set(i, andCons.getLeft());
				temporalConstraintList.add(andCons.getRight());
			} else {

			}
		}

	}

	private Boolean existAnd(Constraint cons) {
		Boolean res = false;

		if (cons instanceof AndConstraint) {
			res = true;
		} else if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			res = (orCons.getLeft() instanceof AndConstraint) || (orCons.getRight() instanceof AndConstraint);
			if (!res) {
				res = existAnd(orCons.getLeft()) || existAnd(orCons.getRight());
			}
		}
		return res;
	}

	private Boolean existAnd() {
		Boolean res = false;
		int index = 0;

		while (!res && index < temporalConstraintList.size()) {
			if (temporalConstraintList.get(index) instanceof AndConstraint) {
				// System.out.println("And de nivel superior detectado.");
				res = true;
			} else {
				res = existAnd(temporalConstraintList.get(index));
			}
			index++;
		}

		return res;
	}

	private void removeDoubleNegation() {

		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof NotConstraint) {
				NotConstraint extNotConst = (NotConstraint) temporalConstraintList.get(i);
				if (extNotConst.getContent() instanceof NotConstraint) {
					NotConstraint intNotCons = (NotConstraint) extNotConst.getContent();
					temporalConstraintList.set(i, intNotCons.getContent());
				}
			} else {
				removeDoubleNegation(temporalConstraintList.get(i));
			}
		}
	}

	private void removeDoubleNegation(Constraint cons) {
		if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof NotConstraint) {
				NotConstraint extNotCons = (NotConstraint) orCons.getLeft();
				if (extNotCons.getContent() instanceof NotConstraint) {
					NotConstraint intNotCons = (NotConstraint) extNotCons.getContent();
					cons.replaceConstraintSubPart(orCons.getLeft(), intNotCons.getContent());
				}
			} else {
				removeDoubleNegation(orCons.getLeft());
			}
			if (orCons.getRight() instanceof NotConstraint) {
				NotConstraint extNotCons = (NotConstraint) orCons.getRight();
				if (extNotCons.getContent() instanceof NotConstraint) {
					NotConstraint intNotCons = (NotConstraint) extNotCons.getContent();
					cons.replaceConstraintSubPart(orCons.getRight(), intNotCons.getContent());
				}
			} else {
				removeDoubleNegation(orCons.getRight());
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof NotConstraint) {
				NotConstraint extNotCons = (NotConstraint) andCons.getLeft();
				if (extNotCons.getContent() instanceof NotConstraint) {
					NotConstraint intNotCons = (NotConstraint) extNotCons.getContent();
					cons.replaceConstraintSubPart(andCons.getLeft(), intNotCons.getContent());
				}
			} else {
				removeDoubleNegation(andCons.getLeft());
			}
			if (andCons.getRight() instanceof NotConstraint) {
				NotConstraint extNotCons = (NotConstraint) andCons.getRight();
				if (extNotCons.getContent() instanceof NotConstraint) {
					NotConstraint intNotCons = (NotConstraint) extNotCons.getContent();
					cons.replaceConstraintSubPart(andCons.getRight(), intNotCons.getContent());
				}
			} else {
				removeDoubleNegation(andCons.getRight());
			}
		}
	}

	private Boolean existDoubleNegation() {
		Boolean res = false;
		int index = 0;

		while (!res && index < temporalConstraintList.size()) {
			if (temporalConstraintList.get(index) instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) temporalConstraintList.get(index);
				res = notCons.getContent() instanceof NotConstraint;
			} else {
				// dig deeper
				res = existDoubleNegation(temporalConstraintList.get(index));
			}
			index++;
		}
		return res;
	}

	private Boolean existDoubleNegation(Constraint cons) {
		Boolean res = false;

		if (cons instanceof NotConstraint) {
			NotConstraint notCons = (NotConstraint) cons;
			res = (notCons.getContent() instanceof NotConstraint);
		} else if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof NotConstraint) {
				NotConstraint notAux = (NotConstraint) orCons.getLeft();
				res = (notAux.getContent() instanceof NotConstraint);
			} else {
				res = existDoubleNegation(orCons.getLeft());
			}
			if (!res) {
				if (orCons.getRight() instanceof NotConstraint) {
					NotConstraint notAux = (NotConstraint) orCons.getRight();
					res = (notAux.getContent() instanceof NotConstraint);
				} else {
					res = existDoubleNegation(orCons.getRight());
				}
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof NotConstraint) {
				NotConstraint notAux = (NotConstraint) andCons.getLeft();
				res = (notAux.getContent() instanceof NotConstraint);
			} else {
				res = existDoubleNegation(andCons.getLeft());
			}
			if (!res) {
				if (andCons.getRight() instanceof NotConstraint) {
					NotConstraint notAux = (NotConstraint) andCons.getRight();
					res = (notAux.getContent() instanceof NotConstraint);
				} else {
					res = existDoubleNegation(andCons.getRight());
				}
			}
		}
		return res;
	}

	private void removeNotAnd() {
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) temporalConstraintList.get(i);
				if (notCons.getContent() instanceof AndConstraint) {
					AndConstraint andCons = (AndConstraint) notCons.getContent();
					OrConstraint orCons = new OrConstraint(new NotConstraint(andCons.getLeft()),
							new NotConstraint(andCons.getRight()));
					temporalConstraintList.set(i, orCons);
				}
			} else {
				removeNotAnd(temporalConstraintList.get(i));
			}
		}
	}

	private void removeNotAnd(Constraint cons) {
		if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) orCons.getLeft();
				if (notCons.getContent() instanceof AndConstraint) {
					AndConstraint andCons = (AndConstraint) notCons.getContent();
					OrConstraint auxOrCons = new OrConstraint(new NotConstraint(andCons.getLeft()),
							new NotConstraint(andCons.getRight()));
					cons.replaceConstraintSubPart(notCons, auxOrCons);
				}
			} else {
				removeNotAnd(orCons.getLeft());
			}
			if (orCons.getRight() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) orCons.getRight();
				if (notCons.getContent() instanceof AndConstraint) {
					AndConstraint andCons = (AndConstraint) notCons.getContent();
					OrConstraint auxOrCons = new OrConstraint(new NotConstraint(andCons.getLeft()),
							new NotConstraint(andCons.getRight()));
					cons.replaceConstraintSubPart(notCons, auxOrCons);
				}
			} else {
				removeNotAnd(orCons.getRight());
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) andCons.getLeft();
				if (notCons.getContent() instanceof AndConstraint) {
					AndConstraint auxAndCons = (AndConstraint) notCons.getContent();
					OrConstraint auxOrCons = new OrConstraint(new NotConstraint(auxAndCons.getLeft()),
							new NotConstraint(auxAndCons.getRight()));
					cons.replaceConstraintSubPart(notCons, auxOrCons);
				}
			} else {
				removeNotAnd(andCons.getLeft());
			}
			if (andCons.getRight() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) andCons.getRight();
				if (notCons.getContent() instanceof AndConstraint) {
					AndConstraint auxAndCons = (AndConstraint) notCons.getContent();
					OrConstraint auxOrCons = new OrConstraint(new NotConstraint(auxAndCons.getLeft()),
							new NotConstraint(auxAndCons.getRight()));
					cons.replaceConstraintSubPart(notCons, auxOrCons);
				}
			} else {
				removeNotAnd(andCons.getRight());
			}
		}
	}

	private void removeNotOr() {
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) temporalConstraintList.get(i);
				if (notCons.getContent() instanceof OrConstraint) {
					OrConstraint orCons = (OrConstraint) notCons.getContent();
					AndConstraint andCons = new AndConstraint(new NotConstraint(orCons.getLeft()),
							new NotConstraint(orCons.getRight()));
					temporalConstraintList.set(i, andCons);
				}
			} else {
				removeNotOr(temporalConstraintList.get(i));
			}
		}
	}

	private void removeNotOr(Constraint cons) {
		if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) orCons.getLeft();
				if (notCons.getContent() instanceof OrConstraint) {
					OrConstraint auxOrCons = (OrConstraint) notCons.getContent();
					AndConstraint auxAndCons = new AndConstraint(new NotConstraint(auxOrCons.getLeft()),
							new NotConstraint(auxOrCons.getRight()));
					cons.replaceConstraintSubPart(notCons, auxAndCons);
				}
			} else {
				removeNotOr(orCons.getLeft());
			}
			if (orCons.getRight() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) orCons.getRight();
				if (notCons.getContent() instanceof OrConstraint) {
					OrConstraint auxOrCons = (OrConstraint) notCons.getContent();
					AndConstraint auxAndCons = new AndConstraint(new NotConstraint(auxOrCons.getLeft()),
							new NotConstraint(auxOrCons.getRight()));
					cons.replaceConstraintSubPart(notCons, auxAndCons);
				}
			} else {
				removeNotOr(orCons.getRight());
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) andCons.getLeft();
				if (notCons.getContent() instanceof OrConstraint) {
					OrConstraint auxOrCons = (OrConstraint) notCons.getContent();
					AndConstraint auxAndCons = new AndConstraint(new NotConstraint(auxOrCons.getLeft()),
							new NotConstraint(auxOrCons.getRight()));
					cons.replaceConstraintSubPart(notCons, auxAndCons);
				}
			} else {
				removeNotOr(andCons.getLeft());
			}
			if (andCons.getRight() instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) andCons.getRight();
				if (notCons.getContent() instanceof OrConstraint) {
					OrConstraint auxOrCons = (OrConstraint) notCons.getContent();
					AndConstraint auxAndCons = new AndConstraint(new NotConstraint(auxOrCons.getLeft()),
							new NotConstraint(auxOrCons.getRight()));
					cons.replaceConstraintSubPart(notCons, auxAndCons);
				}
			} else {
				removeNotOr(andCons.getRight());
			}
		}
	}

	private Boolean existNotAndNotOr() {
		Boolean res = false;
		int index = 0;

		while (!res && index < temporalConstraintList.size()) {
			if (temporalConstraintList.get(index) instanceof NotConstraint) {
				NotConstraint notCons = (NotConstraint) temporalConstraintList.get(index);
				if ((notCons.getContent() instanceof OrConstraint) || (notCons.getContent() instanceof AndConstraint)) {
					res = true;
				}
			} else {
				res = existNotAndNotOr(temporalConstraintList.get(index));

			}
			index++;
		}
		return res;
	}

	// en esta fase no hay implication constraint, ni equivalence constraint
	private Boolean existNotAndNotOr(Constraint cons) {
		Boolean res = false;

		if (cons instanceof NotConstraint) {
			NotConstraint notCons = (NotConstraint) cons;
			res = (notCons.getContent() instanceof OrConstraint) || (notCons.getContent() instanceof AndConstraint);
		} else if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof NotConstraint) {
				NotConstraint notAux = (NotConstraint) orCons.getLeft();
				res = (notAux.getContent() instanceof OrConstraint) || (notAux.getContent() instanceof AndConstraint);
			} else {
				res = existNotAndNotOr(orCons.getLeft());
			}
			if (!res) {
				if (orCons.getRight() instanceof NotConstraint) {
					NotConstraint notAux = (NotConstraint) orCons.getRight();
					res = (notAux.getContent() instanceof OrConstraint)
							|| (notAux.getContent() instanceof AndConstraint);
				} else {
					res = existNotAndNotOr(orCons.getRight());
				}
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof NotConstraint) {
				NotConstraint notAux = (NotConstraint) andCons.getLeft();
				res = (notAux.getContent() instanceof OrConstraint) || (notAux.getContent() instanceof AndConstraint);
			} else {
				res = existNotAndNotOr(andCons.getLeft());
			}
			if (!res) {
				if (andCons.getRight() instanceof NotConstraint) {
					NotConstraint notAux = (NotConstraint) andCons.getRight();
					res = (notAux.getContent() instanceof OrConstraint)
							|| (notAux.getContent() instanceof AndConstraint);
				} else {
					res = existNotAndNotOr(andCons.getRight());
				}
			}
		}
		return res;
	}

	private Boolean existImpicationContraint() {
		Boolean res = false;
		int index = 0;

		while (!res && index < temporalConstraintList.size()) {
			if (temporalConstraintList.get(index) instanceof ImplicationConstraint) {
				res = true;
			} else {
				res = existImplicationContraint(temporalConstraintList.get(index));
			}
			index++;
		}
		return res;
	}

	private Boolean existImplicationContraint(Constraint cons) {
		Boolean res = false;

		if (cons instanceof ParenthesisConstraint) {
			res = existImplicationContraint(((ParenthesisConstraint) cons).getContent());
		} else if (cons instanceof LiteralConstraint) {
			res = false;
		} else if (cons instanceof NotConstraint) {
			res = existImplicationContraint(((NotConstraint) cons).getContent());
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			res = existImplicationContraint(andCons.getLeft()) || existImplicationContraint(andCons.getRight());
		} else if (cons instanceof EquivalenceConstraint) {
			EquivalenceConstraint equilCons = (EquivalenceConstraint) cons;
			res = existImplicationContraint(equilCons.getLeft()) || existImplicationContraint(equilCons.getRight());
		} else if (cons instanceof ImplicationConstraint) {
			res = true;
		} else if (cons instanceof OrConstraint) {
			OrConstraint andCons = (OrConstraint) cons;
			res = existImplicationContraint(andCons.getLeft()) || existImplicationContraint(andCons.getRight());
		}
		return res;
	}

	private void removeImplicationConstraint(Constraint cons) {
		if (cons instanceof NotConstraint) {
			NotConstraint notCons = (NotConstraint) cons;
			if (notCons.getContent() instanceof ImplicationConstraint) {
				ImplicationConstraint implCons = (ImplicationConstraint) notCons.getContent();
				NotConstraint intNotCons = new NotConstraint(implCons.getLeft());
				OrConstraint orCons = new OrConstraint(intNotCons, implCons.getRight());
				notCons.replaceConstraintSubPart(notCons.getContent(), orCons);
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof ImplicationConstraint) {
				ImplicationConstraint implCons = (ImplicationConstraint) andCons.getLeft();
				NotConstraint intNotCons = new NotConstraint(implCons.getLeft());
				OrConstraint orCons = new OrConstraint(intNotCons, implCons.getRight());
				andCons.replaceConstraintSubPart(andCons.getLeft(), orCons);
			} else {
				removeImplicationConstraint(andCons.getLeft());
			}
			if (andCons.getRight() instanceof ImplicationConstraint) {
				ImplicationConstraint implCons = (ImplicationConstraint) andCons.getRight();
				NotConstraint intNotCons = new NotConstraint(implCons.getLeft());
				OrConstraint orCons = new OrConstraint(intNotCons, implCons.getRight());
				andCons.replaceConstraintSubPart(andCons.getRight(), orCons);
			} else {
				removeImplicationConstraint(andCons.getRight());
			}
		} else if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof ImplicationConstraint) {
				ImplicationConstraint implCons = (ImplicationConstraint) orCons.getLeft();
				NotConstraint intNotCons = new NotConstraint(implCons.getLeft());
				OrConstraint intOrCons = new OrConstraint(intNotCons, implCons.getRight());
				orCons.replaceConstraintSubPart(orCons.getLeft(), intOrCons);
			} else {
				removeImplicationConstraint(orCons.getLeft());
			}
			if (orCons.getRight() instanceof ImplicationConstraint) {
				ImplicationConstraint implCons = (ImplicationConstraint) orCons.getRight();
				NotConstraint intNotCons = new NotConstraint(implCons.getLeft());
				OrConstraint intOrCons = new OrConstraint(intNotCons, implCons.getRight());
				orCons.replaceConstraintSubPart(orCons.getRight(), intOrCons);
			} else {
				removeImplicationConstraint(orCons.getRight());
			}
		}
	}

	private void removeImplicationConstraint() {
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof ImplicationConstraint) {
				// se tranforma la estructura
				ImplicationConstraint implCons = (ImplicationConstraint) temporalConstraintList.get(i);
				NotConstraint notCons = new NotConstraint(implCons.getLeft());
				OrConstraint orCons = new OrConstraint(notCons, implCons.getRight());
				temporalConstraintList.set(i, orCons);
			} else if (existImplicationContraint(temporalConstraintList.get(i))) {
				removeImplicationConstraint(temporalConstraintList.get(i));
			}
		}
	}

	private void removeEquivalenceConstraint() {
		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (temporalConstraintList.get(i) instanceof EquivalenceConstraint) {
				// se tranforma la estructura
				EquivalenceConstraint equilCons = (EquivalenceConstraint) temporalConstraintList.get(i);
				ImplicationConstraint leftImplication = new ImplicationConstraint(equilCons.getLeft(),
						equilCons.getRight());
				ImplicationConstraint rightImplication = new ImplicationConstraint(equilCons.getRight(),
						equilCons.getLeft());
				// AndConstraint andConstraint = new AndConstraint(leftImplication,
				// rightImplication);
				temporalConstraintList.set(i, leftImplication);
				temporalConstraintList.add(rightImplication);
			} else if (existEquivalenceConstraint(temporalConstraintList.get(i))) {
				removeEquivalenceConstraint(temporalConstraintList.get(i));
			}
		}
	}

	private void removeEquivalenceConstraint(Constraint cons) {
		if (cons instanceof NotConstraint) {
			NotConstraint notCons = (NotConstraint) cons;
			if (notCons.getContent() instanceof EquivalenceConstraint) {
				EquivalenceConstraint equilCons = ((EquivalenceConstraint) notCons.getContent());
				ImplicationConstraint leftImplication = new ImplicationConstraint(equilCons.getLeft(),
						equilCons.getRight());
				ImplicationConstraint rightImplication = new ImplicationConstraint(equilCons.getRight(),
						equilCons.getLeft());
				AndConstraint andConstraint = new AndConstraint(leftImplication, rightImplication);
				notCons.replaceConstraintSubPart(notCons.getContent(), andConstraint);
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof EquivalenceConstraint) {
				EquivalenceConstraint equilCons = (EquivalenceConstraint) andCons.getLeft();
				ImplicationConstraint leftImplication = new ImplicationConstraint(equilCons.getLeft(),
						equilCons.getRight());
				ImplicationConstraint rightImplication = new ImplicationConstraint(equilCons.getRight(),
						equilCons.getLeft());
				AndConstraint andConstraint = new AndConstraint(leftImplication, rightImplication);
				andCons.replaceConstraintSubPart(andCons.getLeft(), andConstraint);
			} else {
				removeEquivalenceConstraint(andCons.getLeft());
			}
			if (andCons.getRight() instanceof EquivalenceConstraint) {
				EquivalenceConstraint equilCons = (EquivalenceConstraint) andCons.getRight();
				ImplicationConstraint leftImplication = new ImplicationConstraint(equilCons.getLeft(),
						equilCons.getRight());
				ImplicationConstraint rightImplication = new ImplicationConstraint(equilCons.getRight(),
						equilCons.getLeft());
				AndConstraint andConstraint = new AndConstraint(leftImplication, rightImplication);
				andCons.replaceConstraintSubPart(andCons.getRight(), andConstraint);
			} else {
				removeEquivalenceConstraint(andCons.getRight());
			}
		} else if (cons instanceof ImplicationConstraint) {
			ImplicationConstraint impCons = (ImplicationConstraint) cons;
			if (impCons.getLeft() instanceof EquivalenceConstraint) {
				EquivalenceConstraint equilCons = (EquivalenceConstraint) impCons.getLeft();
				ImplicationConstraint leftImplication = new ImplicationConstraint(equilCons.getLeft(),
						equilCons.getRight());
				ImplicationConstraint rightImplication = new ImplicationConstraint(equilCons.getRight(),
						equilCons.getLeft());
				AndConstraint andConstraint = new AndConstraint(leftImplication, rightImplication);
				impCons.replaceConstraintSubPart(impCons.getLeft(), andConstraint);
			} else {
				removeEquivalenceConstraint(impCons.getLeft());
			}
			if (impCons.getRight() instanceof EquivalenceConstraint) {
				EquivalenceConstraint equilCons = (EquivalenceConstraint) impCons.getRight();
				ImplicationConstraint leftImplication = new ImplicationConstraint(equilCons.getLeft(),
						equilCons.getRight());
				ImplicationConstraint rightImplication = new ImplicationConstraint(equilCons.getRight(),
						equilCons.getLeft());
				AndConstraint andConstraint = new AndConstraint(leftImplication, rightImplication);
				impCons.replaceConstraintSubPart(impCons.getRight(), andConstraint);
			} else {
				removeEquivalenceConstraint(impCons.getRight());
			}
		} else if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof EquivalenceConstraint) {
				EquivalenceConstraint equilCons = (EquivalenceConstraint) orCons.getLeft();
				ImplicationConstraint leftImplication = new ImplicationConstraint(equilCons.getLeft(),
						equilCons.getRight());
				ImplicationConstraint rightImplication = new ImplicationConstraint(equilCons.getRight(),
						equilCons.getLeft());
				AndConstraint andConstraint = new AndConstraint(leftImplication, rightImplication);
				orCons.replaceConstraintSubPart(orCons.getLeft(), andConstraint);
			} else {
				removeEquivalenceConstraint(orCons.getLeft());
			}
			if (orCons.getRight() instanceof EquivalenceConstraint) {
				EquivalenceConstraint equilCons = (EquivalenceConstraint) orCons.getRight();
				ImplicationConstraint leftImplication = new ImplicationConstraint(equilCons.getLeft(),
						equilCons.getRight());
				ImplicationConstraint rightImplication = new ImplicationConstraint(equilCons.getRight(),
						equilCons.getLeft());
				AndConstraint andConstraint = new AndConstraint(leftImplication, rightImplication);
				orCons.replaceConstraintSubPart(orCons.getRight(), andConstraint);
			} else {
				removeEquivalenceConstraint(orCons.getRight());
			}
		}
	}

	private Boolean existEquivalenceConstraint() {
		Boolean res = false;
		int index = 0;

		while (!res && index < temporalConstraintList.size()) {
			if (temporalConstraintList.get(index) instanceof EquivalenceConstraint) {
				res = true;
			} else {
				res = existEquivalenceConstraint(temporalConstraintList.get(index));
			}
			index++;
		}
		return res;
	}

	private Boolean existEquivalenceConstraint(Constraint cons) {
		Boolean res = false;
		if (cons instanceof ParenthesisConstraint) {
			res = existEquivalenceConstraint(((ParenthesisConstraint) cons).getContent());
		} else if (cons instanceof LiteralConstraint) {
			res = false;
		} else if (cons instanceof NotConstraint) {
			res = existEquivalenceConstraint(((NotConstraint) cons).getContent());
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			res = existEquivalenceConstraint(andCons.getLeft()) || existEquivalenceConstraint(andCons.getRight());
		} else if (cons instanceof EquivalenceConstraint) {

			res = true;
		} else if (cons instanceof ImplicationConstraint) {
			ImplicationConstraint andCons = (ImplicationConstraint) cons;
			res = existEquivalenceConstraint(andCons.getLeft()) || existEquivalenceConstraint(andCons.getRight());
		} else if (cons instanceof OrConstraint) {
			OrConstraint andCons = (OrConstraint) cons;
			res = existEquivalenceConstraint(andCons.getLeft()) || existEquivalenceConstraint(andCons.getRight());
		}
		return res;

	}

	private Boolean existParenthesis(Constraint cons) {
		Boolean res = false;

		if (cons instanceof ParenthesisConstraint) {
			res = true;
		} else if (cons instanceof LiteralConstraint) {
			res = false;
		} else if (cons instanceof NotConstraint) {
			res = existParenthesis(((NotConstraint) cons).getContent());
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			res = existParenthesis(andCons.getLeft()) || existParenthesis(andCons.getRight());
		} else if (cons instanceof EquivalenceConstraint) {
			EquivalenceConstraint andCons = (EquivalenceConstraint) cons;
			res = existParenthesis(andCons.getLeft()) || existParenthesis(andCons.getRight());
		} else if (cons instanceof ImplicationConstraint) {
			ImplicationConstraint andCons = (ImplicationConstraint) cons;
			res = existParenthesis(andCons.getLeft()) || existParenthesis(andCons.getRight());
		} else if (cons instanceof OrConstraint) {
			OrConstraint andCons = (OrConstraint) cons;
			res = existParenthesis(andCons.getLeft()) || existParenthesis(andCons.getRight());
		}
		return res;
	}

	private Boolean existParenthesis() {
		Boolean res = false;
		int index = 0;
		while (!res && index < temporalConstraintList.size()) {
			if (temporalConstraintList.get(index) instanceof ParenthesisConstraint) {
				res = true;
			} else {
				res = existParenthesis(temporalConstraintList.get(index));
			}
			index++;
		}
		return res;
	}

	private void removeParenthesis(Constraint cons) {

		if (cons instanceof NotConstraint) {
			NotConstraint notCons = (NotConstraint) cons;
			if (notCons.getContent() instanceof ParenthesisConstraint) {
				Constraint content = ((ParenthesisConstraint) notCons.getContent()).getContent();
				notCons.replaceConstraintSubPart(notCons.getContent(), content);
			}
		} else if (cons instanceof AndConstraint) {
			AndConstraint andCons = (AndConstraint) cons;
			if (andCons.getLeft() instanceof ParenthesisConstraint) {
				Random rand = new Random();
				String literal = "Fake_Literal" + rand.nextInt();
				int index = problem.getIndex(literal);
				problem.addBoundingConstraint(index, 0, 1);
				LiteralConstraint litCons = new LiteralConstraint(literal);
				// se reemplaza el lado izquierdo por el nuevo literal
				Constraint aux = ((ParenthesisConstraint) andCons.getLeft()).getContent();
				andCons.replaceConstraintSubPart(andCons.getLeft(), litCons);
				EquivalenceConstraint equilCons = new EquivalenceConstraint(litCons, aux);
				temporalConstraintList.add(equilCons);
			} else {
				removeParenthesis(andCons.getLeft());
			}
			if (andCons.getRight() instanceof ParenthesisConstraint) {
				Random rand = new Random();
				String literal = "Fake_Literal" + rand.nextInt();
				int index = problem.getIndex(literal);
				problem.addBoundingConstraint(index, 0, 1);
				LiteralConstraint litCons = new LiteralConstraint(literal);
				// se reemplaza el lado izquierdo por el nuevo literal
				Constraint aux = ((ParenthesisConstraint) andCons.getRight()).getContent();
				andCons.replaceConstraintSubPart(andCons.getRight(), litCons);
				EquivalenceConstraint equilCons = new EquivalenceConstraint(litCons, aux);
				temporalConstraintList.add(equilCons);
			} else {
				removeParenthesis(andCons.getRight());
			}
		} else if (cons instanceof EquivalenceConstraint) {
			EquivalenceConstraint equiCons = (EquivalenceConstraint) cons;
			if (equiCons.getLeft() instanceof ParenthesisConstraint) {
				Random rand = new Random();
				String literal = "Fake_Literal" + rand.nextInt();
				int index = problem.getIndex(literal);
				problem.addBoundingConstraint(index, 0, 1);
				LiteralConstraint litCons = new LiteralConstraint(literal);
				// se reemplaza el lado izquierdo por el nuevo literal
				Constraint aux = ((ParenthesisConstraint) equiCons.getLeft()).getContent();
				equiCons.replaceConstraintSubPart(equiCons.getLeft(), litCons);
				EquivalenceConstraint equilCons = new EquivalenceConstraint(litCons, aux);
				temporalConstraintList.add(equilCons);
			} else {
				removeParenthesis(equiCons.getLeft());
			}
			if (equiCons.getRight() instanceof ParenthesisConstraint) {
				Random rand = new Random();
				String literal = "Fake_Literal" + rand.nextInt();
				int index = problem.getIndex(literal);
				problem.addBoundingConstraint(index, 0, 1);
				LiteralConstraint litCons = new LiteralConstraint(literal);
				// se reemplaza el lado izquierdo por el nuevo literal
				Constraint aux = ((ParenthesisConstraint) equiCons.getRight()).getContent();
				equiCons.replaceConstraintSubPart(equiCons.getRight(), litCons);
				EquivalenceConstraint equilCons = new EquivalenceConstraint(litCons, aux);
				temporalConstraintList.add(equilCons);
			} else {
				removeParenthesis(equiCons.getRight());
			}
		} else if (cons instanceof ImplicationConstraint) {
			ImplicationConstraint impCons = (ImplicationConstraint) cons;
			if (impCons.getLeft() instanceof ParenthesisConstraint) {
				Random rand = new Random();
				String literal = "Fake_Literal" + rand.nextInt();
				int index = problem.getIndex(literal);
				problem.addBoundingConstraint(index, 0, 1);
				LiteralConstraint litCons = new LiteralConstraint(literal);
				// se reemplaza el lado izquierdo por el nuevo literal
				Constraint aux = ((ParenthesisConstraint) impCons.getLeft()).getContent();
				impCons.replaceConstraintSubPart(impCons.getLeft(), litCons);
				EquivalenceConstraint equilCons = new EquivalenceConstraint(litCons, aux);
				temporalConstraintList.add(equilCons);
			} else {
				removeParenthesis(impCons.getLeft());
			}
			if (impCons.getRight() instanceof ParenthesisConstraint) {
				Random rand = new Random();
				String literal = "Fake_Literal" + rand.nextInt();
				int index = problem.getIndex(literal);
				problem.addBoundingConstraint(index, 0, 1);
				LiteralConstraint litCons = new LiteralConstraint(literal);
				// se reemplaza el lado izquierdo por el nuevo literal
				Constraint aux = ((ParenthesisConstraint) impCons.getRight()).getContent();
				impCons.replaceConstraintSubPart(impCons.getRight(), litCons);
				EquivalenceConstraint equilCons = new EquivalenceConstraint(litCons, aux);
				temporalConstraintList.add(equilCons);
			} else {
				removeParenthesis(impCons.getRight());
			}
		} else if (cons instanceof OrConstraint) {
			OrConstraint orCons = (OrConstraint) cons;
			if (orCons.getLeft() instanceof ParenthesisConstraint) {
				Random rand = new Random();
				String literal = "Fake_Literal" + rand.nextInt();
				int index = problem.getIndex(literal);
				problem.addBoundingConstraint(index, 0, 1);
				LiteralConstraint litCons = new LiteralConstraint(literal);
				// se reemplaza el lado izquierdo por el nuevo literal
				Constraint aux = ((ParenthesisConstraint) orCons.getLeft()).getContent();
				orCons.replaceConstraintSubPart(orCons.getLeft(), litCons);
				EquivalenceConstraint equilCons = new EquivalenceConstraint(litCons, aux);
				temporalConstraintList.add(equilCons);
			} else {
				removeParenthesis(orCons.getLeft());
			}
			if (orCons.getRight() instanceof ParenthesisConstraint) {
				Random rand = new Random();
				String literal = "Fake_Literal" + rand.nextInt();
				int index = problem.getIndex(literal);
				problem.addBoundingConstraint(index, 0, 1);
				LiteralConstraint litCons = new LiteralConstraint(literal);
				// se reemplaza el lado izquierdo por el nuevo literal
				Constraint aux = ((ParenthesisConstraint) orCons.getRight()).getContent();
				orCons.replaceConstraintSubPart(orCons.getRight(), litCons);
				EquivalenceConstraint equilCons = new EquivalenceConstraint(litCons, aux);
				temporalConstraintList.add(equilCons);
			} else {
				removeParenthesis(orCons.getRight());
			}
		}

	}

	private void removeParenthesis() {

		for (int i = 0; i < temporalConstraintList.size(); i++) {
			if (existParenthesis(temporalConstraintList.get(i))) {
				removeParenthesis(temporalConstraintList.get(i));
			} else if (temporalConstraintList.get(i) instanceof ParenthesisConstraint) {
				temporalConstraintList.set(i, ((ParenthesisConstraint) temporalConstraintList.get(i)).getContent());
			}
		}
	}

	// Si es una fake constraint, no tiene feature asociada
	// Las fake constraint son generadas cuando hacemos cut-off de árboles.
	private Integer getIndexFromLiteralConstraint(LiteralConstraint cons) {
		Feature feature = cons.getFeature();
		Integer index;
		if (feature == null) {
			index = problem.getIndex(cons.getLiteral());
		} else {
			index = problem.getIndex(feature);
		}
		// se añade boundings para esta constraint
		problem.addBoundingConstraint(index, 0, 1);
		return index;
	}

	//
	private void transformOrConstraint(OrConstraint cons) {
		int numNotLiterals = 0;
		List<Term> termList = new LinkedList<Term>();
		for (int i = 0; i < cons.getConstraintSubParts().size(); i++) {
			Constraint aux = cons.getConstraintSubParts().get(i);
			if (aux instanceof LiteralConstraint) {
				Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
				termList.add(new Term(-1d, index));
			} else if (aux instanceof NotConstraint) {
				numNotLiterals++;
				// Si es un literal dentro del not continuamos como si nada.
				if (((NotConstraint) aux).getContent() instanceof LiteralConstraint) {
					Integer index = getIndexFromLiteralConstraint(
							(LiteralConstraint) ((NotConstraint) aux).getContent());
					termList.add(new Term(1d, index));
				} else {
					Random rand = new Random();
					// se crea una variable falsa.
					LiteralConstraint fakeConstraint = new LiteralConstraint("Fake_" + rand.nextInt());
					// se añade al termList
					Integer index = getIndexFromLiteralConstraint(fakeConstraint);
					termList.add(new Term(1d, index));
					// se crea la expresión que hace la equivalencia
					NotConstraint notFakeContraint = new NotConstraint(fakeConstraint);
					EquivalenceConstraint eec = new EquivalenceConstraint(notFakeContraint,
							((NotConstraint) aux).getContent());
					transfromInLinearConstraint(eec);
				}
			}
		}
		Integer constant = (-1) * (1 - numNotLiterals);
		LinearConstraint newCons = new LinearConstraint(termList, constant, Comparator.LowerOrEqual);
		problem.addConstraint(newCons);
	}

	private void transfromInLinearConstraint(Constraint cons) {
		List<Term> termList = new LinkedList<Term>();
		if (cons instanceof LiteralConstraint) {
			Integer index = getIndexFromLiteralConstraint((LiteralConstraint) cons);
			termList.add(new Term(1d, index));
			LinearConstraint lc = new LinearConstraint(termList, 1, Comparator.Equal);
			problem.addEqualityConstraint(lc);
		} else if (cons instanceof OrConstraint) {
			transformOrConstraint((OrConstraint) cons);
		} else if (cons instanceof ImplicationConstraint) {
			transformImplicationConstraint((ImplicationConstraint) cons);
		} else if (cons instanceof NotConstraint) {
			Constraint aux = ((NotConstraint) cons).getContent();
			if (aux instanceof LiteralConstraint) {
				Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
				termList.add(new Term(1d, index));
				LinearConstraint lc = new LinearConstraint(termList, 1, Comparator.Equal);
				problem.addEqualityConstraint(lc);
			}
			/*
			 * } else if (cons instanceof ExpressionConstraint) {
			 * transformExpressionConstraint((ExpressionConstraint) cons);
			 */
		} else if (cons instanceof EquivalenceConstraint) {
			// (A <-> B) == (!A | !B) & (A | B)
			EquivalenceConstraint aux = (EquivalenceConstraint) cons;
			Constraint a = ((EquivalenceConstraint) aux).getLeft();
			Constraint b = ((EquivalenceConstraint) aux).getRight();
			OrConstraint left = new OrConstraint(reduceNotConstraint(new NotConstraint(a)),
					reduceNotConstraint(new NotConstraint(b)));
			OrConstraint right = new OrConstraint(reduceNotConstraint(a), reduceNotConstraint(b));
			transfromInLinearConstraint(left);
			transfromInLinearConstraint(right);
		}

		/*
		 * // (A <-> B) == (!A | !B) & (A | B) Constraint a = ((EquivalenceConstraint)
		 * aux).getLeft(); Constraint b = ((EquivalenceConstraint) aux).getRight();
		 * OrConstraint left = new OrConstraint(reduceNotConstraint(new
		 * NotConstraint(a)), reduceNotConstraint(new NotConstraint(b))); OrConstraint
		 * right = new OrConstraint(reduceNotConstraint(a), reduceNotConstraint(b)); res
		 * = new AndConstraint(left, right);
		 **/
	}

	private Boolean hasNumberExpression(ExpressionConstraint cons) {
		return (cons.getLeft() instanceof NumberExpression) || (cons.getRight() instanceof NumberExpression);
	}

	private void transformExpressionConstraintWithoutNumbers(ExpressionConstraint cons) {
		LiteralExpression aux;
		List<Term> termList = new LinkedList<Term>();
		if (cons instanceof EqualEquationConstraint) {
			aux = (LiteralExpression) cons.getLeft();
			Integer index = problem.getIndex(aux.getFeature());
			termList.add(new Term(1d, index));
			aux = (LiteralExpression) cons.getLeft();
			index = problem.getIndex(aux.getFeature());
			termList.add(new Term(-1d, index));
			problem.addEqualityConstraint(new LinearConstraint(termList, 0, Comparator.Equal));
		} else if (cons instanceof GreaterEqualsEquationConstraint) {
			// -a+b<=0
			aux = (LiteralExpression) cons.getLeft();
			Integer index = problem.getIndex(aux.getFeature());
			termList.add(new Term(-1d, index));
			aux = (LiteralExpression) cons.getLeft();
			index = problem.getIndex(aux.getFeature());
			termList.add(new Term(1d, index));
			problem.addEqualityConstraint(new LinearConstraint(termList, 0, Comparator.LowerOrEqual));
		} else if (cons instanceof GreaterEquationConstraint) {
			aux = (LiteralExpression) cons.getLeft();
			Integer index = problem.getIndex(aux.getFeature());
			termList.add(new Term(-1d, index));
			aux = (LiteralExpression) cons.getLeft();
			index = problem.getIndex(aux.getFeature());
			termList.add(new Term(1d, index));
			problem.addEqualityConstraint(new LinearConstraint(termList, -1, Comparator.LowerOrEqual));
		} else if (cons instanceof LowerEqualsEquationConstraint) {
			aux = (LiteralExpression) cons.getLeft();
			Integer index = problem.getIndex(aux.getFeature());
			termList.add(new Term(1d, index));
			aux = (LiteralExpression) cons.getLeft();
			index = problem.getIndex(aux.getFeature());
			termList.add(new Term(-1d, index));
			problem.addEqualityConstraint(new LinearConstraint(termList, 0, Comparator.LowerOrEqual));
		} else if (cons instanceof LowerEquationConstraint) {
			// a-b<=-1
			aux = (LiteralExpression) cons.getLeft();
			Integer index = problem.getIndex(aux.getFeature());
			termList.add(new Term(1d, index));
			aux = (LiteralExpression) cons.getLeft();
			index = problem.getIndex(aux.getFeature());
			termList.add(new Term(-1d, index));
			problem.addEqualityConstraint(new LinearConstraint(termList, -1, Comparator.LowerOrEqual));
		} else {// NotEqualsEquationConstraint
				// we generate two constraints to model the scenario in which literals cannot be
				// equals
				// -a+b<=-1
			aux = (LiteralExpression) cons.getLeft();
			Integer index = problem.getIndex(aux.getFeature());
			termList.add(new Term(-1d, index));
			aux = (LiteralExpression) cons.getLeft();
			index = problem.getIndex(aux.getFeature());
			termList.add(new Term(1d, index));
			problem.addEqualityConstraint(new LinearConstraint(termList, -1, Comparator.LowerOrEqual));
			// a-b<=-1
			aux = (LiteralExpression) cons.getLeft();
			index = problem.getIndex(aux.getFeature());
			termList.add(new Term(1d, index));
			aux = (LiteralExpression) cons.getLeft();
			index = problem.getIndex(aux.getFeature());
			termList.add(new Term(-1d, index));
			problem.addEqualityConstraint(new LinearConstraint(termList, -1, Comparator.LowerOrEqual));
		}
	}

	private void transformExpressionConstraintWithNumbers(ExpressionConstraint cons) {
		LiteralExpression literal;
		NumberExpression number;
		LinearConstraint toPrint = null;
		List<Term> termList = new LinkedList<Term>();
		if (cons.getLeft() instanceof NumberExpression) {
			literal = (LiteralExpression) cons.getRight();
			number = (NumberExpression) cons.getLeft();
		} else {
			literal = (LiteralExpression) cons.getLeft();
			number = (NumberExpression) cons.getRight();
		}
		int constant = (int) number.getNumber();
		Integer index = problem.getIndex(literal.getFeature());
		if (cons instanceof EqualEquationConstraint) {
			termList.add(new Term(1d, index));
			problem.addEqualityConstraint(new LinearConstraint(termList, constant, Comparator.Equal));
			toPrint = new LinearConstraint(termList, constant, Comparator.Equal);
			System.out.println(toPrint);
		} else if (cons instanceof GreaterEqualsEquationConstraint) {
			// 3>=X
			if (cons.getLeft() instanceof NumberExpression) {
				termList.add(new Term(-1d, index));
				constant = constant * (-1);
				// x>=3
			} else {
				termList.add(new Term(1d, index));

			}
			problem.addEqualityConstraint(new LinearConstraint(termList, constant, Comparator.LowerOrEqual));
			toPrint = new LinearConstraint(termList, constant, Comparator.LowerOrEqual);
			System.out.println(toPrint);
		} else if (cons instanceof GreaterEquationConstraint) {
			// X>3
			if (cons.getLeft() instanceof LiteralExpression) {
				termList.add(new Term(-1d, index));
				constant = constant * (-1);// -X<-3
				constant--;
				// 3>X
			} else {
				// -a<=-(number+1)
				termList.add(new Term(1d, index));
				constant--;
			}
			problem.addEqualityConstraint(new LinearConstraint(termList, constant, Comparator.LowerOrEqual));
			toPrint = new LinearConstraint(termList, constant, Comparator.LowerOrEqual);
			System.out.println(toPrint);
		} else if (cons instanceof LowerEqualsEquationConstraint) {
			// 3<=X
			if (cons.getLeft() instanceof NumberExpression) {
				termList.add(new Term(-1d, index));
				constant = constant * (-1);
				// x>=3
			} else {
				termList.add(new Term(1d, index));
			}
			problem.addEqualityConstraint(new LinearConstraint(termList, constant, Comparator.LowerOrEqual));
			toPrint = new LinearConstraint(termList, constant, Comparator.LowerOrEqual);
			System.out.println(toPrint);
		} else if (cons instanceof LowerEquationConstraint) {
			// X<3
			if (cons.getRight() instanceof NumberExpression) {
				// -a<=-(number+1)
				termList.add(new Term(1d, index));
				constant--;
				// 3<X
			} else {
				termList.add(new Term(-1d, index));
				constant = (-1) * constant;// -3>-X
				constant--;

			}
			problem.addEqualityConstraint(new LinearConstraint(termList, constant, Comparator.LowerOrEqual));
			toPrint = new LinearConstraint(termList, constant, Comparator.LowerOrEqual);
			System.out.println(toPrint);
		} else {// NotEqualsEquationConstraint
			// -a<=-(num+1)
			termList.add(new Term(-1d, index));
			problem.addConstraint(new LinearConstraint(termList, (-1) * (constant + 1), Comparator.LowerOrEqual));
			toPrint = new LinearConstraint(termList, (-1) * (constant + 1), Comparator.LowerOrEqual);
			System.out.print(toPrint + " y ");
			termList = new LinkedList<Term>();
			termList.add(new Term(1d, index));
			problem.addConstraint(new LinearConstraint(termList, constant - 1, Comparator.LowerOrEqual));
			toPrint = new LinearConstraint(termList, constant - 1, Comparator.LowerOrEqual);
			System.out.println(toPrint);
		}
	}

	// we assume that these expression are composed only of LiteralExpression
	// elements
	private void transformExpressionConstraint(ExpressionConstraint cons) {

		if (!hasNumberExpression(cons)) {
			transformExpressionConstraintWithoutNumbers(cons);
		} else {
			transformExpressionConstraintWithNumbers(cons);
		}
	}

	private void transformImplicationConstraint(ImplicationConstraint cons) {
		Constraint leftConstraint = cons.getLeft();
		List<Term> termList = new LinkedList<Term>();
		int numNotLiteralLeft = 0;

		// se procesa el lado izquiero de la implicación
		for (int i = 0; i < leftConstraint.getConstraintSubParts().size(); i++) {
			Constraint aux = leftConstraint.getConstraintSubParts().get(i);
			if (aux instanceof LiteralConstraint) {
				Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
				termList.add(new Term(1d, index));
			} else if (aux instanceof NotConstraint) {
				numNotLiteralLeft++;
				Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
				termList.add(new Term(1d, index));
			} else if (aux instanceof OrConstraint) {
				OrConstraint orCons = (OrConstraint) aux;
				for (int j = 0; j < orCons.getConstraintSubParts().size(); i++) {
					if (orCons.getConstraintSubParts().get(j) instanceof LiteralConstraint) {
						Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
						termList.add(new Term(1d, index));
					} else if (orCons.getConstraintSubParts().get(j) instanceof LiteralConstraint) {
						numNotLiteralLeft++;
						Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
						termList.add(new Term(-1d, index));
					}
				}
			}
		}
		// se procesa el lado derecho de la implicación
		Constraint rightConstraint = cons.getRight();
		int numNotLiteralRight = 0;
		for (int i = 0; i < rightConstraint.getConstraintSubParts().size(); i++) {
			Constraint aux = rightConstraint.getConstraintSubParts().get(i);
			if (aux instanceof LiteralConstraint) {
				Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
				termList.add(new Term(-1d, index));
			} else if (aux instanceof NotConstraint) {
				numNotLiteralRight++;
				Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
				termList.add(new Term(1d, index));
			} else if (aux instanceof OrConstraint) {
				OrConstraint orCons = (OrConstraint) aux;
				for (int j = 0; j < orCons.getConstraintSubParts().size(); i++) {
					if (orCons.getConstraintSubParts().get(j) instanceof LiteralConstraint) {
						Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
						termList.add(new Term(-1d, index));
					} else if (orCons.getConstraintSubParts().get(j) instanceof LiteralConstraint) {
						numNotLiteralRight++;
						Integer index = getIndexFromLiteralConstraint((LiteralConstraint) aux);
						termList.add(new Term(1d, index));
					}
				}
			}
		}
		// se compone la expresión
		Integer constant = numNotLiteralRight - numNotLiteralLeft;
		LinearConstraint constraint = new LinearConstraint(termList, constant, Comparator.LowerOrEqual);
		problem.addConstraint(constraint);
	}

	private Constraint distributeOr(Constraint lit, AndConstraint andCons) {
		Constraint aux = andCons.getLeft();
		if (aux instanceof ParenthesisConstraint) {
			aux = ((ParenthesisConstraint) andCons.getLeft()).getContent();
		}
		if (aux instanceof OrConstraint) {
			aux = pushUpwardsOr((OrConstraint) aux);
		}
		if (aux == null) {
			aux = andCons.getLeft();
		}
		OrConstraint left = new OrConstraint(lit, aux);

		aux = andCons.getRight();
		if (aux instanceof ParenthesisConstraint) {
			aux = ((ParenthesisConstraint) andCons.getRight()).getContent();
		}
		if (aux instanceof OrConstraint) {
			aux = pushUpwardsOr((OrConstraint) aux);
		}
		if (aux == null) {
			aux = andCons.getRight();
		}
		OrConstraint right = new OrConstraint(lit, aux);
		AndConstraint res = new AndConstraint(left, right);
		return res;
	}

	private Constraint pushUpwardsOr(OrConstraint cons) {
		Constraint res = null;
		Constraint left = cons.getLeft();
		Constraint right = cons.getRight();

		if ((left instanceof LiteralConstraint) || (left instanceof NotConstraint)) {
			if (right instanceof ParenthesisConstraint) {
				right = ((ParenthesisConstraint) right).getContent();
			}
			if (right instanceof AndConstraint) {
				res = distributeOr(left, (AndConstraint) right);
			}
		} else if ((right instanceof LiteralConstraint) || (right instanceof NotConstraint)) {
			if (left instanceof ParenthesisConstraint) {
				left = ((ParenthesisConstraint) left).getContent();
			}
			if (left instanceof AndConstraint) {
				res = distributeOr(right, (AndConstraint) left);
			}
		}
		return res;
	}

	private Constraint reduceNotConstraintLevelTwo(Constraint aux) {
		Constraint res = null;
		if (aux instanceof NotConstraint) {
			res = reduceNotConstraint(((NotConstraint) aux).getContent());
		} else if (aux instanceof AndConstraint) {
			Constraint left = new NotConstraint(((AndConstraint) aux).getLeft());
			Constraint right = new NotConstraint(((AndConstraint) aux).getRight());
			res = new OrConstraint(reduceNotConstraint(left), reduceNotConstraint(right));
		} else if (aux instanceof OrConstraint) {
			Constraint left = new NotConstraint(((OrConstraint) aux).getLeft());
			Constraint right = new NotConstraint(((OrConstraint) aux).getRight());
			res = new AndConstraint(reduceNotConstraint(left), reduceNotConstraint(right));
		} else if (aux instanceof EquivalenceConstraint) {
			// (A <-> B) == (!A | !B) & (A | B)
			Constraint a = ((EquivalenceConstraint) aux).getLeft();
			Constraint b = ((EquivalenceConstraint) aux).getRight();
			OrConstraint left = new OrConstraint(reduceNotConstraint(new NotConstraint(a)),
					reduceNotConstraint(new NotConstraint(b)));
			OrConstraint right = new OrConstraint(reduceNotConstraint(a), reduceNotConstraint(b));
			res = new AndConstraint(left, right);
		} else if (aux instanceof ExpressionConstraint) {
			if (aux instanceof GreaterEquationConstraint) {
				Expression left = ((GreaterEquationConstraint) aux).getLeft();
				Expression right = ((GreaterEquationConstraint) aux).getRight();
				res = new LowerEquationConstraint(left, right);
			} else if (aux instanceof GreaterEqualsEquationConstraint) {
				Expression left = ((GreaterEquationConstraint) aux).getLeft();
				Expression right = ((GreaterEquationConstraint) aux).getRight();
				res = new LowerEqualsEquationConstraint(left, right);
			} else if (aux instanceof LowerEquationConstraint) {
				Expression left = ((LowerEquationConstraint) aux).getLeft();
				Expression right = ((LowerEquationConstraint) aux).getRight();
				res = new GreaterEquationConstraint(left, right);
			} else if (aux instanceof LowerEqualsEquationConstraint) {
				Expression left = ((LowerEqualsEquationConstraint) aux).getLeft();
				Expression right = ((LowerEqualsEquationConstraint) aux).getRight();
				res = new GreaterEqualsEquationConstraint(left, right);
			} else if (aux instanceof EqualEquationConstraint) {
				Expression left = ((EqualEquationConstraint) aux).getLeft();
				Expression right = ((EqualEquationConstraint) aux).getRight();
				res = new NotEqualsEquationConstraint(left, right);
			} else if (aux instanceof NotEqualsEquationConstraint) {
				Expression left = ((NotEqualsEquationConstraint) aux).getLeft();
				Expression right = ((NotEqualsEquationConstraint) aux).getRight();
				res = new EqualEquationConstraint(left, right);
			}
		}
		return res;
	}

	private Constraint reduceNotConstraint(Constraint cons) {
		Constraint res = cons;
		if (cons instanceof NotConstraint) {
			Constraint aux = ((NotConstraint) cons).getContent();
			if (aux instanceof ParenthesisConstraint) {
				res = reduceNotConstraintLevelTwo(((ParenthesisConstraint) aux).getContent());
			} else {
				res = reduceNotConstraintLevelTwo(aux);
				if (res == null) {
					res = cons;
				}
			}
		} else if (cons instanceof ParenthesisConstraint) {
			res = reduceNotConstraint(((ParenthesisConstraint) cons).getContent());
		} else {
			for (int i = 0; i < res.getConstraintSubParts().size(); i++) {
				res.getConstraintSubParts().set(i, reduceNotConstraint(res.getConstraintSubParts().get(i)));
			}
		}
		return res;
	}

	private void addGroups(Feature feature) {
		for (int i = 0; i < feature.getChildren().size(); i++) {
			addGroupConstraint(feature.getChildren().get(i));
		}

	}

	// restricción children >=parent
	// Clonables: Si a alguien se le ocurre, tendríamos que poner las clonables
	// ya se ha ejecutado addIndependentChildren, así que deberían de estar ya
	// registradas en el problema.
	private void addMandatoryChildren(Feature parentFeature) {
		Integer parentIndex = problem.getIndex(parentFeature);
		List<Group> featureGroup = parentFeature.getChildren();
		for (int i = 0; i < featureGroup.size(); i++) {
			if (featureGroup.get(i).GROUPTYPE == GroupType.MANDATORY) {
				// up-uc<=0
				// hay que buscar al padre
				Double childRange;
				Double parentRange;
				if (isNumerical(parentFeature)) {
					parentRange = getFeatureRange(parentFeature).doubleValue();
				} else {
					parentRange = 1d;
				}
				for (int j = 0; j < featureGroup.get(i).getFeatures().size(); j++) {
					// List<Term> listTerm = new LinkedList<Term>();
					Feature childFeature = featureGroup.get(i).getFeatures().get(j);
					if (!isClonable(childFeature)) {
						Integer childIndex = problem.getIndex(childFeature);
						generateMandatoryParentChildrenConstraint(childFeature, childIndex, parentRange, parentIndex);
					} else {
						// sacamos la lista de características asociadas a esa clonable
						List<Feature> clonList = clonableAndClonListRegistry.get(childFeature);
						for (int k = 0; k < clonList.size(); k++) {
							Feature clonFeature = clonList.get(k);
							Integer clonIndex = problem.getIndex(clonFeature);
							generateMandatoryParentChildrenConstraint(clonFeature, clonIndex, parentRange, parentIndex);
						}
					}
				}
			}
		}
	}

	private void generateMandatoryParentChildrenConstraint(Feature childFeature, Integer childIndex, Double parentRange,
			Integer parentIndex) {
		List<Term> listTerm = new LinkedList<Term>();
		Double childRange;
		if (isNumerical(childFeature)) {
			if (!problem.isBounded(childIndex)) {
				addBoundingConstraints(childIndex, childFeature);
			}
			childRange = getFeatureRange(childFeature).doubleValue();
		} else {
			childRange = 1d;
		}
		if (parentRange > childRange) {
			// up-(UBp-LBp+1)*uc<=0
			listTerm.add(new Term(1d, parentIndex));
			listTerm.add(new Term((parentRange + 1) * (-1), childIndex));
		} else {
			// up-uc<=0
			listTerm.add(new Term(1d, parentIndex));
			listTerm.add(new Term(-1d, childIndex));
		}
		problem.addConstraint(new LinearConstraint(listTerm, 0, Comparator.LowerOrEqual));
	}

	private Boolean isNumerical(Feature f) {
		String[] featureNameLines = f.toString().split("\n");

		return (f.getFeatureType() == FeatureType.INT) || (f.getFeatureType() == FeatureType.REAL)
				|| (featureNameLines[0].contains("Integer"));
	}

	private Boolean isClonable(Feature f) {
		String[] featureNameLines = f.toString().split("\n");
		Boolean res = featureNameLines[0].contains("cardinality");
		return res;
	}

	private Integer getFeatureRange(Feature f) {
		Integer res = 1;
		if (isNumerical(f) && f.getLowerBound() != null && f.getUpperBound() != null) {
			Integer lowerBound = Integer.parseInt(f.getLowerBound());
			Integer upperBound = Integer.parseInt(f.getUpperBound());
			res = upperBound - lowerBound + 1;
		}
		return res;
	}

	private List<Feature> getChildrenList(Feature parent) {
		List<Feature> res = new LinkedList<Feature>();
		for (int i = 0; i < parent.getChildren().size(); i++) {
			Group group = parent.getChildren().get(i);
			res.addAll(group.getFeatures());
		}

		return res;
	}

	private Boolean hasClonableAncestor(Feature f) {
		Boolean res = false;

		if (!f.equals(model.getRootFeature())) {
			if (isClonable(f.getParentFeature())) {
				res = true;
			} else {
				res = hasClonableAncestor(f.getParentFeature());
			}
		}
		return res;
	}

	private Feature getClonableAncestor(Feature f) {
		if (f.getParentFeature().equals(model.getRootFeature())) {
			return null;
		} else if (isClonable(f.getParentFeature())) {
			return f.getParentFeature();
		} else {
			return getClonableAncestor(f.getParentFeature());
		}
	}

	// parent-children relationship children <= parent para todos los hijos
	private void addIndependentChildren(Feature parent, Integer parentIndex) {
		for (int i = 0; i < parent.getChildren().size(); i++) {
			if (parent.getChildren().get(i).GROUPTYPE == GroupType.OPTIONAL
					|| parent.getChildren().get(i).GROUPTYPE == GroupType.MANDATORY
					|| parent.getChildren().get(i).GROUPTYPE == GroupType.OR
					|| parent.getChildren().get(i).GROUPTYPE == GroupType.ALTERNATIVE
					|| parent.getChildren().get(i).GROUPTYPE == GroupType.GROUP_CARDINALITY) {
				List<Feature> optionalFeatures = parent.getChildren().get(i).getFeatures();
				for (int j = 0; j < optionalFeatures.size(); j++) {
					Double parentRange;
					Feature child = optionalFeatures.get(j);
					int childIndex;// = problem.getIndex(child);
					if (isNumerical(parent)) {
						parentRange = getFeatureRange(parent).doubleValue();
					} else {
						parentRange = 1d;
					}
					if (isClonable(child)) {
						// System.out.println("Se añaden un clon "+child.getFeatureName());
						int upperBound = Integer.parseInt(child.getUpperBound());
						List<Feature> clonList;
						// ¿Está registrada la clonable en el problema?
						if (clonableAndClonListRegistry.containsKey(child)) {
							clonList = clonableAndClonListRegistry.get(child);
						} else {
							clonList = new LinkedList<Feature>();
						}
						for (int k = 1; k <= upperBound; k++) {
							// se crea una característica clonada
							Feature clonedFeature = child.clone();
							clonedFeature.setFeatureName(child.getFeatureName() + "_" + k);
							// se registra en el problema
							clonedFeatureRegistry.putIfAbsent(child.getFeatureName() + "_" + k, clonedFeature);//
							if (!clonList.contains(clonedFeature))
								clonList.add(clonedFeature);
							clonAndClonableRegistry.put(clonedFeature, child);
							childIndex = problem.getIndex(clonedFeature);
							generateIndependentChildConstraint(clonedFeature, parentIndex, childIndex, parentRange);
						}
						// se actualiza la lista de clones asociadas.
						clonableAndClonListRegistry.put(child, clonList);
					} else {
						childIndex = problem.getIndex(child);
						generateIndependentChildConstraint(child, parentIndex, childIndex, parentRange);
					}
				}
			}
		}
	}

	private void generateIndependentChildConstraint(Feature child, int parentIndex, int childIndex,
			Double parentRange) {
		List<Term> listTerm;
		Double childRange;
		// System.out.println("Se añade rango para "+child.getFeatureName());
		if (isNumerical(child)) {
			childRange = getFeatureRange(child).doubleValue();
			if (!problem.isBounded(childIndex)) {
				addBoundingConstraints(childIndex, child);
			}
		} else {
			childRange = 1d;
			if (!problem.isBounded(childIndex)) {
				problem.addBoundingConstraint(childIndex, 0, 1);
			}
		}
		if (childRange > parentRange) {
			// uc-(UBc-LBc+1)*up<=0
			listTerm = new LinkedList<Term>();
			listTerm.add(new Term(1d, childIndex));
			listTerm.add(new Term((-1) * (childRange + 1), parentIndex));
		} else {
			// uc-up<=0
			listTerm = new LinkedList<Term>();
			listTerm.add(new Term(1d, childIndex));
			listTerm.add(new Term(-1d, parentIndex));
		}
		problem.addConstraint(new LinearConstraint(listTerm, 0, Comparator.LowerOrEqual));
	}

	private Boolean isAGroup(Group g) {
		return g.GROUPTYPE == GroupType.ALTERNATIVE || g.GROUPTYPE == GroupType.OR
				|| g.GROUPTYPE == GroupType.GROUP_CARDINALITY;
	}

	private List<Feature> getFeatureListWithClons(Group g) {
		List<Feature> res = new LinkedList<Feature>();
		for (int i = 0; i < g.getFeatures().size(); i++) {
			if (isClonable(g.getFeatures().get(i))) {
				res.addAll(clonableAndClonListRegistry.get(g.getFeatures().get(i)));
			} else {
				res.add(g.getFeatures().get(i));
			}
		}
		return res;
	}

	// Método para incluir restricciones de grupo.
	private void addGroupConstraint(Group group) {
		if (isAGroup(group)) {
			List<Integer> groupVariables = new LinkedList<Integer>();
			List<Feature> groupFeatureList = getFeatureListWithClons(group);
			// se añaden las clonables a la lista.
			for (int i = 0; i < groupFeatureList.size(); i++) {
				Feature child = groupFeatureList.get(i);
				int uIndex = problem.getIndex(child);
				if (!problem.isBounded(uIndex)) {
					problem.addBoundingConstraint(uIndex, 0, 1);
				}
				List<Term> termList = new LinkedList<Term>();
				if (isNumerical(child)) {
					// se añade una variable ficticia z
					int zIndex = problem.getIndex(child.getFeatureName() + "_z");
					if (!problem.isBounded(zIndex)) {
						problem.addBoundingConstraint(zIndex, 0, 1);
					}
					groupVariables.add(zIndex);
					// se añade una constraint que relaciona la variable ficticia con la real.
					// real-M*ficticia<=0
					termList = new LinkedList<Term>();
					termList.add(new Term(1d, uIndex));
					termList.add(new Term(-bigM, zIndex));
					LinearConstraint lc = new LinearConstraint(termList, 0, Comparator.LowerOrEqual);
					problem.addConstraint(lc);
				} else {
					groupVariables.add(uIndex);
				}
			}
			// En groupVarialbes tenemos los índices de la variables que formaran la
			// constraint grupal
			List<Term> termN = new LinkedList<Term>();
			List<Term> termM = new LinkedList<Term>();
			for (int i = 0; i < groupVariables.size(); i++) {
				termN.add(new Term(-1d, groupVariables.get(i)));
				termM.add(new Term(1d, groupVariables.get(i)));
			}
			// se añade el padre a la constraint
			Integer parentIndex = problem.getIndex(group.getParentFeature());
			if (!problem.isBounded(parentIndex)) {
				addBoundingConstraints(parentIndex, group.getParentFeature());
			}
			Double upperBound = 1d;
			if (group.GROUPTYPE == GroupType.ALTERNATIVE) {
				upperBound = 1d;
			} else if (group.GROUPTYPE == GroupType.OR) {
				upperBound = Double.parseDouble(groupVariables.size() + "");
			} else if (group.GROUPTYPE == GroupType.GROUP_CARDINALITY) {
				upperBound = Double.parseDouble(group.getUpperBound());
			}
			if (isNumerical(group.getParentFeature())) {
				// se añade variable ficticia
				int zIndex = problem.getIndex(group.getParentFeature().getFeatureName() + "_z");
				problem.addBoundingConstraint(zIndex, 0, 1);
				groupVariables.add(zIndex);
				List<Term> termList = new LinkedList<Term>();
				termList.add(new Term(1d, parentIndex));
				termList.add(new Term(-bigM, zIndex));
				problem.addConstraint(new LinearConstraint(termList, 0, Comparator.LowerOrEqual));
				termM.add(new Term(-1 * upperBound, zIndex));
			} else {
				termM.add(new Term(-1 * upperBound, parentIndex));
				termN.add(new Term(1d, parentIndex));
			}
			// sum u_i >= n
			LinearConstraint lcN = new LinearConstraint(termN, 0, Comparator.LowerOrEqual);
			problem.addConstraint(lcN);
			LinearConstraint lcM = new LinearConstraint(termM, 0, Comparator.LowerOrEqual);
			problem.addConstraint(lcM);
		}

	}

	private void addBoundingConstraints(Integer featureIndex, Feature feature) {
		int upperBound = 1, lowerBound = 0;

		// se obtienen los boundings
		if (feature.getUpperBound() != null && feature.getLowerBound() != null) {

			upperBound = Integer.parseInt(feature.getUpperBound());
			lowerBound = Integer.parseInt(feature.getLowerBound());
		} else {
			List<Constraint> auxConstList = new LinkedList<Constraint>();
			auxConstList.addAll(model.getConstraints());
			for (int i = 0; i < auxConstList.size(); i++) {
				if (isLowerBoundConstraint(feature, auxConstList.get(i))) {
					lowerBound = getLowerBoundConstraintNumber(feature, auxConstList.get(i)).intValue();
				}
				if (isUpperBoundConstraint(feature, auxConstList.get(i))) {
					upperBound = getUpperBoundConstraintNumber(feature, auxConstList.get(i)).intValue();
				}
			}
		}
		if (lowerBound != 0) {
			upperBound = upperBound - lowerBound + 1;
		}
		problem.addBoundingConstraint(featureIndex, 0, upperBound);
	}

	private Double getUpperBoundConstraintNumber(Feature feature, Constraint cons) {
		Double res = 1d;
		Expression left, right;
		if (cons instanceof GreaterEqualsEquationConstraint) {
			left = ((GreaterEqualsEquationConstraint) cons).getLeft();
			right = ((GreaterEqualsEquationConstraint) cons).getRight();
			if (right instanceof LiteralExpression && left instanceof NumberExpression) {
				if (((LiteralExpression) right).getFeature().equals(feature)) {
					res = ((NumberExpression) left).getNumber();
				}
			}
		} else if (cons instanceof GreaterEquationConstraint) {
			left = ((GreaterEquationConstraint) cons).getLeft();
			right = ((GreaterEquationConstraint) cons).getRight();
			if (right instanceof LiteralExpression && left instanceof NumberExpression) {
				if (((LiteralExpression) right).getFeature().equals(feature)) {
					res = ((NumberExpression) left).getNumber();
				}
			}
		} else if (cons instanceof LowerEqualsEquationConstraint) {
			left = ((LowerEqualsEquationConstraint) cons).getLeft();
			right = ((LowerEqualsEquationConstraint) cons).getRight();
			if (left instanceof LiteralExpression && right instanceof NumberExpression) {
				if (((LiteralExpression) left).getFeature().equals(feature)) {
					res = ((NumberExpression) right).getNumber();
				}
			}
		} else if (cons instanceof LowerEquationConstraint) {
			left = ((LowerEquationConstraint) cons).getLeft();
			right = ((LowerEquationConstraint) cons).getRight();
			if (left instanceof LiteralExpression && right instanceof NumberExpression) {
				if (((LiteralExpression) left).getFeature().equals(feature)) {
					res = ((NumberExpression) right).getNumber();
				}
			}
		}

		return res;
	}

	private Boolean isUpperBoundConstraint(Feature feature, Constraint cons) {
		Boolean res = false;
		Expression left, right;
		if (cons instanceof GreaterEqualsEquationConstraint) {
			left = ((GreaterEqualsEquationConstraint) cons).getLeft();
			right = ((GreaterEqualsEquationConstraint) cons).getRight();
			if (right instanceof LiteralExpression && left instanceof NumberExpression) {
				if (((LiteralExpression) right).getFeature().equals(feature)) {
					res = true;
				}
			}
		} else if (cons instanceof GreaterEquationConstraint) {
			left = ((GreaterEquationConstraint) cons).getLeft();
			right = ((GreaterEquationConstraint) cons).getRight();
			if (right instanceof LiteralExpression && left instanceof NumberExpression) {
				if (((LiteralExpression) right).getFeature().equals(feature)) {
					res = true;
				}
			}
		} else if (cons instanceof LowerEqualsEquationConstraint) {
			left = ((LowerEqualsEquationConstraint) cons).getLeft();
			right = ((LowerEqualsEquationConstraint) cons).getRight();
			if (left instanceof LiteralExpression && right instanceof NumberExpression) {
				if (((LiteralExpression) left).getFeature().equals(feature)) {
					res = true;
				}
			}
		} else if (cons instanceof LowerEquationConstraint) {
			left = ((LowerEquationConstraint) cons).getLeft();
			right = ((LowerEquationConstraint) cons).getRight();
			if (left instanceof LiteralExpression && right instanceof NumberExpression) {
				if (((LiteralExpression) left).getFeature().equals(feature)) {
					res = true;
				}
			}
		}
		return res;
	}

	private Boolean isLowerBoundConstraint(Feature feature, Constraint cons) {
		Boolean res = false;
		Expression left, right;
		if (cons instanceof GreaterEqualsEquationConstraint) {
			left = ((GreaterEqualsEquationConstraint) cons).getLeft();
			right = ((GreaterEqualsEquationConstraint) cons).getRight();
			if (left instanceof LiteralExpression && right instanceof NumberExpression) {
				if (((LiteralExpression) left).getFeature().equals(feature)) {
					res = true;
				}
			}
		} else if (cons instanceof GreaterEquationConstraint) {
			left = ((GreaterEquationConstraint) cons).getLeft();
			right = ((GreaterEquationConstraint) cons).getRight();
			if (left instanceof LiteralExpression && right instanceof NumberExpression) {
				if (((LiteralExpression) left).getFeature().equals(feature)) {
					res = true;
				}
			}
		} else if (cons instanceof LowerEqualsEquationConstraint) {
			left = ((LowerEqualsEquationConstraint) cons).getLeft();
			right = ((LowerEqualsEquationConstraint) cons).getRight();
			if (right instanceof LiteralExpression && left instanceof NumberExpression) {
				if (((LiteralExpression) right).getFeature().equals(feature)) {
					res = true;
				}
			}
		} else if (cons instanceof LowerEquationConstraint) {
			left = ((LowerEquationConstraint) cons).getLeft();
			right = ((LowerEquationConstraint) cons).getRight();
			if (right instanceof LiteralExpression && left instanceof NumberExpression) {
				if (((LiteralExpression) right).getFeature().equals(feature)) {
					res = true;
				}
			}
		}
		return res;
	}

	private Double getLowerBoundConstraintNumber(Feature feature, Constraint cons) {
		Double res = 0d;
		Expression left, right;
		if (cons instanceof GreaterEqualsEquationConstraint) {
			left = ((GreaterEqualsEquationConstraint) cons).getLeft();
			right = ((GreaterEqualsEquationConstraint) cons).getRight();
			if (left instanceof LiteralExpression && right instanceof NumberExpression) {
				if (((LiteralExpression) left).getFeature().equals(feature)) {
					res = ((NumberExpression) right).getNumber();
				}
			}
		} else if (cons instanceof GreaterEquationConstraint) {
			left = ((GreaterEquationConstraint) cons).getLeft();
			right = ((GreaterEquationConstraint) cons).getRight();
			if (left instanceof LiteralExpression && right instanceof NumberExpression) {
				if (((LiteralExpression) left).getFeature().equals(feature)) {
					res = ((NumberExpression) right).getNumber();
				}
			}
		} else if (cons instanceof LowerEqualsEquationConstraint) {
			left = ((LowerEqualsEquationConstraint) cons).getLeft();
			right = ((LowerEqualsEquationConstraint) cons).getRight();
			if (right instanceof LiteralExpression && left instanceof NumberExpression) {
				if (((LiteralExpression) right).getFeature().equals(feature)) {
					res = ((NumberExpression) left).getNumber();
				}
			}
		} else if (cons instanceof LowerEquationConstraint) {
			left = ((LowerEquationConstraint) cons).getLeft();
			right = ((LowerEquationConstraint) cons).getRight();
			if (right instanceof LiteralExpression && left instanceof NumberExpression) {
				if (((LiteralExpression) right).getFeature().equals(feature)) {
					res = ((NumberExpression) left).getNumber();
				}
			}
		}
		return res;
	}

	public void getFeatures(Feature feature, List<Feature> featureList) {
		for (Group group : feature.getChildren()) {
			for (Feature childFeature : group.getFeatures()) {
				featureList.add(childFeature);
				getFeatures(childFeature, featureList);
			}
		}
	}

	public void readConfiguration(String resFile) {
		try {
			BufferedReader br = new BufferedReader(new FileReader(resFile));
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
				resList.put(problem.getVariables().get(index), number.intValue());// se asigna a cada característica su
																					// valor.
				// System.out.println(variables.get(i)+":"+texto);
				texto = br.readLine();
				index++;
			}
			// visualización de los resultados.
			// TO-DO: generar configuración de UVLS
//			for (int j = 0; j < variables.size(); j++) {
//				// Se extrae el nombre del objeto en su estructura.
//				Object name = mIDToName.get(variables.get(j));
//				if (name instanceof String) {
//					// se obtiene el elemento intencional
//					/*IStarEntity entity = goalModel.getEntity((String) name);
//					if (entity != null) {
//						System.out.println(
//								entity.getText() + "(" + variables.get(j) + ")" + ":" + resList.get(variables.get(j)));
//					}*/
//				} else {
//					String featureName = featureModel.getName((Integer) name);
//					if (featureName != null) {
//						System.out.println(
//								featureName + "(" + variables.get(j) + ")" + ":" + resList.get(variables.get(j)));
//					} else {
//						System.out.println("Index de la variable ficticia " + variables.get(j) + " y nombre "
//								+ mIDToName.get(variables.get(j)));
//
//					}
//				}
//			}
//			br.close();
		} catch (FileNotFoundException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}

	private Integer getBranchId(Feature fea) {
		Integer res = null;
		if (isClon(fea)) {
			String name = fea.getFeatureName();
			String[] elements = name.split("_");
			try {
				res = Integer.parseInt(elements[elements.length - 1]);
			} catch (NumberFormatException e) {
				res = null;
			}
		}
		return res;
	}

	private void writeFile(PrintWriter printer, HashMap<Integer, Integer> resList,
			HashMap<Feature, HashMap<Integer, HashMap<String, Integer>>> clonConf) {
		List<Feature> regClonableList = new LinkedList<Feature>();
		HashMap<Integer, HashMap<String, Integer>> subTreeConf;
		HashMap<String, Integer> branchConf;
		Integer[] resListKey = resList.keySet().toArray(new Integer[resList.size()]);

		for (int j = 0; j < resListKey.length; j++) {
			Object var = problem.getNameFromID(resListKey[j]);
			if (var instanceof Feature) {

				Feature feature = ((Feature) var);
				if (!isClon(feature)) {
					String featureName = ((Feature) var).getFeatureName();
					if (isNumerical(feature)) {
						List<Feature> childrenFeatures = getChildrenList((Feature) var);

						printer.println("\t\t\"" + featureName + "\": [");

						// for para cada item dentro del feature cardinality
						for (int k = 0; k < childrenFeatures.size(); k++) {
							printer.println("\t\t\t{");
							// tengo duda de si aunque este en un group cardinality, en el res viene la
							// configuracion de su hijo en forma consecutiva
							// es decir, si puedo seguir leyendo los valores de j y por tanto es correcto
							// meterle el j++
							printer.println(
									"\t\t\t\t\"" + featureName + "\": " + resList.get(problem.getVariables().get(j)));
							// si es el último valor no añada la coma al final
							if (k == childrenFeatures.size() - 1) {
								printer.print("\t\t\t}");
							} else {
								printer.print("\t\t\t},");
							}
							j++;
						}
						printer.println("\t\t],");
					} else {
						Integer iValue = resList.get(resListKey[j]);
						String sValue;

						if (iValue == 0) {
							sValue = "false";
						} else {
							sValue = "true";
						}

						if (j == resListKey.length - 1) {
							printer.println("\t\t\"" + featureName + "\": " + sValue);
						} else {
							printer.println("\t\t\"" + featureName + "\": " + sValue + ",");
						}
					}
				} else {
					Feature oriFea = clonAndClonableRegistry.get(feature);
					if (isClonable(oriFea)) {
						// ¿se ha registrado el subarbol asociado a la clonable en la configuración?
						if (!regClonableList.contains(oriFea)) {
							// contador de características que vamos a añadir
							int feaCounter = 0;
							// la añadimos al registro de añadidas.
							regClonableList.add(oriFea);
							// añadimos el subarbol al fichero de resultado.
							printer.println("\t\t\"" + oriFea.getFeatureName() + "\": [");
							// recuperamos el subarbol

							subTreeConf = clonConf.get(oriFea);
							// recuperamos las claves
							Integer[] branchKeyArray = subTreeConf.keySet().toArray(new Integer[subTreeConf.size()]);
							for (int a = 0; a < branchKeyArray.length; a++) {
								Integer bId = branchKeyArray[a];
								branchConf = subTreeConf.get(bId);
								String[] feaIter = branchConf.keySet().toArray(new String[branchConf.size()]);
								printer.println("\t\t\t{");
								// no está preparado para numéricas.
								for (int b = 0; b < feaIter.length; b++) {
									String feaName = feaIter[b];
									Integer value = branchConf.get(feaName);
									String conVal = (value == 1 ? "true" : "false");
									String term = (b == feaIter.length - 1 ? "\": " + conVal : "\": " + conVal + ",");
									printer.println("\t\t\t\t\"" + feaName + term);
									feaCounter++;
								}
								// para el último elemento no va una coma.
								if (a != branchKeyArray.length - 1) {
									printer.println("\t\t\t},");
								} else {
									printer.println("\t\t\t}");
								}
							}
							// en la última línea no va una coma
							if (j == resListKey.length - 1) {
								printer.println("\t\t]");
							} else {
								printer.println("\t\t],");
							}
						}
					}
				}
			}
		}
		// cierre del fichero
		printer.println("\t}");
		printer.println("}");
	}

	private HashMap<Feature, Double> getConfiguration(String resFile) throws IOException {
		HashMap<Feature, Double> res = new HashMap<Feature, Double>();
		BufferedReader br = new BufferedReader(new FileReader(resFile));
		int index = 0;
		String texto = br.readLine();
		while (texto != null && index < problem.getVariables().size()) {
			if (texto.startsWith("-")) {
				texto = texto.substring(1);
			}
			Double number = Double.parseDouble(texto);
			Integer id = problem.getVariables().get(index);
			Object obj = problem.getNameFromID(id);
			if (obj instanceof Feature) {
				res.put((Feature) obj, number);
			}
			index++;
			texto = br.readLine();
		}
		br.close();
		return res;
	}

	private Feature getFeatureFromString(String featureName) {
		Feature res = null;
		Boolean end = false;
		int index = 0;
		Feature fea;
		Object[] objects = problem.getProblemObject();
		while (index < objects.length && !end) {
			if (objects[index] instanceof Feature) {
				fea = (Feature) objects[index];
				if (fea.getFeatureName().equals(featureName)) {
					res = fea;
					end = true;
				}
			}
			index++;
		}

		return res;
	}

	private Feature getFeatureFromString(String name, HashMap<Feature, Double> resConf) {
		//String original=name;
		//System.out.println("Se llama a getFeatureFromString con "+name);
		name = name.trim();
		String regex = "\"|(?i)\\b(cardinality|integer)\\b|\\[\\s*[^\\[\\]]+?\\s*\\]";
		name = name.replaceAll(regex, "");
		name = name.trim().replaceAll("\\s*\\{.*?\\}\\s*$", "");
		//System.out.println("Tras transformar: "+name);
		Feature res = null;
		Iterator<Feature> featureIter = resConf.keySet().iterator();
		Feature aux;
		Boolean end = false;
		while (featureIter.hasNext() && !end) {
			aux = featureIter.next();
			if (aux.getFeatureName().equals(name)) {
				res = aux;
				end = true;
			}
		}
		// si la característica no está en la configuración es una clonable.
		if(!end) {
			Iterator<Feature> iter=clonableAndClonListRegistry.keySet().iterator();
			while(iter.hasNext() && !end) {
				aux=iter.next();
				if(aux.getFeatureName().equals(name)) {
					end=true;
					res=aux;
				}
			}
		}
		//System.out.println("Se asigna a "+res.getFeatureName());
		return res;
	}

	// fea is a clon, so it is a the real feature that has assigned value in the
	// configuration.
	private String composeJSONEntryClonChild(Feature fea, HashMap<Feature, Double> resConf) {
		String res = "";
		String branchId = getBranchId(fea).toString();
		List<Feature> children = getChildrenList(fea);
		for (Feature child : children) {
			String childName = child.getFeatureName() + "_" + branchId;
			Feature childClon = getFeatureFromString(childName, resConf);
			Double value = resConf.get(childClon);
			if (child.getFeatureName().contains(" ")) {
				childName = "\"\\\"" + child.getFeatureName() + "\\\"\"";
			} else {
				childName = "\"" + child.getFeatureName() + "\"";
			}
			res = res + "        " + childName + ":"
					+ (isNumerical(child) ? value.toString() : (value == 0 ? "false,\n" : "true,\n"));
			if (getChildrenList(childClon).size() > 0) {
				composeJSONEntryClonChild(childClon, resConf);
			}
		}
		return res;
	}

	private String composeJSONEntry(String line, HashMap<Feature, Double> resConf) {
		String res = "";
		Feature fea = getFeatureFromString(line, resConf);
		if(fea==null)System.out.println(line);
		if (isClon(fea))
			fea = clonAndClonableRegistry.get(fea);
		String featureName;
		if (fea.getFeatureName().contains(" ")) {
			featureName = "\"\\\"" + fea.getFeatureName() + "\\\"\"";
		} else {
			featureName = "\"" + fea.getFeatureName() + "\"";
		}
		// ¿Es una clonable?
		if (isClonable(fea)) {
			res = featureName + ": [\n";
			List<Feature> clonList = clonableAndClonListRegistry.get(fea);
			List<Feature> children = getChildrenList(fea);
			for (int i = 1; i <= clonList.size(); i++) {
				res = res + "      {\n";
				
				String childClonName = fea.getFeatureName() + "_" + i;
				Feature clon = getFeatureFromString(childClonName, resConf);
				if(clon==null)System.out.println(childClonName);
				Double value = resConf.get(clon);
				
				res = res + "        " + featureName + ":"
						+ (isNumerical(fea) ? value.toString() : (value == 0 ? "false,\n" : "true,\n"));
				for (Feature child : children) {
					childClonName = child.getFeatureName() + "_" + i;
					clon = getFeatureFromString(childClonName, resConf);
					value = resConf.get(clon);
					String childName;
					if (child.getFeatureName().contains(" ")) {
						childName = "\"\\\"" + child.getFeatureName() + "\\\"\"";
					} else {
						childName = "\"" + child.getFeatureName() + "\"";
					}
					res = res + "        " + childName + ":"
							+ (isNumerical(fea) ? value.toString() : (value == 0 ? "false,\n" : "true,\n"));
					// se añaden los descendientes de child
					if (getChildrenList(clon).size() > 0) {
						res = res + composeJSONEntryClonChild(clon, resConf);
					}
				}
				res = res.substring(0, res.length() - 2) + "\n";
				res = res + "      },\n";
			}
			res = res.substring(0, res.length() - 2) + "\n";
			res = res + "    ]";
		} else if (hasClonableAncestor(fea)) {
			res = "";
		} else {
			Double value = resConf.get(fea);
			res = featureName + ":" + (isNumerical(fea) ? value.toString() : (value == 0 ? "false" : "true"));
		}
		return res;
	}

	// the order for the elements to appear in the file is determined by their
	// apearance in the UVL file.
	// resFile archivo del resultado en Matlab
	// outputFile archivo json donde se escribirá el resultado de la configuración.
	public void writeConfiguration(String resFile, String outputFile) {
		try {
			PrintWriter printer = new PrintWriter(outputFile);
			HashMap<Feature, Double> resConf = getConfiguration(resFile);
			BufferedReader reader = new BufferedReader(new FileReader(featureModelFile));
			// The first line is the word feature, we ignore that line.
			reader.readLine();
			// We print the preamble of the document.
			printer.println("{");
			String spaces = "  ";
			printer.println(spaces + "\"file\": \"" + featureModelFile + "\",");
			printer.println(spaces + "\"config\": {");

			String line = reader.readLine();

			String toBePrinted = "";
			spaces = spaces + "  ";
			while (!line.trim().equals("constraints")) {

				if (!ignoreList.contains(line.trim())) {
					// line contiene una línea del fichero uvl
					
					String newPart = composeJSONEntry(line, resConf);
					if (!newPart.equals(""))
						toBePrinted = toBePrinted + spaces + newPart + ",\n";
				}
				line = reader.readLine();
				if (line == null) {
					break;
				}

			}
			toBePrinted = toBePrinted.substring(0, toBePrinted.length() - 2) + "\n";
			printer.print(toBePrinted);
			printer.println("  " + "}");
			printer.println("}");
			reader.close();
			printer.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
	}

	/*
	 * public void writeConfigurationToFile(String resFile, String conFile, String
	 * featureModelName) {
	 * 
	 * try { HashMap<Feature, HashMap<Integer, HashMap<String, Integer>>> clonConf =
	 * new HashMap<Feature, HashMap<Integer, HashMap<String, Integer>>>();
	 * HashMap<Integer, HashMap<String, Integer>> subTreeConf; HashMap<String,
	 * Integer> branchConf; PrintWriter printer = new PrintWriter(conFile);
	 * BufferedReader br = new BufferedReader(new FileReader(resFile)); String texto
	 * = br.readLine(); // cada posición de la lista resList se corresponde al valor
	 * de la variable // guardada en esa posición. HashMap<Integer, Integer> resList
	 * = new HashMap<Integer, Integer>();// <Index,Value> int index = 0; while
	 * (texto != null && index < problem.getVariables().size()) { if
	 * (texto.startsWith("-")) { texto = texto.substring(1); } Double number =
	 * Double.parseDouble(texto); Integer id = problem.getVariables().get(index);
	 * Object obj = problem.getNameFromID(id); if (obj instanceof Feature) { if
	 * (isClon((Feature) obj)) { // 1. ¿De quién eres un clon? Feature oriFea =
	 * clonAndClonableRegistry.get((Feature) obj); // 2. ¿Es tu original una
	 * clonable? // si if (isClonable(oriFea)) { // ¿Está registrado en el modelo?
	 * if (clonConf.containsKey(oriFea)) { subTreeConf = clonConf.get(oriFea); }
	 * else { clonConf.put(oriFea, new HashMap<Integer, HashMap<String,
	 * Integer>>()); subTreeConf = clonConf.get(oriFea); } // no } else { // ¿Cuál
	 * es su ancestro clonable?
	 * 
	 * Feature anc = getClonableAncestor(oriFea); // ¿Está registrado en el modelo?
	 * if (clonConf.containsKey(anc)) { subTreeConf = clonConf.get(anc); } else {
	 * clonConf.put(anc, new HashMap<Integer, HashMap<String, Integer>>());
	 * subTreeConf = clonConf.get(anc); } } // ¿Está registrada esa rama? Integer
	 * branchId = getBranchId((Feature) obj); if (subTreeConf.containsKey(branchId))
	 * { branchConf = subTreeConf.get(branchId); } else { branchConf = new
	 * HashMap<String, Integer>(); subTreeConf.put(branchId, branchConf); } //
	 * Añadimos ese valor en la rama branchConf.put(oriFea.getFeatureName(),
	 * number.intValue()); } resList.put(id, number.intValue());// se asigna a cada
	 * característica su // valor. } //
	 * System.out.println(variables.get(i)+":"+texto); texto = br.readLine();
	 * index++; }
	 * 
	 * // visualización de los resultados. // cabecera de fichero
	 * printer.println("{"); printer.println("\t\"file\": " + "\"" +
	 * featureModelName + "\","); printer.println("\t\"config\": {");
	 * writeFile(printer, resList, clonConf); br.close(); printer.close(); } catch
	 * (FileNotFoundException e) { e.printStackTrace(); } catch (IOException e) {
	 * e.printStackTrace(); }
	 * 
	 * }
	 */

	/***
	 * Se añaden todos los descendientes de un clon al problema
	 * 
	 * @param clonable is the original feature from de UVL model
	 * @param clon     is a copy of clonable that has been already add to the
	 *                 problem.
	 */
	private void addClonedBranch(Feature clonable, Feature clon) {
		addClonedChildren(clonable, clon);
		addMandatoryClonedChildren(clonable, clon);
		addClonedGroups(clonable, clon);

	}

	// se añaden los hijos obligatorios
	private void addMandatoryClonedChildren(Feature clonable, Feature clon) {
		String branch_id = clon.getFeatureName().substring(clon.getFeatureName().length() - 1);
		Integer parentIndex = problem.getIndex(clon);
		List<Group> featureGroup = clonable.getChildren();
		for (int i = 0; i < featureGroup.size(); i++) {
			if (featureGroup.get(i).GROUPTYPE == GroupType.MANDATORY) {
				// up-uc<=0
				// hay que buscar al padre
				Double parentRange;
				if (isNumerical(clon)) {
					parentRange = getFeatureRange(clon).doubleValue();
				} else {
					parentRange = 1d;
				}
				for (int j = 0; j < featureGroup.get(i).getFeatures().size(); j++) {
					// List<Term> listTerm = new LinkedList<Term>();
					Feature childFeature = featureGroup.get(i).getFeatures().get(j);
					if (!isClonable(childFeature)) {
						// recuperamos la lista de clones asociada.
						List<Feature> clonList = clonableAndClonListRegistry.get(childFeature);
						// buscamos el clon que termina por branch_id
						Feature clonedChild = getClonedChild(clonList, branch_id);
						Integer childIndex = problem.getIndex(clonedChild);
						generateMandatoryParentChildrenConstraint(childFeature, childIndex, parentRange, parentIndex);
					} else {
						// sacamos la lista de características asociadas a esa clonable
						List<Feature> clonList = clonableAndClonListRegistry.get(childFeature);
						Integer lowerBound = Integer.parseInt(childFeature.getLowerBound());
						if (lowerBound > 0) {
							for (int k = 1; k <= lowerBound; k++) {
								Feature clonFeature = clonList.get(k);
								Integer clonIndex = problem.getIndex(clonFeature);
								generateMandatoryParentChildrenConstraint(clonFeature, clonIndex, parentRange,
										parentIndex);
							}
						}
					}
				}
			}
		}
	}

	private Feature getClonedChild(List<Feature> clonList, String branchId) {
		Feature res = null;
		int index = 0;
		while (index < clonList.size() && res == null) {
			if (clonList.get(index).getFeatureName().endsWith(branchId)) {
				res = clonList.get(index);
			}
			index++;
		}
		return res;
	}

	// se añaden las parenthood relationship de un clon.
	private void addClonedChildren(Feature clonable, Feature clon) {
		String branch_id = getBranchId(clon).toString();// .getFeatureName().substring(clon.getFeatureName().length() -
														// 1);

		for (int i = 0; i < clonable.getChildren().size(); i++) {
			List<Feature> children = clonable.getChildren().get(i).getFeatures();
			for (int j = 0; j < children.size(); j++) {
				// se crea un clon de este hijo
				Feature childClon = children.get(j).clone();
				// se le cambia el nombre.
				String clonName = childClon.getFeatureName().replaceAll("_[0-9]+", "");
				childClon.setFeatureName(clonName + "_" + branch_id);
				// se registra en las estructuras
				// hay clones registrados para esta característica?
				List<Feature> clonList = clonableAndClonListRegistry.getOrDefault(children.get(j),
						new LinkedList<Feature>());
				clonList.add(childClon);
				clonableAndClonListRegistry.put(children.get(j), clonList);
				clonAndClonableRegistry.put(childClon, children.get(j));
				// se añaden las restricciones
				Double parentRange;
				int childIndex = problem.getIndex(childClon);
				if (isNumerical(clon)) {
					parentRange = getFeatureRange(clon).doubleValue();
				} else {
					parentRange = 1d;
				}
				generateIndependentChildConstraint(childClon, problem.getIndex(clon), childIndex, parentRange);
				// llamada recursiva para generar el resto de restricciones
				if (children.get(j).getChildren().size() > 0) {
					addClonedBranch(children.get(j), childClon);
				}
			}
		}
	}

	private void addClonedGroups(Feature clonable, Feature clon) {
		String branch_id = clon.getFeatureName().substring(clon.getFeatureName().length() - 1);
		for (int i = 0; i < clonable.getChildren().size(); i++) {
			if (isAGroup(clonable.getChildren().get(i))) {
				addClonedGroupConstraint(clonable.getChildren().get(i), clon, branch_id);
			}
		}
	}

	// no se consideran clonables dentro de los grupos
	private List<Feature> getClonedGroupFeature(Group g, String branchId) {
		List<Feature> res = new LinkedList<Feature>();
		// 1. Recuperamos la características que forman parte del grupo.
		List<Feature> groupFeatureList = g.getFeatures();
		for (int i = 0; i < groupFeatureList.size(); i++) {
			// 2. Recuperamos todos los clones
			List<Feature> clonList = clonableAndClonListRegistry.get(groupFeatureList.get(i));
			// 3. Buscamos el clon asociado a la rama
			Feature clon = getClonedChild(clonList, branchId);
			// 4. Se añade a la respuesta
			res.add(clon);
		}
		return res;
	}

	// este método solo se llama si group es uno de los grupos que consideramos para
	// añadir.
	private void addClonedGroupConstraint(Group group, Feature clon, String branchId) {
		List<Integer> groupVariables = new LinkedList<Integer>();
		List<Feature> groupFeatureList = getClonedGroupFeature(group, branchId);
		// se añaden las clonables a la lista.
		for (int i = 0; i < groupFeatureList.size(); i++) {
			Feature child = groupFeatureList.get(i);
			int uIndex = problem.getIndex(child);
			if (!problem.isBounded(uIndex)) {
				problem.addBoundingConstraint(uIndex, 0, 1);
			}
			List<Term> termList = new LinkedList<Term>();
			if (isNumerical(child)) {
				// se añade una variable ficticia z
				int zIndex = problem.getIndex(child.getFeatureName() + "_z");
				if (!problem.isBounded(zIndex)) {
					problem.addBoundingConstraint(zIndex, 0, 1);
				}
				groupVariables.add(zIndex);
				// se añade una constraint que relaciona la variable ficticia con la real.
				// real-M*ficticia<=0
				termList = new LinkedList<Term>();
				termList.add(new Term(1d, uIndex));
				termList.add(new Term(-bigM, zIndex));
				LinearConstraint lc = new LinearConstraint(termList, 0, Comparator.LowerOrEqual);
				problem.addConstraint(lc);
			} else {
				groupVariables.add(uIndex);
			}
		}
		// En groupVarialbes tenemos los índices de la variables que formaran la
		// constraint grupal
		List<Term> termN = new LinkedList<Term>();
		List<Term> termM = new LinkedList<Term>();
		for (int i = 0; i < groupVariables.size(); i++) {
			termN.add(new Term(-1d, groupVariables.get(i)));
			termM.add(new Term(1d, groupVariables.get(i)));
		}
		// se añade el padre a la constraint-> que tiene que ser el padre clonado.
		Integer parentIndex = problem.getIndex(clon);
		if (!problem.isBounded(parentIndex)) {
			addBoundingConstraints(parentIndex, clon);
		}
		Double upperBound = 1d;
		if (group.GROUPTYPE == GroupType.ALTERNATIVE) {
			upperBound = 1d;
		} else if (group.GROUPTYPE == GroupType.OR) {
			upperBound = Double.parseDouble(groupVariables.size() + "");
		} else if (group.GROUPTYPE == GroupType.GROUP_CARDINALITY) {
			upperBound = Double.parseDouble(group.getUpperBound());
		}
		if (isNumerical(clon)) {
			// se añade variable ficticia
			int zIndex = problem.getIndex(group.getParentFeature().getFeatureName() + "_z");
			problem.addBoundingConstraint(zIndex, 0, 1);
			groupVariables.add(zIndex);
			List<Term> termList = new LinkedList<Term>();
			termList.add(new Term(1d, parentIndex));
			termList.add(new Term(-bigM, zIndex));
			problem.addConstraint(new LinearConstraint(termList, 0, Comparator.LowerOrEqual));
			termM.add(new Term(-1 * upperBound, zIndex));
		} else {
			termM.add(new Term(-1 * upperBound, parentIndex));
			termN.add(new Term(1d, parentIndex));
		}
		// sum u_i >= n
		LinearConstraint lcN = new LinearConstraint(termN, 0, Comparator.LowerOrEqual);
		problem.addConstraint(lcN);
		LinearConstraint lcM = new LinearConstraint(termM, 0, Comparator.LowerOrEqual);
		problem.addConstraint(lcM);

	}

	private void printClonableAndClonRegistry() {
		Iterator<Feature> iterator = clonableAndClonListRegistry.keySet().iterator();
		while (iterator.hasNext()) {
			Feature feature = iterator.next();
			System.out.println("Original: " + feature);
			System.out.println("Clons");
			List<Feature> clonList = clonableAndClonListRegistry.get(feature);
			for (int i = 0; i < clonList.size(); i++) {
				System.out.println(clonList.get(i).getFeatureName());
			}
		}
	}

	private OrConstraint generateClonDisjunction(Feature fea) {
		OrConstraint res = null;
		if (isClonable(fea) | hasClonableAncestor(fea)) {
			List<Feature> clonList = clonableAndClonListRegistry.get(fea);
			LiteralConstraint lit1 = new LiteralConstraint(clonList.get(0).getFeatureName());
			lit1.setFeature(clonList.get(0));
			LiteralConstraint lit2 = new LiteralConstraint(clonList.get(1).getFeatureName());
			lit2.setFeature(clonList.get(1));
			res = new OrConstraint(lit1, lit2);
			for (int i = 2; i < clonList.size(); i++) {
				OrConstraint aux = res;
				lit1 = new LiteralConstraint(clonList.get(i).getFeatureName());
				lit1.setFeature(clonList.get(i));
				res = new OrConstraint(lit1, aux);
			}
		}
		return res;
	}

	public List<Feature> getClonsFromClonable(String featureName) {
		List<Feature> res = new LinkedList<Feature>();
		Boolean end = false;
		Iterator<Feature> keyIterator = clonableAndClonListRegistry.keySet().iterator();

		while (!end && keyIterator.hasNext()) {
			Feature key = keyIterator.next();
			if (key.getFeatureName().equals(featureName)) {
				res = clonableAndClonListRegistry.get(key);
				end = true;
			}
		}
		return res;
	}
}
