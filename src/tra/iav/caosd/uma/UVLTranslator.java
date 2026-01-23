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
import ilp.iav.caosd.uma.Bounding;
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
	private HashMap<Integer,Bounding> originalBounding=new HashMap<Integer,Bounding>();

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
		// traducción de crostree constraints
		temporalConstraintList.addAll(model.getConstraints());

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
				if (!problem.isBounded(index)) {
					// es numerica
					if (isNumerical(featureList.get(i))) {
						addBoundingConstraints(index, featureList.get(i));
					} else {
						problem.addBoundingConstraint(index, 0, 1);
					}
				}
				// paternity
				addIndependentChildren(featureList.get(i), index);
				// mandatory features
				addMandatoryChildren(featureList.get(i));
				addGroups(featureList.get(i));
			}
		}
		
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
	
	private Boolean isComparisonConstraint(ExpressionConstraint cons) {
		return (cons instanceof GreaterEqualsEquationConstraint)||(cons instanceof GreaterEquationConstraint)||
				 (cons instanceof LowerEqualsEquationConstraint)||(cons instanceof LowerEquationConstraint);
	}
	
	private Boolean isNumericalComparison(ExpressionConstraint cons) {
		Expression left=cons.getLeft();
		Expression right=cons.getRight();
		return ((left instanceof LiteralExpression)&&(right instanceof NumberExpression))||
				((right instanceof LiteralExpression)&&(left instanceof NumberExpression));
	}
	
	// los boundings pueden ser sobre numéricas o atributos, nos quedamos con LiteralExpression para simplificar.
	private LiteralExpression extractLiteral(ExpressionConstraint exp){
		Expression left,right;
		left=exp.getLeft();
		right=exp.getRight();
		LiteralExpression res=null;
		if(left instanceof LiteralExpression) {
			res=((LiteralExpression) left);
		}else if(right instanceof LiteralExpression){
			res=((LiteralExpression)right);
		}
		return res;
	}
	
	private Constraint removeParenthesis(Constraint cons) {
		if(cons instanceof ParenthesisConstraint) {
			cons=((ParenthesisConstraint)cons).getContent();
		}
		return cons;
	}
	
	
	private Boolean isBoundingConstraint(Constraint cons) {
		Boolean res=false;
		if(cons instanceof AndConstraint) {
			Constraint left,right;
			left=((AndConstraint)cons).getLeft();
			right=((AndConstraint)cons).getRight();
			// si la expresión está dentro de un paréntesis (lo habitual) se extrae.
			left=removeParenthesis(left);
			right=removeParenthesis(right);
			// comprobamos que es un AND de expression
			if((left instanceof ExpressionConstraint)&&(right instanceof ExpressionConstraint)) {
				if(isComparisonConstraint((ExpressionConstraint)left) && (isComparisonConstraint((ExpressionConstraint)right))) {
					if(isNumericalComparison((ExpressionConstraint)left) && isNumericalComparison((ExpressionConstraint)right)) {
						LiteralExpression leftExp=extractLiteral((ExpressionConstraint)left);
						LiteralExpression rightExp=extractLiteral((ExpressionConstraint)right);
						res=leftExp.equals(rightExp);
					}
				}
			}
		}
		return res;
	}
	
	private Integer getVariableIndex(AndConstraint cons) {
		Integer res=null;
		LiteralExpression le=null;
		Constraint left=removeParenthesis(cons.getLeft());
		if(left instanceof GreaterEqualsEquationConstraint) {
			// en qué lado está el literal.
			 GreaterEqualsEquationConstraint geec=(GreaterEqualsEquationConstraint)left;
			 if(geec.getLeft() instanceof LiteralExpression) {
				 le=(LiteralExpression)geec.getLeft();
			 }else {
				 le=(LiteralExpression)geec.getRight();
			 }		
		}else if(left instanceof GreaterEquationConstraint) {
			// en qué lado está el literal.
			 GreaterEquationConstraint gec=(GreaterEquationConstraint)left;
			 if(gec.getLeft() instanceof LiteralExpression) {
				 le=(LiteralExpression)gec.getLeft();
			 }else {
				 le=(LiteralExpression)gec.getRight();
			 }
		}else if(left instanceof LowerEqualsEquationConstraint) {
			LowerEqualsEquationConstraint leec=(LowerEqualsEquationConstraint)left;
			if(leec.getLeft() instanceof LiteralExpression) {
				le=(LiteralExpression)leec.getLeft();
			}else {
				le=(LiteralExpression)leec.getRight();
			}
		}else if(left instanceof LowerEquationConstraint) {
			LowerEquationConstraint lec=(LowerEquationConstraint)left;
			if(lec.getLeft() instanceof LiteralExpression) {
				le=(LiteralExpression)lec.getLeft();
			}else {
				le=(LiteralExpression)lec.getRight();
			}
		}
		if (le != null) {
			if (le.getAttribute() == null) {
				res = problem.getIndex(le.getFeature());
				// está establecido sobre un atributo
			} else {
				res = problem.getIndex(le.getAttribute());
			}
		}
		return res;
	}
	
	private void getBounding(Constraint cons,Bounding bound) {
		Double lowerBound=null,upperBound=null;
		
		cons=removeParenthesis(cons);
		if(cons instanceof GreaterEqualsEquationConstraint) {
			// en qué lado está el literal.
			 GreaterEqualsEquationConstraint geec=(GreaterEqualsEquationConstraint)cons;
			 if(geec.getLeft() instanceof LiteralExpression) {
				 lowerBound=((NumberExpression)geec.getRight()).getNumber();
			 }else {
				 upperBound=((NumberExpression)geec.getLeft()).getNumber();
			 }		
		}else if(cons instanceof GreaterEquationConstraint) {
			// en qué lado está el literal.
			 GreaterEquationConstraint gec=(GreaterEquationConstraint)cons;
			 if(gec.getLeft() instanceof LiteralExpression) {
				 lowerBound=((NumberExpression)gec.getRight()).getNumber()+1;
			 }else {
				 upperBound=((NumberExpression)gec.getLeft()).getNumber()-1;
			 }
		}else if(cons instanceof LowerEqualsEquationConstraint) {
			LowerEqualsEquationConstraint leec=(LowerEqualsEquationConstraint)cons;
			if(leec.getLeft() instanceof LiteralExpression) {
				upperBound=((NumberExpression)leec.getRight()).getNumber();
			}else {
				lowerBound=((NumberExpression)leec.getLeft()).getNumber();
			}
		}else if(cons instanceof LowerEquationConstraint) {
			LowerEquationConstraint lec=(LowerEquationConstraint)cons;
			if(lec.getLeft() instanceof LiteralExpression) {
				upperBound=((NumberExpression)lec.getRight()).getNumber()-1;
			}else {
				lowerBound=((NumberExpression)lec.getLeft()).getNumber()+1;
			}
		}
		if(lowerBound!=null)bound.setMin(lowerBound.intValue());
		if(upperBound!=null)bound.setMax(upperBound.intValue());
	}
	
	
	
	private void processBoundingConstraint(AndConstraint cons) {			
		Integer variableIndex=getVariableIndex(cons);
		Bounding bound=new Bounding();
		Integer upperBound=bound.getMax();
		getBounding(cons.getLeft(), bound);
		getBounding(cons.getRight(),bound);
		//System.out.println(variableIndex+" "+bound.toString());
		originalBounding.put(variableIndex, bound);
		if (bound.getMin() != 0) {
			upperBound = upperBound - bound.getMin() + 1;
		}
		problem.addBoundingConstraint(variableIndex, 0, upperBound);
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
				if (!isBoundingConstraint(temporalConstraintList.get(i))) {
					temp = translateFormula(temporalConstraintList.get(i), f);
					transformed = temp.transform(tseitinTrans);
					// System.out.println("Despues: "+transformed);
					// el resultado es una conjunción de OR
					// debemos obtener todas las conjunciones y meterlas una a una.
					transformInLC(transformed.toString());
				}
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
		for(int i=0;i<temporalConstraintList.size();i++) {
			if(isBoundingConstraint(temporalConstraintList.get(i))) {
				Integer consIndex=getVariableIndex((AndConstraint)temporalConstraintList.get(i));
				if(consIndex.equals(featureIndex)) {
					processBoundingConstraint((AndConstraint)temporalConstraintList.get(i));
				}
			}
		}
		
	}

	/*private Double getUpperBoundConstraintNumber(Feature feature, Constraint cons) {
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
	}*/

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
		// String original=name;
		// System.out.println("Se llama a getFeatureFromString con "+name);
		name = name.trim();
		String regex = "\"|(?i)\\b(cardinality|integer)\\b|\\[\\s*[^\\[\\]]+?\\s*\\]";
		name = name.replaceAll(regex, "");
		name = name.trim().replaceAll("\\s*\\{.*?\\}\\s*$", "");
		// System.out.println("Tras transformar: "+name);
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
		if (!end) {
			Iterator<Feature> iter = clonableAndClonListRegistry.keySet().iterator();
			while (iter.hasNext() && !end) {
				aux = iter.next();
				if (aux.getFeatureName().equals(name)) {
					end = true;
					res = aux;
				}
			}
		}
		// System.out.println("Se asigna a "+res.getFeatureName());
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
					+ (isNumerical(child) ? getNotNormalizedValue(child,value) : (value == 0 ? "false,\n" : "true,\n"));
			if (getChildrenList(childClon).size() > 0) {
				composeJSONEntryClonChild(childClon, resConf);
			}
		}
		return res;
	}
	
	private String getNotNormalizedValue(Feature fea,Double value) {
		String res=value.toString();
		Integer index=problem.getIndex(fea);
		if(originalBounding.containsKey(index)) {
			Bounding bound=originalBounding.get(index);
			Double newValue=bound.getMin()+value;
			res=newValue.toString();
		}
		return res;
	}

	private String composeJSONEntry(String line, HashMap<Feature, Double> resConf) {
		String res = "";
		Feature fea = getFeatureFromString(line, resConf);
		if (fea == null)
			System.out.println(line);
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
				if (clon == null)
					System.out.println(childClonName);
				Double value = resConf.get(clon);

				res = res + "        " + featureName + ":"
						+ (isNumerical(fea) ? getNotNormalizedValue(fea, value) : (value == 0 ? "false,\n" : "true,\n"));
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
							+ (isNumerical(child) ? getNotNormalizedValue(child, value) : (value == 0 ? "false,\n" : "true,\n"));
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
			res = featureName + ":" + (isNumerical(fea) ? getNotNormalizedValue(fea, value) : (value == 0 ? "false" : "true"));
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
