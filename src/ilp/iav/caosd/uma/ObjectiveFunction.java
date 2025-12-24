package ilp.iav.caosd.uma;

import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

public class ObjectiveFunction {

	private List<Term> terms = new LinkedList<Term>();

	public void addTerm(Term t) {
		terms.add(t);
	}
	
	public void addTerm(Double weight,Integer index) {
		terms.add(new Term(weight,index));
	}

	public List<Term> getTerms() {
		return terms;
	}

	public void setTerms(List<Term> terms) {
		this.terms = terms;
	}

	public Boolean containsIndex(Integer index) {
		Boolean res = false;
		int i = 0;
		while (!res && i < terms.size()) {
			if (terms.get(i).getVariableID().equals(index)) {
				res = true;
			}
			i++;
		}
		return res;
	}

	public Double getWeight(Integer index) {
		Double res = null;
		int i = 0;
		while (res == null && i < terms.size()) {
			if (terms.get(i).getVariableID().equals(index)) {
				res = terms.get(i).getWeight();
			}
			i++;
		}
		return res;
	}

	@Override
	public int hashCode() {
		return Objects.hash(terms);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		ObjectiveFunction other = (ObjectiveFunction) obj;
		return Objects.equals(terms, other.terms);
	}

	@Override
	public String toString() {
		if (terms.size() > 0) {
			String res = "";
			for (int i = 0; i < terms.size(); i++) {
				res = res + terms.get(i).toString() + "+";
			}
			return res.substring(0, res.length() - 1);
		} else {
			return "";
		}
	}

}
