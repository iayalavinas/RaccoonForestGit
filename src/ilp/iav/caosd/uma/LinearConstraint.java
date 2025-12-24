package ilp.iav.caosd.uma;

import java.util.List;
import java.util.Objects;


public class LinearConstraint extends ObjectiveFunction{

	private Integer constant;
	private Comparator comparator;// only <= or =
	
	
	public LinearConstraint() {
		super();
		constant=0;
		comparator=Comparator.Equal;
	}
	
	public LinearConstraint(List<Term> l,Integer c,Comparator comp) {
		super.setTerms(l);
		constant=c;
		comparator=comp;
	}
	
	public Integer getConstant() {
		return constant;
	}

	public void setConstant(Integer constant) {
		this.constant = constant;
	}
	
	

	public Comparator getComparator() {
		return comparator;
	}

	public void setComparator(Comparator comparator) {
		this.comparator = comparator;
	}

	

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + Objects.hash(comparator, constant);
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		LinearConstraint other = (LinearConstraint) obj;
		return comparator == other.comparator && Objects.equals(constant, other.constant);
	}

	@Override
	public String toString() {
		List<Term> terms=super.getTerms();
		String res="";
		for(int i=0;i<terms.size();i++) {
			res=res+" "+terms.get(i).toString();
		}
		if(comparator.equals(Comparator.Equal)) {
			res=res+" = "+constant;
		}else if(comparator.equals(Comparator.LowerOrEqual)) {
			res=res+" <= "+constant;
		}else if(comparator.equals(Comparator.HigherOrEqual)) {
			res=res+" >= "+constant;
		}else if(comparator.equals(Comparator.Lower)) {
			res=res+" < "+constant;
		}else {
			res=res+" > "+constant;
		}
		return res.substring(1);
	}
	
	

}
