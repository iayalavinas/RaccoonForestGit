package ctr.iav.caosd.uma;

import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

import ilp.iav.caosd.uma.Comparator;
import ilp.iav.caosd.uma.LinearConstraint;
import ilp.iav.caosd.uma.Term;

public class Filter {
	private Integer id,value;
	
	public Filter(Integer i,Integer v) {
		id=i;
		value=v;
	}

	public Integer getId() {
		return id;
	}

	public void setId(Integer id) {
		this.id = id;
	}

	public Integer getValue() {
		return value;
	}

	public void setValue(Integer value) {
		this.value = value;
	}
	
	public LinearConstraint getLinearConstraint() {
		List<Term> listTerm=new LinkedList<Term>();
		Term term=new Term(1d,id);
		listTerm.add(term);
		LinearConstraint lc=new LinearConstraint(listTerm, value, Comparator.Equal);
		return lc;
	}

	@Override
	public int hashCode() {
		return Objects.hash(id, value);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Filter other = (Filter) obj;
		return Objects.equals(id, other.id) && Objects.equals(value, other.value);
	}

	@Override
	public String toString() {
		return "x_" + id + "=" + value;
	}
	
	


}
