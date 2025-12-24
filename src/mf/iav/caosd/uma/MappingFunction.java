package mf.iav.caosd.uma;

import java.util.LinkedList;
import java.util.List;
import java.util.Objects;

import ilp.iav.caosd.uma.Comparator;
import ilp.iav.caosd.uma.LinearConstraint;
import ilp.iav.caosd.uma.Term;

public class MappingFunction {
	private Integer intentionalElement;
	private List<Term> features=new LinkedList<Term>();
	
	public Integer getEntity() {
		return intentionalElement;
	}
	public void setEntity(Integer entity) {
		this.intentionalElement = entity;
	}
	public List<Term> getFeatures() {
		return features;
	}
	public void setFeatures(List<Term> features) {
		this.features = features;
	}
	
	public void addFeature(Double w,Integer v) {
		Term t=new Term(w,v);
		features.add(t);
	}
	
	@Override
	public int hashCode() {
		return Objects.hash(intentionalElement, features);
	}
	
	@Override
	public String toString() {
		String res="x_"+intentionalElement+" = ";
		for(int i=0;i<features.size();i++) {
			res=res+" "+features.get(i).toString();
		}
		return res;
	}
	
	// -intentional_element + features = 0
	public LinearConstraint getLinearConstraint() {
		List<Term> listTerm=new LinkedList<Term>();
		listTerm.addAll(features);
		listTerm.add(new Term(-1d,intentionalElement));
		LinearConstraint lc=new LinearConstraint(listTerm, 0, Comparator.Equal);
		return lc;
	}

}
