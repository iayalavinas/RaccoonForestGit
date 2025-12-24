package ilp.iav.caosd.uma;

import java.util.Objects;

public class Term {
	private Double weight;
	private Integer variableID;
	
	public Term(Double w,Integer v) {
		weight=w;
		variableID=v;
	}

	public Double getWeight() {
		return weight;
	}

	public void setWeight(Double weight) {
		this.weight = weight;
	}

	public Integer getVariableID() {
		return variableID;
	}

	public void setVariableID(Integer variableID) {
		this.variableID = variableID;
	}

	@Override
	public int hashCode() {
		return Objects.hash(variableID, weight);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Term other = (Term) obj;
		return Objects.equals(variableID, other.variableID) && Objects.equals(weight, other.weight);
	}

	@Override
	public String toString() {
		return weight + "* x_" + variableID;
	}
	
	

}
