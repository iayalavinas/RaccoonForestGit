package istar.iav.caosd.uma;

import java.util.LinkedList;
import java.util.List;

public class Refinement {
	// los refinements solo pueden ser de un tipo, si hubiera de 2 tipos el modelo estar�a mal construido.
	private GoalTaskElement parent;
	private List<GoalTaskElement> orRefinements;
	private List<GoalTaskElement> andRefinements;
	
	public Refinement(GoalTaskElement g) {
		parent=g;
		orRefinements = new LinkedList<GoalTaskElement>();
		andRefinements = new LinkedList<GoalTaskElement>();
	}
	
	public void addOrRefinement(GoalTaskElement gte) {
		orRefinements.add(gte);
	}
	
	public void addAndRefinement(GoalTaskElement gte) {
		andRefinements.add(gte);
	}

	public GoalTaskElement getParent() {
		return parent;
	}

	public void setParent(GoalTaskElement parentGoal) {
		this.parent = parentGoal;
	}

	public List<GoalTaskElement> getOrRefinements() {
		return orRefinements;
	}

	public void setOrRefinements(List<GoalTaskElement> orRefinements) {
		this.orRefinements = orRefinements;
	}

	public List<GoalTaskElement> getAndRefinements() {
		return andRefinements;
	}

	public void setAndRefinements(List<GoalTaskElement> andRefinements) {
		this.andRefinements = andRefinements;
	}
	
	public Boolean isChild(String key) {
		Boolean res=false;
		// comprobamos los AND-refinement.
		int i=0;
		while(!res && i<andRefinements.size()) {
			if(andRefinements.get(i).getId().equals(key))res=true;
			i++;
		}
		i=0;
		while(!res && i<orRefinements.size()) {
			if(orRefinements.get(i).getId().equals(key))res=true;
			i++;
		}
		
		return res;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((andRefinements == null) ? 0 : andRefinements.hashCode());
		result = prime * result + ((orRefinements == null) ? 0 : orRefinements.hashCode());
		result = prime * result + ((parent == null) ? 0 : parent.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Refinement other = (Refinement) obj;
		if (andRefinements == null) {
			if (other.andRefinements != null)
				return false;
		} else if (!andRefinements.equals(other.andRefinements))
			return false;
		if (orRefinements == null) {
			if (other.orRefinements != null)
				return false;
		} else if (!orRefinements.equals(other.orRefinements))
			return false;
		if (parent == null) {
			if (other.parent != null)
				return false;
		} else if (!parent.equals(other.parent))
			return false;
		return true;
	}
	
	

}
