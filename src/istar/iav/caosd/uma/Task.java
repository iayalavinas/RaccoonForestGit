package istar.iav.caosd.uma;

import java.util.LinkedList;
import java.util.List;

public class Task extends GoalTaskElement {
	
	private List<Resource> neededBy;

	public Task(String i, String t) {
		super(i, t);
		neededBy=new LinkedList<Resource>();
	}
	
	public void addNeededResource(Resource res) {
		neededBy.add(res);
	}
	
	public List<Resource> getNeededBy(){
		return neededBy;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((neededBy == null) ? 0 : neededBy.hashCode());
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
		Task other = (Task) obj;
		if (neededBy == null) {
			if (other.neededBy != null)
				return false;
		} else if (!neededBy.equals(other.neededBy))
			return false;
		return true;
	}

	

}
