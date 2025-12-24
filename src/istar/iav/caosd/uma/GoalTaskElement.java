package istar.iav.caosd.uma;

import java.util.LinkedList;
import java.util.List;

public class GoalTaskElement extends IntentionalElement {
	private List<Quality> qualifications;

	public GoalTaskElement(String i, String t) {
		super(i, t);
		qualifications=new LinkedList<Quality>();
	}
	
	public void addQualification(Quality qua) {
		qualifications.add(qua);
	}
	
	public void removeQualification(Quality qua) {
		qualifications.remove(qua);
	}

	public List<Quality> getQualifications() {
		return qualifications;
	}

	public void setQualifications(List<Quality> qualifications) {
		this.qualifications = qualifications;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((qualifications == null) ? 0 : qualifications.hashCode());
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
		GoalTaskElement other = (GoalTaskElement) obj;
		if (qualifications == null) {
			if (other.qualifications != null)
				return false;
		} else if (!qualifications.equals(other.qualifications))
			return false;
		return true;
	}
	
	
	
	

}
