package istar.iav.caosd.uma;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

public class Actor extends IStarEntity {
	
	private HashMap<String,IntentionalElement> wants;
	private List<Actor> participatesIn,isA;
	private HashMap<String, Refinement> refinementList;
	private HashMap<String, Contribution> contributionList;
	// tenemos pendiente poner el qualified.

	public Actor(String i, String t) {
		super(i, t);
		wants=new HashMap<String, IntentionalElement>();
		participatesIn=new LinkedList<Actor>();
		isA=new LinkedList<Actor>();
		refinementList = new HashMap<String, Refinement>();
		contributionList = new HashMap<String, Contribution>();
	}

	public HashMap<String,IntentionalElement> getWants() {
		return wants;
	}

	public void setWants(HashMap<String,IntentionalElement> wants) {
		this.wants = wants;
	}
	
	public void putIntentionalElement(IntentionalElement ie) {
		wants.put(ie.getId(), ie);
	}
	
	public Boolean wants(String id) {
		return wants.containsKey(id);
	}

	public List<Actor> getParticipatesIn() {
		return participatesIn;
	}

	public void setParticipatesIn(List<Actor> participatesIn) {
		this.participatesIn = participatesIn;
	}
	
	public void addParticipatesIn(Actor act) {
		participatesIn.add(act);
	}

	public List<Actor> getIsA() {
		return isA;
	}

	public void setIsA(List<Actor> isA) {
		this.isA = isA;
	}
	
	public void addIs(Actor act) {
		isA.add(act);
	}
	
	

	public HashMap<String, Refinement> getRefinementList() {
		return refinementList;
	}

	public void setRefinementList(HashMap<String, Refinement> refinementList) {
		this.refinementList = refinementList;
	}

	public HashMap<String, Contribution> getContributionList() {
		return contributionList;
	}

	public void setContributionList(HashMap<String, Contribution> contributionList) {
		this.contributionList = contributionList;
	}
	
	public Boolean hasIntentionalElement(String id) {
		return wants.containsKey(id);
	}
	
	public Boolean isRootElement(String id) {
		Boolean res=true;
		//1. Es elemento intencional del agente
		if(wants.containsKey(id)) {
			//System.out.println(wants.get(id).getText());
			// comprobamos si es hijo en alg�n refinement.
			Iterator<String> refiIte=refinementList.keySet().iterator();
			while(refiIte.hasNext() && res) {
				Refinement ref=refinementList.get(refiIte.next());
				if(ref.isChild(id))res=false;
			}
			// comprobamos si est� en alguna contribution
			Iterator<String> contIte=contributionList.keySet().iterator();
			while(contIte.hasNext() && res) {
				Contribution con=contributionList.get(contIte.next());
				if(con.isChild(id))res=false;
			}
		}else {
			res=false;
		}
		return res;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((contributionList == null) ? 0 : contributionList.hashCode());
		result = prime * result + ((isA == null) ? 0 : isA.hashCode());
		result = prime * result + ((participatesIn == null) ? 0 : participatesIn.hashCode());
		result = prime * result + ((refinementList == null) ? 0 : refinementList.hashCode());
		result = prime * result + ((wants == null) ? 0 : wants.hashCode());
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
		Actor other = (Actor) obj;
		if (contributionList == null) {
			if (other.contributionList != null)
				return false;
		} else if (!contributionList.equals(other.contributionList))
			return false;
		if (isA == null) {
			if (other.isA != null)
				return false;
		} else if (!isA.equals(other.isA))
			return false;
		if (participatesIn == null) {
			if (other.participatesIn != null)
				return false;
		} else if (!participatesIn.equals(other.participatesIn))
			return false;
		if (refinementList == null) {
			if (other.refinementList != null)
				return false;
		} else if (!refinementList.equals(other.refinementList))
			return false;
		if (wants == null) {
			if (other.wants != null)
				return false;
		} else if (!wants.equals(other.wants))
			return false;
		return true;
	}

	
	

}
