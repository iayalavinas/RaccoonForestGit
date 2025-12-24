package istar.iav.caosd.uma;

import java.util.LinkedList;
import java.util.List;

public class Contribution {
	private Quality target;
	private List<IntentionalElement> helpList,hurtList,makeList,breakList;
	
	public Contribution(Quality t) {
		target=t;
		helpList=new LinkedList<IntentionalElement>();
		hurtList=new LinkedList<IntentionalElement>();
		makeList=new LinkedList<IntentionalElement>();
		breakList=new LinkedList<IntentionalElement>();
	}
	
	public void addHelpContribution(IntentionalElement gte) {
		helpList.add(gte);
	}
	
	public void addHurtContribution(IntentionalElement gte) {
		hurtList.add(gte);
	}
	
	public void addMakeContribution(IntentionalElement gte) {
		makeList.add(gte);
	}
	
	public void addBreakContribution(IntentionalElement gte) {
		breakList.add(gte);
	}

	public Quality getTarget() {
		return target;
	}

	public void setTarget(Quality target) {
		this.target = target;
	}

	public List<IntentionalElement> getHelpList() {
		return helpList;
	}

	public void setHelpList(List<IntentionalElement> helpList) {
		this.helpList = helpList;
	}

	public List<IntentionalElement> getHurtList() {
		return hurtList;
	}

	public void setHurtList(List<IntentionalElement> hurtList) {
		this.hurtList = hurtList;
	}

	public List<IntentionalElement> getMakeList() {
		return makeList;
	}

	public void setMakeList(List<IntentionalElement> makeList) {
		this.makeList = makeList;
	}

	public List<IntentionalElement> getBreakList() {
		return breakList;
	}

	public void setBreakList(List<IntentionalElement> breakList) {
		this.breakList = breakList;
	}
	
	public Boolean isChild(String id) {
		Boolean res=false;
		int i=0;
		// comprobamos hurt
		while(i<hurtList.size() && !res) {
			if(hurtList.get(i).getId().equals(id))res=true;
			i++;
		}
		i=0;
		// comprobamos make
		while(i<makeList.size() && !res) {
			if(makeList.get(i).getId().equals(id))res=true;
			i++;
		}
		i=0;
		//comprobamos help
		while(i<helpList.size() && !res) {
			if(helpList.get(i).getId().equals(id))res=true;
			i++;
		}
		i=0;
		// comprobamos break
		while(i<breakList.size() && !res) {
			if(breakList.get(i).getId().equals(id))res=true;
			i++;
		}
		return res;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((breakList == null) ? 0 : breakList.hashCode());
		result = prime * result + ((helpList == null) ? 0 : helpList.hashCode());
		result = prime * result + ((hurtList == null) ? 0 : hurtList.hashCode());
		result = prime * result + ((makeList == null) ? 0 : makeList.hashCode());
		result = prime * result + ((target == null) ? 0 : target.hashCode());
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
		Contribution other = (Contribution) obj;
		if (breakList == null) {
			if (other.breakList != null)
				return false;
		} else if (!breakList.equals(other.breakList))
			return false;
		if (helpList == null) {
			if (other.helpList != null)
				return false;
		} else if (!helpList.equals(other.helpList))
			return false;
		if (hurtList == null) {
			if (other.hurtList != null)
				return false;
		} else if (!hurtList.equals(other.hurtList))
			return false;
		if (makeList == null) {
			if (other.makeList != null)
				return false;
		} else if (!makeList.equals(other.makeList))
			return false;
		if (target == null) {
			if (other.target != null)
				return false;
		} else if (!target.equals(other.target))
			return false;
		return true;
	}
}
