package istar.iav.caosd.uma;

public class Dependency extends IStarEntity {
	
	private Actor depender,dependee;
	private IStarEntity dependerEle,dependeeEle;
	private IntentionalElement dependum;

	public Dependency(String i, String t) {
		super(i, t);
	}

	public Actor getDepender() {
		return depender;
	}

	public void setDepender(Actor depender) {
		this.depender = depender;
	}

	public Actor getDependee() {
		return dependee;
	}

	public void setDependee(Actor dependee) {
		this.dependee = dependee;
	}

	public IStarEntity getDependerEle() {
		return dependerEle;
	}

	public void setDependerEle(IStarEntity dependerEle) {
		this.dependerEle = dependerEle;
	}

	public IStarEntity getDependeeEle() {
		return dependeeEle;
	}

	public void setDependeeEle(IStarEntity dependeeEle) {
		this.dependeeEle = dependeeEle;
	}

	public IntentionalElement getDependum() {
		return dependum;
	}

	public void setDependum(IntentionalElement dependum) {
		this.dependum = dependum;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((dependee == null) ? 0 : dependee.hashCode());
		result = prime * result + ((dependeeEle == null) ? 0 : dependeeEle.hashCode());
		result = prime * result + ((depender == null) ? 0 : depender.hashCode());
		result = prime * result + ((dependerEle == null) ? 0 : dependerEle.hashCode());
		result = prime * result + ((dependum == null) ? 0 : dependum.hashCode());
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
		Dependency other = (Dependency) obj;
		if (dependee == null) {
			if (other.dependee != null)
				return false;
		} else if (!dependee.equals(other.dependee))
			return false;
		if (dependeeEle == null) {
			if (other.dependeeEle != null)
				return false;
		} else if (!dependeeEle.equals(other.dependeeEle))
			return false;
		if (depender == null) {
			if (other.depender != null)
				return false;
		} else if (!depender.equals(other.depender))
			return false;
		if (dependerEle == null) {
			if (other.dependerEle != null)
				return false;
		} else if (!dependerEle.equals(other.dependerEle))
			return false;
		if (dependum == null) {
			if (other.dependum != null)
				return false;
		} else if (!dependum.equals(other.dependum))
			return false;
		return true;
	}
	
	
	
	

}
