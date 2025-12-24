package ilp.iav.caosd.uma;

import java.util.Objects;

public class Bounding {
	
	private Integer min,max;
	
	public Bounding(int n,int x) {
		min=n;
		max=x;
	}

	public Integer getMin() {
		return min;
	}

	public void setMin(Integer min) {
		this.min = min;
	}

	public Integer getMax() {
		return max;
	}

	public void setMax(Integer max) {
		this.max = max;
	}
	
	public Double getRange() {
		Integer res=max-min;
		return res.doubleValue();
	}

	@Override
	public int hashCode() {
		return Objects.hash(max, min);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Bounding other = (Bounding) obj;
		return Objects.equals(max, other.max) && Objects.equals(min, other.min);
	}

	@Override
	public String toString() {
		return "Bounding [min=" + min + ", max=" + max + "]";
	}
	
	

}
