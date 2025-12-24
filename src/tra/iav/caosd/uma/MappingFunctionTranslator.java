package tra.iav.caosd.uma;

import java.util.List;

import ilp.iav.caosd.uma.ILPProblem;
import mf.iav.caosd.uma.MappingFunction;

public class MappingFunctionTranslator {
	
	private ILPProblem problem;
	
	public MappingFunctionTranslator(ILPProblem p) {
		problem=p;
	}
	
	public void loadConstraints(MappingFunction mf) {
		problem.addEqualityConstraint(mf.getLinearConstraint());
	}

	public void loadConstraints(List<MappingFunction> mf) {
		for (int i = 0; i < mf.size(); i++) {
			problem.addEqualityConstraint(mf.get(i).getLinearConstraint());
		}
	}

}
