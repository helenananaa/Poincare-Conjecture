import PoincareConjecture.ProofContract.Refinement20260927.JointC1Approximation
import PoincareConjecture.ParallelImplementation.RefinedUniformMollification
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ProofContract.Refinement20260927
/-- **Math.** Actual fixed proof, independently rebuilt from the captured worker source. -/
theorem checked_uniform_mollification : UniformMollificationStatement :=
  ParallelImplementation.RefinedUniformMollification.uniform_mollification
/-- **Math.** The uniform-convergence input disappears; the two running leaves are explicit. -/
theorem cylinder_c1_after_uniform (restrict : CylinderRestrictionEstimateStatement)
    (extend : CylinderCompactExtensionStatement) : CylinderC1ApproximationStatement :=
  cylinder_c1_approximation_of_leaves checked_uniform_mollification restrict extend
#print axioms checked_uniform_mollification
#print axioms cylinder_c1_after_uniform
end PoincareConjecture.ProofContract.Refinement20260927
