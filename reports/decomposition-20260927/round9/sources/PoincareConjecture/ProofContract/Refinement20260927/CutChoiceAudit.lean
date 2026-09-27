import PoincareConjecture.ProofContract.Refinement20260927.SynchronizedBudget
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** Audit: the old Nonempty choice forgets which collar supplied its proof.
The conditional root theorem remains logically valid, but this value is not
certified to be the actual cut of the supplied collar. -/
theorem old_cut_choice_independent_of_collar
    (atlas : SideInteriorAtlasStatement.{u}) (negative : NegativeHalfCollarStatement.{u})
    {M : ClosedThreeManifold.{u}} (hsc : SimplyConnectedSpace M)
    (f g : Sphere2 × Icc (-1 : ℝ) 1 → M)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) (p q : Sphere2) :
    closedCut_of_neck atlas negative hsc f hf p =
      closedCut_of_neck atlas negative hsc g hg q := by
  rfl
#print axioms old_cut_choice_independent_of_collar
end PoincareConjecture.ProofContract.Refinement20260927
