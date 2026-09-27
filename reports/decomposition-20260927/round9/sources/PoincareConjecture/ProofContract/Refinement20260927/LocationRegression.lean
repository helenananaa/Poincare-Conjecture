import PoincareConjecture.ProofContract.Refinement20260927.MatchedBudget
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** Regression: the selected output carries the two prescribed subsets. -/
theorem locatedCut_has_expected_subsets {M : ClosedThreeManifold.{u}}
    (hsc : SimplyConnectedSpace M) (f : Sphere2 × Icc (-1 : ℝ) 1 → M)
    (hf : Topology.IsEmbedding f) (p : Sphere2) :
    (locatedNeckCut hsc f hf p).cut.U = closure (positiveCutComponent f p) ∧
    (locatedNeckCut hsc f hf p).cut.V = closure (negativeCutComponent f p) :=
  ⟨(locatedNeckCut hsc f hf p).left_eq,(locatedNeckCut hsc f hf p).right_eq⟩
/-- **Math.** Different prescribed negative regions force different selected cuts.
This is a regression contract, not an assertion that any two collars differ. -/
theorem locatedCuts_ne_of_negative_regions_ne {M : ClosedThreeManifold.{u}}
    (hsc : SimplyConnectedSpace M) (f g : Sphere2 × Icc (-1 : ℝ) 1 → M)
    (hf : Topology.IsEmbedding f) (hg : Topology.IsEmbedding g) (p q : Sphere2)
    (hne : closure (negativeCutComponent f p) ≠ closure (negativeCutComponent g q)) :
    (locatedNeckCut hsc f hf p).cut ≠ (locatedNeckCut hsc g hg q).cut := by
  intro heq
  apply hne
  exact (locatedNeckCut hsc f hf p).right_eq.symm.trans
    ((congrArg RegularClosedCut.V heq).trans (locatedNeckCut hsc g hg q).right_eq)
#print axioms locatedCut_has_expected_subsets
#print axioms locatedCuts_ne_of_negative_regions_ne
end PoincareConjecture.ProofContract.Refinement20260927
