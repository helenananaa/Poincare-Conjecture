import PoincareConjecture.ProofContract.Refinement20260927.ApproximateTransferRoot
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
/-- **Math.** A constant target map cannot satisfy this class-transfer contract.
This guards against lowering the energy by destroying the nontrivial class. -/
theorem SmoothClassMap.not_constant {M N : CompactSmoothThree.{u}}
    {C : BasedSphereClass M} {D : BasedSphereClass N} (h : SmoothClassMap C D) :
    ¬ ∀ p : M, h.map p = D.base := by
  intro hconst
  apply D.nontrivial
  have hc : ((⟨h.map,h.smooth.continuous⟩ : C(M,N)).comp C.reference.continuousMap) =
      ContinuousMap.const (SweepParameter × Sphere2) D.base := by
    ext x
    exact hconst _
  have ht := h.reference.symm
  rw [hc] at ht
  exact ht
#print axioms SmoothClassMap.not_constant
end PoincareConjecture.ProofContract.Refinement20260927
