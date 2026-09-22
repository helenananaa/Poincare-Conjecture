import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ProofContract.Proofs
open Function
open scoped Topology
/-- Based homotopy transports pi1 surjectivity to a retracted domain. -/
theorem pi1_surjective_after_based_homotopy
    {U A X : Type*} [TopologicalSpace U] [TopologicalSpace A] [TopologicalSpace X]
    (j : C(U, X)) (k : C(A, X)) (r : C(U, A)) (c : U) (a : A)
    (hr : r c = a) (hj : j c = k a) (H : j.Homotopy (k.comp r))
    (hfix : ∀ t : unitInterval, H (t,c) = k a)
    (hsurj : Surjective (FundamentalGroup.mapOfEq j hj)) :
    Surjective (FundamentalGroup.map k a) :=
/- SWARM_PROOF_BEGIN -/
by
  intro q
  obtain ⟨p, hp⟩ := hsurj q
  refine ⟨FundamentalGroup.mapOfEq r hr p, ?_⟩
  rw [← hp, FundamentalGroup.mapOfEq_apply, FundamentalGroup.map_apply,
    FundamentalGroup.mapOfEq_apply]
  rw [Path.Homotopic.Quotient.map_cast, ← Path.Homotopic.Quotient.map_comp]
  refine Quotient.inductionOn p ?_
  intro γ
  change
    (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk γ) (k.comp r)).cast _ _ =
      (Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk γ) j).cast _ _
  rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map]
  rw [← Path.Homotopic.Quotient.mk_cast, ← Path.Homotopic.Quotient.mk_cast]
  rw [Path.Homotopic.Quotient.eq]
  have hrX : k a = (k.comp r) c := by
    simpa only [ContinuousMap.comp_apply] using congrArg k hr.symm
  have hconst : (H.evalAt c).cast hj.symm hrX = Path.refl (k a) := by
    apply Path.ext
    funext t
    rw [Path.cast_coe]
    change H (t, c) = k a
    exact hfix t
  have hhom :
      (((γ.map j.continuous).trans (H.evalAt c)).cast hj.symm hrX).Homotopic
        (((H.evalAt c).trans (γ.map (k.comp r).continuous)).cast hj.symm hrX) :=
    (Path.Homotopic.map_trans_evalAt H γ).pathCast hj.symm hrX
  have hleft :
      (((γ.map j.continuous).trans (H.evalAt c)).cast hj.symm hrX).Homotopic
        ((γ.map j.continuous).cast hj.symm hj.symm) := by
    rw [Path.cast_trans _ _ hj.symm hj.symm hrX, hconst]
    exact ⟨Path.Homotopy.transRefl _⟩
  have hright :
      (((H.evalAt c).trans (γ.map (k.comp r).continuous)).cast hj.symm hrX).Homotopic
        ((γ.map (k.comp r).continuous).cast hrX hrX) := by
    rw [Path.cast_trans _ _ hj.symm hrX hrX, hconst]
    exact ⟨Path.Homotopy.reflTrans _⟩
  exact hright.symm.trans (hhom.symm.trans hleft)
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
