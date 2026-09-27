import PoincareConjecture.ProofContract.Refinement20260927.Neck
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedNegativeHalfCollar
open PoincareConjecture.ProofContract.Refinement20260927
theorem negative_half_collar : NegativeHalfCollarStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro M hsc f hf p
  dsimp only
  let rho : Set.Icc (-1 : ℝ) 1 → Set.Icc (-1 : ℝ) 1 := fun t =>
    ⟨-(t : ℝ), by
      constructor <;> rcases t.2 with ⟨htl, htu⟩ <;> linarith⟩
  let r : Set.Icc (-1 : ℝ) 1 ≃ₜ Set.Icc (-1 : ℝ) 1 :=
    { toEquiv :=
        { toFun := rho
          invFun := rho
          left_inv := by
            intro t
            apply Subtype.ext
            simp [rho]
          right_inv := by
            intro t
            apply Subtype.ext
            simp [rho] }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hrho : Topology.IsEmbedding rho := by
    change Topology.IsEmbedding r
    exact r.isEmbedding
  let j : PoincareConjecture.ProofContract.V1.Sphere2 × Set.Icc (-1 : ℝ) 1 →
      PoincareConjecture.ProofContract.V1.Sphere2 × Set.Icc (-1 : ℝ) 1 :=
    fun q => (q.1, rho q.2)
  have hj : Topology.IsEmbedding j := by
    exact Topology.IsEmbedding.id.prodMap hrho
  let F : PoincareConjecture.ProofContract.V1.Sphere2 × Set.Icc (-1 : ℝ) 1 → M :=
    f ∘ j
  have hF : Topology.IsEmbedding F := hf.comp hj
  have hrho0 : rho ⟨0, by norm_num⟩ = ⟨0, by norm_num⟩ := by
    apply Subtype.ext
    simp [rho]
  have hrhohalf : rho ⟨(1 / 2 : ℝ), by norm_num⟩ =
      ⟨(-1 / 2 : ℝ), by norm_num⟩ := by
    apply Subtype.ext
    norm_num [rho]
  have hslice :
      PoincareConjecture.ParallelImplementation.ClosedSphereCutData.embeddedSphereCutSlice F =
      PoincareConjecture.ParallelImplementation.ClosedSphereCutData.embeddedSphereCutSlice f := by
    ext x
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      change f (s, rho ⟨0, by norm_num⟩) = x at hs
      change f (s, ⟨0, by norm_num⟩) = x
      simpa only [hrho0] using hs
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      change f (s, ⟨0, by norm_num⟩) = x at hs
      change f (s, rho ⟨0, by norm_num⟩) = x
      simpa only [hrho0] using hs
  have hseed :
      PoincareConjecture.ParallelImplementation.ClosedSphereCutData.embeddedSphereCutPositiveSeed F p =
      PoincareConjecture.ParallelImplementation.ClosedSphereCutData.embeddedSphereCutNegativeSeed f p := by
    change f (p, rho ⟨(1 / 2 : ℝ), by norm_num⟩) =
      f (p, ⟨(-1 / 2 : ℝ), by norm_num⟩)
    rw [hrhohalf]
  have hpos :=
    PoincareConjecture.ParallelImplementation.ClosedSideHalfCollar.exists_actual_closed_side_half_collar
      hsc F hF p
  dsimp only at hpos
  rw [hslice, hseed] at hpos
  rcases hpos with ⟨b, k, hb, hk, hb0, hkpos, hglue⟩
  refine ⟨b, k, hb, hk, ?_, ?_, hglue⟩
  · intro s
    simpa only [F, Function.comp_apply, j, hrho0] using hb0 s
  · intro s t
    have hrhalf_t :
        rho ⟨(t : ℝ) / 2, by
          constructor <;> linarith [t.2.1, t.2.2]⟩ =
        ⟨-(t : ℝ) / 2, by
          constructor <;> linarith [t.2.1, t.2.2]⟩ := by
      apply Subtype.ext
      dsimp only [rho]
      ring
    simpa only [F, Function.comp_apply, j, hrhalf_t] using hkpos s t
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedNegativeHalfCollar
