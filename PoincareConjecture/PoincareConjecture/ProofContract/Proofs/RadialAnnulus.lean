import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Explicit radial collar for a closed Euclidean annulus. -/
theorem radial_annulus_homeomorph :
    ∃ e : {x : Euclidean3 // 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2} ≃ₜ
      (Sphere2 × Set.Icc (1 : ℝ) 2),
      ∀ x, ((e x).1 : Euclidean3) = ‖(x : Euclidean3)‖⁻¹ • (x : Euclidean3) ∧
        ((e x).2 : ℝ) = ‖(x : Euclidean3)‖ :=
/- SWARM_PROOF_BEGIN -/
by
  let A := {x : Euclidean3 // 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 2}
  let f : A → Sphere2 × Set.Icc (1 : ℝ) 2 := fun x =>
    (⟨‖(x : Euclidean3)‖⁻¹ • (x : Euclidean3), by
        rw [Metric.mem_sphere, dist_zero_right]
        have hx : 0 < ‖(x : Euclidean3)‖ := lt_of_lt_of_le zero_lt_one x.property.1
        simp [norm_smul, abs_of_pos (inv_pos.mpr hx), hx.ne']⟩,
      ⟨‖(x : Euclidean3)‖, x.property⟩)
  let g : (Sphere2 × Set.Icc (1 : ℝ) 2) → A := fun p =>
    ⟨(p.2 : ℝ) • (p.1 : Euclidean3), by
      have hs : ‖(p.1 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.property
      have hp : 0 < (p.2 : ℝ) := lt_of_lt_of_le zero_lt_one p.2.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hs]
      simp only [mul_one]
      exact p.2.property⟩
  have hfg : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    dsimp [f, g]
    have hx : 0 < ‖(x : Euclidean3)‖ := lt_of_lt_of_le zero_lt_one x.property.1
    simp [smul_smul, hx.ne']
  have hgf : Function.RightInverse g f := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      dsimp [f, g]
      have hs : ‖(p.1 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.property
      have hp : 0 < (p.2 : ℝ) := lt_of_lt_of_le zero_lt_one p.2.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hs]
      rw [mul_one, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
    · apply Subtype.ext
      dsimp [f, g]
      have hs : ‖(p.1 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.property
      have hp : 0 < (p.2 : ℝ) := lt_of_lt_of_le zero_lt_one p.2.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hs]
      simp only [mul_one]
  have hf : Continuous f := by
    dsimp [f]
    have hn : Continuous (fun x : A => ‖(x : Euclidean3)‖) :=
      continuous_subtype_val.norm
    have hni : Continuous (fun x : A => ‖(x : Euclidean3)‖⁻¹) :=
      hn.inv₀ (fun x => (lt_of_lt_of_le zero_lt_one x.property.1).ne')
    exact (hni.smul continuous_subtype_val).subtype_mk _ |>.prodMk (hn.subtype_mk _)
  have hg : Continuous g := by
    dsimp [g]
    exact ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  let e : A ≃ₜ (Sphere2 × Set.Icc (1 : ℝ) 2) :=
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := hfg
          right_inv := hgf }
      continuous_toFun := hf
      continuous_invFun := hg }
  refine ⟨e, ?_⟩
  intro x
  exact ⟨rfl, rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
