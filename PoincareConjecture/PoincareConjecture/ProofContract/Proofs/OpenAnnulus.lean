import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- A genuine open three-dimensional annulus is path connected. -/
theorem open_annulus_path_connected (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Nonempty ({x : Euclidean3 // a < ‖x‖ ∧ ‖x‖ < b} ≃ₜ
      (Sphere2 × Set.Ioo a b)) ∧
    IsPathConnected {x : Euclidean3 | a < ‖x‖ ∧ ‖x‖ < b} :=
/- SWARM_PROOF_BEGIN -/
by
  let A := {x : Euclidean3 // a < ‖x‖ ∧ ‖x‖ < b}
  let f : A → Sphere2 × Set.Ioo a b := fun x =>
    (⟨‖(x : Euclidean3)‖⁻¹ • (x : Euclidean3), by
        rw [Metric.mem_sphere, dist_zero_right]
        have hx : 0 < ‖(x : Euclidean3)‖ := lt_trans ha x.property.1
        simp [norm_smul, abs_of_pos (inv_pos.mpr hx), hx.ne']⟩,
      ⟨‖(x : Euclidean3)‖, x.property⟩)
  let g : (Sphere2 × Set.Ioo a b) → A := fun p =>
    ⟨(p.2 : ℝ) • (p.1 : Euclidean3), by
      have hs : ‖(p.1 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.property
      have hp : 0 < (p.2 : ℝ) := lt_trans ha p.2.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hs]
      simp only [mul_one]
      exact p.2.property⟩
  have hfg : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    dsimp [f, g]
    have hx : 0 < ‖(x : Euclidean3)‖ := lt_trans ha x.property.1
    simp [smul_smul, hx.ne']
  have hgf : Function.RightInverse g f := by
    intro p
    apply Prod.ext
    · apply Subtype.ext
      dsimp [f, g]
      have hs : ‖(p.1 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.property
      have hp : 0 < (p.2 : ℝ) := lt_trans ha p.2.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hs]
      rw [mul_one, smul_smul, inv_mul_cancel₀ hp.ne', one_smul]
    · apply Subtype.ext
      dsimp [f, g]
      have hs : ‖(p.1 : Euclidean3)‖ = 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using p.1.property
      have hp : 0 < (p.2 : ℝ) := lt_trans ha p.2.2.1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp, hs]
      simp only [mul_one]
  have hf : Continuous f := by
    dsimp [f]
    have hn : Continuous (fun x : A => ‖(x : Euclidean3)‖) :=
      continuous_subtype_val.norm
    have hni : Continuous (fun x : A => ‖(x : Euclidean3)‖⁻¹) :=
      hn.inv₀ (fun x => (lt_trans ha x.property.1).ne')
    exact (hni.smul continuous_subtype_val).subtype_mk _ |>.prodMk (hn.subtype_mk _)
  have hg : Continuous g := by
    dsimp [g]
    exact ((continuous_subtype_val.comp continuous_snd).smul
      (continuous_subtype_val.comp continuous_fst)).subtype_mk _
  let e : A ≃ₜ (Sphere2 × Set.Ioo a b) :=
    { toEquiv :=
        { toFun := f
          invFun := g
          left_inv := hfg
          right_inv := hgf }
      continuous_toFun := hf
      continuous_invFun := hg }
  haveI : PathConnectedSpace Sphere2 := by
    apply isPathConnected_iff_pathConnectedSpace.mp
    apply isPathConnected_sphere ?_ _ (by norm_num)
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  have hI : IsPathConnected (Set.Ioo a b) := by
    apply (convex_Ioo a b).isPathConnected
    exact ⟨(a + b) / 2, by constructor <;> linarith⟩
  letI : PathConnectedSpace (Set.Ioo a b) :=
    isPathConnected_iff_pathConnectedSpace.mp hI
  have hT : IsPathConnected (Set.univ : Set (Sphere2 × Set.Ioo a b)) :=
    isPathConnected_univ
  have hA : IsPathConnected (Set.univ : Set A) := by
    have h := (e.symm.isPathConnected_image
      (s := (Set.univ : Set (Sphere2 × Set.Ioo a b)))).mpr hT
    have hrange : e.symm '' (Set.univ : Set (Sphere2 × Set.Ioo a b)) =
        (Set.univ : Set A) := by
      ext x
      constructor
      · intro _
        exact Set.mem_univ _
      · intro _
        exact ⟨e x, Set.mem_univ _, e.symm_apply_apply x⟩
    rw [hrange] at h
    exact h
  have hambient := hA.image (continuous_subtype_val : Continuous (Subtype.val : A → Euclidean3))
  have himage :
      (Subtype.val : A → Euclidean3) '' (Set.univ : Set A) =
        {x : Euclidean3 | a < ‖x‖ ∧ ‖x‖ < b} := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  rw [himage] at hambient
  exact ⟨⟨e⟩, hambient⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
