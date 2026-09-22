import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- Topological Alexander extension with exact boundary values. -/
theorem sphere_homeomorph_extends_closedBall (h : Sphere2 ≃ₜ Sphere2) :
    ∃ H : Metric.closedBall (0 : Euclidean3) 1 ≃ₜ Metric.closedBall (0 : Euclidean3) 1,
      ∀ x : Sphere2, (H ⟨x, by have hx := x.property; simpa using (le_of_eq hx)⟩ : Euclidean3) = h x :=
/- SWARM_PROOF_BEGIN -/
by
  let B := Metric.closedBall (0 : Euclidean3) 1
  let s0 : Sphere2 :=
    Classical.choice (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).coe_sort
  let n : B → Sphere2 := fun x =>
    if hx : (x : Euclidean3) = 0 then s0
    else
      ⟨NormedSpace.normalize (x : Euclidean3), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize hx⟩
  let q : B → Euclidean3 := fun x =>
    ‖(x : Euclidean3)‖ • (h (n x) : Euclidean3)
  have hqmem : ∀ x : B, q x ∈ B := by
    intro x
    have hxle : ‖(x : Euclidean3)‖ ≤ 1 := by
      have hxmem := x.property
      change dist (x : Euclidean3) 0 ≤ 1 at hxmem
      simpa [dist_zero_right] using hxmem
    change dist (q x) 0 ≤ 1
    simp only [q, norm_smul, Real.norm_of_nonneg (norm_nonneg _),
      dist_zero_right, mem_sphere_zero_iff_norm.1 (h (n x)).property, mul_one]
    exact hxle
  let F : B → B := B.codRestrict q hqmem
  let q' : B → Euclidean3 := fun x =>
    ‖(x : Euclidean3)‖ • (h.symm (n x) : Euclidean3)
  have hq'mem : ∀ x : B, q' x ∈ B := by
    intro x
    have hxle : ‖(x : Euclidean3)‖ ≤ 1 := by
      have hxmem := x.property
      change dist (x : Euclidean3) 0 ≤ 1 at hxmem
      simpa [dist_zero_right] using hxmem
    change dist (q' x) 0 ≤ 1
    simp only [q', norm_smul, Real.norm_of_nonneg (norm_nonneg _),
      dist_zero_right, mem_sphere_zero_iff_norm.1 (h.symm (n x)).property, mul_one]
    exact hxle
  let G : B → B := B.codRestrict q' hq'mem
  have hF_norm (x : B) : ‖(F x : Euclidean3)‖ = ‖(x : Euclidean3)‖ := by
    change ‖q x‖ = ‖(x : Euclidean3)‖
    simp only [q, norm_smul, Real.norm_of_nonneg (norm_nonneg _),
      mem_sphere_zero_iff_norm.1 (h (n x)).property, mul_one]
  have hG_norm (x : B) : ‖(G x : Euclidean3)‖ = ‖(x : Euclidean3)‖ := by
    change ‖q' x‖ = ‖(x : Euclidean3)‖
    simp only [q', norm_smul, Real.norm_of_nonneg (norm_nonneg _),
      mem_sphere_zero_iff_norm.1 (h.symm (n x)).property, mul_one]
  have hF_zero : F (0 : B) = 0 := by
    apply Subtype.ext
    change q (0 : B) = 0
    simp [q]
  have hG_zero : G (0 : B) = 0 := by
    apply Subtype.ext
    change q' (0 : B) = 0
    simp [q']
  have hn_cont (x : B) (hx : (x : Euclidean3) ≠ 0) : ContinuousAt n x := by
    have hnorm : ContinuousAt (fun y : B => ‖(y : Euclidean3)‖) x :=
      continuous_norm.continuousAt.comp continuousAt_subtype_val
    have hraw : ContinuousAt (fun y : B => NormedSpace.normalize (y : Euclidean3)) x :=
      (hnorm.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_subtype_val
    have hne : {y : B | (y : Euclidean3) ≠ 0} ∈ 𝓝 x := by
      exact (isOpen_compl_singleton.preimage continuous_subtype_val).mem_nhds (by simpa using hx)
    have hev : (fun y : B => NormedSpace.normalize (y : Euclidean3)) =ᶠ[𝓝 x]
        (fun y : B => (n y : Euclidean3)) := by
      filter_upwards [hne] with y hy
      have hy0 : y ≠ (0 : B) := by
        intro hy'
        apply hy
        simpa [hy']
      simp [n, hy0]
    have hval : ContinuousAt (fun y : B => (n y : Euclidean3)) x := hraw.congr hev
    rw [ContinuousAt, tendsto_subtype_rng]
    exact hval
  have hq_at (x : B) (hx : (x : Euclidean3) ≠ 0) : ContinuousAt q x := by
    have hnorm : ContinuousAt (fun y : B => ‖(y : Euclidean3)‖) x :=
      continuous_norm.continuousAt.comp continuousAt_subtype_val
    have hh : ContinuousAt (fun y : B => (h (n y) : Euclidean3)) x := by
      exact continuousAt_subtype_val.comp (h.continuous.continuousAt.comp (hn_cont x hx))
    change ContinuousAt (fun y : B => ‖(y : Euclidean3)‖ • (h (n y) : Euclidean3)) x
    exact (hnorm.smul hh).congr (Filter.Eventually.of_forall (fun y => rfl))
  have hq'_at (x : B) (hx : (x : Euclidean3) ≠ 0) : ContinuousAt q' x := by
    have hnorm : ContinuousAt (fun y : B => ‖(y : Euclidean3)‖) x :=
      continuous_norm.continuousAt.comp continuousAt_subtype_val
    have hh : ContinuousAt (fun y : B => (h.symm (n y) : Euclidean3)) x := by
      exact continuousAt_subtype_val.comp (h.symm.continuous.continuousAt.comp (hn_cont x hx))
    change ContinuousAt (fun y : B => ‖(y : Euclidean3)‖ • (h.symm (n y) : Euclidean3)) x
    exact (hnorm.smul hh).congr (Filter.Eventually.of_forall (fun y => rfl))
  have hF_at (x : B) (hx : (x : Euclidean3) ≠ 0) : ContinuousAt F x := by
    simpa [F] using (hq_at x hx).codRestrict hqmem
  have hG_at (x : B) (hx : (x : Euclidean3) ≠ 0) : ContinuousAt G x := by
    simpa [G] using (hq'_at x hx).codRestrict hq'mem
  have hF_zero_cont : ContinuousAt F (0 : B) := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    rw [hF_zero]
    simpa [Subtype.dist_eq, dist_eq_norm, hF_norm y] using hy
  have hG_zero_cont : ContinuousAt G (0 : B) := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro y hy
    rw [hG_zero]
    simpa [Subtype.dist_eq, dist_eq_norm, hG_norm y] using hy
  have hF_cont : Continuous F := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : (x : Euclidean3) = 0
    · have hx0 : x = 0 := Subtype.ext hx
      rw [hx0]
      exact hF_zero_cont
    · exact hF_at x hx
  have hG_cont : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : (x : Euclidean3) = 0
    · have hx0 : x = 0 := Subtype.ext hx
      rw [hx0]
      exact hG_zero_cont
    · exact hG_at x hx
  have hnF (x : B) (hx : (x : Euclidean3) ≠ 0) : n (F x) = h (n x) := by
    have hFxnorm : ‖(F x : Euclidean3)‖ ≠ 0 := by
      rw [hF_norm x]
      exact (norm_pos_iff.mpr hx).ne'
    have hFx : (F x : Euclidean3) ≠ 0 := norm_ne_zero_iff.mp hFxnorm
    apply Subtype.ext
    simp only [n, dif_neg hFx]
    change NormedSpace.normalize (‖(x : Euclidean3)‖ • (h (n x) : Euclidean3)) = _
    rw [NormedSpace.normalize_smul_of_pos (norm_pos_iff.mpr hx)]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.1 (h (n x)).property)
  have hnG (x : B) (hx : (x : Euclidean3) ≠ 0) : n (G x) = h.symm (n x) := by
    have hGxnorm : ‖(G x : Euclidean3)‖ ≠ 0 := by
      rw [hG_norm x]
      exact (norm_pos_iff.mpr hx).ne'
    have hGx : (G x : Euclidean3) ≠ 0 := norm_ne_zero_iff.mp hGxnorm
    apply Subtype.ext
    simp only [n, dif_neg hGx]
    change NormedSpace.normalize (‖(x : Euclidean3)‖ • (h.symm (n x) : Euclidean3)) = _
    rw [NormedSpace.normalize_smul_of_pos (norm_pos_iff.mpr hx)]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.1 (h.symm (n x)).property)
  have hGF : ∀ x : B, G (F x) = x := by
    intro x
    by_cases hx : (x : Euclidean3) = 0
    · have hx0 : x = 0 := Subtype.ext hx
      rw [hx0, hF_zero, hG_zero]
    · apply Subtype.ext
      change ‖(F x : Euclidean3)‖ • (h.symm (n (F x)) : Euclidean3) = (x : Euclidean3)
      rw [hnF x hx, h.symm_apply_apply, hF_norm x]
      have hx0 : x ≠ (0 : B) := by
        intro hx'
        apply hx
        simpa [hx']
      simpa [n, hx0] using (NormedSpace.norm_smul_normalize (x : Euclidean3))
  have hFG : ∀ x : B, F (G x) = x := by
    intro x
    by_cases hx : (x : Euclidean3) = 0
    · have hx0 : x = 0 := Subtype.ext hx
      rw [hx0, hG_zero, hF_zero]
    · apply Subtype.ext
      change ‖(G x : Euclidean3)‖ • (h (n (G x)) : Euclidean3) = (x : Euclidean3)
      rw [hnG x hx, h.apply_symm_apply, hG_norm x]
      have hx0 : x ≠ (0 : B) := by
        intro hx'
        apply hx
        simpa [hx']
      simpa [n, hx0] using (NormedSpace.norm_smul_normalize (x : Euclidean3))
  let H : B ≃ₜ B :=
    { toEquiv :=
        { toFun := F
          invFun := G
          left_inv := hGF
          right_inv := hFG }
      continuous_toFun := hF_cont
      continuous_invFun := hG_cont }
  refine ⟨H, ?_⟩
  intro x
  let bx : B :=
    ⟨(x : Euclidean3), by
      have hx := x.property
      change dist (x : Euclidean3) 0 ≤ 1
      simpa [dist_zero_right] using (le_of_eq hx)⟩
  have hinput : (⟨x, by
      have hx := x.property
      change dist (x : Euclidean3) 0 ≤ 1
      simpa [dist_zero_right] using (le_of_eq hx)⟩ : B) = bx := by
    apply Subtype.ext
    rfl
  rw [hinput]
  have hxnorm : ‖(x : Euclidean3)‖ = 1 := mem_sphere_zero_iff_norm.1 x.property
  have hx0 : (x : Euclidean3) ≠ 0 := by
    intro hx
    rw [hx, norm_zero] at hxnorm
    norm_num at hxnorm
  have hnb : n bx = x := by
    apply Subtype.ext
    have hbx0 : bx ≠ (0 : B) := by
      intro hzero
      apply hx0
      simpa [bx] using congrArg (fun y : B => (y : Euclidean3)) hzero
    simp [n, bx, hbx0, NormedSpace.normalize_eq_self_of_norm_eq_one hxnorm]
  change ‖(bx : Euclidean3)‖ • (h (n bx) : Euclidean3) = (h x : Euclidean3)
  rw [hnb, hxnorm]
  simp
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
