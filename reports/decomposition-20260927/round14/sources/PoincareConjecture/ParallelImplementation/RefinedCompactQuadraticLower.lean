import PoincareConjecture.ProofContract.Refinement20260927.CompactMetricComparison
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCompactQuadraticLower
open PoincareConjecture.ProofContract.Refinement20260927
theorem compact_quadratic_lower : CompactQuadraticLowerStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro X instMetric instCompact instNonempty Q hQ hpos
  let E := PoincareConjecture.ProofContract.V1.Euclidean3
  let S : Set E := Metric.sphere (0 : E) 1
  let K : Set (X × E) := Set.univ ×ˢ S
  let f : X × E → ℝ := fun p => quadraticValue (Q p.1) p.2
  have hSphereCompact : IsCompact S := by
    dsimp [S]
    exact isCompact_sphere (0 : E) 1
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_univ.prod hSphereCompact
  let e : E := EuclideanSpace.single 0 1
  have he : e ∈ S := by
    dsimp [S, e]
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
    rw [EuclideanSpace.norm_single, norm_one]
  have hKne : K.Nonempty := by
    refine ⟨(Classical.choice instNonempty, e), ?_⟩
    exact ⟨Set.mem_univ _, he⟩
  have hf : Continuous f := by
    dsimp [f, quadraticValue]
    have happly : Continuous (fun p : X × E => Q p.1 p.2) :=
      hQ.comp continuous_fst |>.clm_apply continuous_snd
    exact continuous_inner.comp (happly.prodMk continuous_snd)
  obtain ⟨p, hpK, hpmin⟩ := hKcompact.exists_isMinOn hKne hf.continuousOn
  have hpunit : ‖p.2‖ = 1 := by
    have h := hpK.2
    simpa [S, Metric.mem_sphere, dist_eq_norm] using h
  have hpne : p.2 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hpunit
    norm_num at hpunit
  have hmpos : 0 < f p := by
    exact hpos p.1 p.2 hpne
  refine ⟨f p, hmpos, ?_⟩
  intro x v
  by_cases hv : v = 0
  · simp [hv, quadraticValue]
  · have hrpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let r : ℝ := ‖v‖
    let w : E := r⁻¹ • v
    have hwnorm : ‖w‖ = 1 := by
      dsimp [w, r]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrpos)]
      rw [inv_mul_cancel₀ (ne_of_gt hrpos)]
    have hwK : (x, w) ∈ K := by
      refine ⟨Set.mem_univ _, ?_⟩
      simpa [S, Metric.mem_sphere, dist_eq_norm] using hwnorm
    have hmin : f p ≤ f (x, w) := hpmin hwK
    have hvscale : v = r • w := by
      dsimp [w, r]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hrpos), one_smul]
    have hqscale : quadraticValue (Q x) v =
        r ^ 2 * quadraticValue (Q x) w := by
      change inner ℝ ((Q x) v) v = _
      rw [hvscale, map_smul, inner_smul_left, inner_smul_right]
      simp [quadraticValue, pow_two]
      ring
    change f p ≤ quadraticValue (Q x) w at hmin
    change (f p) * ‖v‖ ^ 2 ≤ quadraticValue (Q x) v
    calc
      f p * ‖v‖ ^ 2 = f p * r ^ 2 := by rfl
      _ ≤ quadraticValue (Q x) w * r ^ 2 :=
        mul_le_mul_of_nonneg_right hmin (sq_nonneg r)
      _ = quadraticValue (Q x) v := by rw [hqscale]; ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCompactQuadraticLower
