import PoincareConjecture.ProofContract.Proofs.DoubleBallCore
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open V1 Set Function Topology
open scoped Topology Manifold ContDiff
/-- A concrete collar-supported extension of a sphere map into the closed ball. -/
theorem radial_capping_extension (h : Sphere2 ≃ₜ Sphere2) :
    ∃ F : C({x : Euclidean3 // 1 ≤ ‖x‖}, DoubleBall.Ball),
      (∀ s : Sphere2, (F ⟨s, by simpa only [Metric.mem_sphere, dist_zero_right] using
        (le_of_eq s.property.symm)⟩ : Euclidean3) = (h s : Euclidean3)) ∧
      ∀ x : {x : Euclidean3 // 1 ≤ ‖x‖}, 2 ≤ ‖(x : Euclidean3)‖ → (F x : Euclidean3) = 0 :=
/- SWARM_PROOF_BEGIN -/
by
  let D := {x : Euclidean3 // 1 ≤ ‖x‖}
  let r : D → ℝ := fun x => max 0 (2 - ‖(x : Euclidean3)‖)
  have hnorm : Continuous (fun x : D => ‖(x : Euclidean3)‖) :=
    continuous_norm.comp continuous_subtype_val
  have hnorm0 : ∀ x : D, ‖(x : Euclidean3)‖ ≠ 0 := by
    intro x
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one x.property)
  have hnvec : Continuous (fun x : D =>
      (‖(x : Euclidean3)‖ : ℝ)⁻¹ • (x : Euclidean3)) := by
    exact (hnorm.inv₀ hnorm0).smul continuous_subtype_val
  have hnmem : ∀ x : D, (‖(x : Euclidean3)‖ : ℝ)⁻¹ •
      (x : Euclidean3) ∈ Sphere2 := by
    intro x
    rw [Metric.mem_sphere, dist_zero_right, norm_smul]
    simp [hnorm0 x, norm_nonneg]
  let n : D → Sphere2 := fun x =>
    ⟨(‖(x : Euclidean3)‖ : ℝ)⁻¹ • (x : Euclidean3), hnmem x⟩
  have hn : Continuous n := hnvec.subtype_mk hnmem
  have hr : Continuous r := by
    change Continuous (fun x : D => max 0 (2 - ‖(x : Euclidean3)‖))
    exact (continuous_const.max (continuous_const.sub hnorm))
  have hg : Continuous (fun x : D => (h (n x) : Euclidean3)) := by
    exact continuous_subtype_val.comp (h.continuous.comp hn)
  have hf : Continuous (fun x : D => r x • (h (n x) : Euclidean3)) :=
    hr.smul hg
  have hr_nonneg : ∀ x : D, 0 ≤ r x := by
    intro x
    exact le_max_left _ _
  have hr_le_one : ∀ x : D, r x ≤ 1 := by
    intro x
    apply max_le
    · norm_num
    · linarith [x.property]
  have hball : ∀ x : D, r x • (h (n x) : Euclidean3) ∈ DoubleBall.Ball := by
    intro x
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul]
    have hh : ‖(h (n x) : Euclidean3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using (h (n x)).property
    rw [Real.norm_of_nonneg (hr_nonneg x), hh, mul_one]
    exact hr_le_one x
  let F : C(D, DoubleBall.Ball) := ContinuousMap.mk
    (fun x => ⟨r x • (h (n x) : Euclidean3), hball x⟩)
    (hf.subtype_mk hball)
  refine ⟨F, ?_, ?_⟩
  · intro s
    have hs_norm : ‖(s : Euclidean3)‖ = 1 := by
      simpa [Metric.mem_sphere, dist_zero_right] using s.property
    have hns : n ⟨(s : Euclidean3), by simpa using (le_of_eq s.property.symm)⟩ = s := by
      apply Subtype.ext
      simp [n, hs_norm]
    have hrs : r ⟨(s : Euclidean3), by simpa using (le_of_eq s.property.symm)⟩ = 1 := by
      norm_num [r, hs_norm]
    simp [F, hns, hrs]
  · intro x hx
    have hrx : r x = 0 := by
      simp [r, max_eq_left (sub_nonpos.mpr hx)]
    simp [F, hrx]
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
