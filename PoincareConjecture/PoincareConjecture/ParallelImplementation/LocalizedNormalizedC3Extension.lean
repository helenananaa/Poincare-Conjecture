import Mathlib
import PoincareConjecture.ParallelImplementation.C3IteratedNormIdentification
import PoincareConjecture.ParallelImplementation.SmoothUnitBallCutoff
import PoincareConjecture.ParallelImplementation.CompactC3RescalingSmallness
import PoincareConjecture.ParallelImplementation.CompactCutoffC3ProductBound
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.LocalizedNormalizedC3Extension
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance stdGroup0 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance stdSpace0 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance stdGroup1 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace1 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdGroup2 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace2 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
theorem exists_localized_normalized_c3_extension
    (u : E3 → E6) (hu : ContDiff ℝ 3 u) (p : E3) (hp : u p=0)
    (epsilon : ℝ) (heps : 0 < epsilon) :

    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ U : E3 → E6,
      ContDiff ℝ 3 U ∧ HasCompactSupport U ∧
      (∀ x : E3, ‖x‖ ≤ 1 → U x=u (p+r • x)) ∧
      (∀ x : E3, 2 ≤ ‖x‖ → U x=0) ∧
      (∀ x : E3, ‖U x‖ ≤ epsilon) ∧ (∀ x : E3, ‖fderiv ℝ U x‖ ≤ epsilon) ∧
      (∀ x : E3, ‖fderiv ℝ (fderiv ℝ U) x‖ ≤ epsilon) ∧
      (∀ x : E3, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖ ≤ epsilon) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨χ, hχsmooth, hχcompact, hχrange, hχinner, hχouter, K, hKpos, hKbound⟩ :=
    SmoothUnitBallCutoff.exists_smooth_unit_ball_cutoff
  have hχ3 : ContDiff ℝ 3 χ :=
    hχsmooth.of_le
      (WithTop.coe_le_coe.mpr (show (3 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  let N : ℝ := epsilon / (8 * K)
  have hNpos : 0 < N := by
    dsimp [N]
    positivity
  obtain ⟨δ, hδpos, hδone, hδsmall⟩ :=
    CompactC3RescalingSmallness.compact_c3_rescaling_smallness
      u hu p hp (tsupport χ) hχcompact N hNpos
  let r : ℝ := δ
  let f : E3 → E6 := fun x => u (p + r • x)
  let U : E3 → E6 := fun x => χ x • f x
  have hf : ContDiff ℝ 3 f := by
    dsimp [f]
    fun_prop
  have hproduct :=
    CompactCutoffC3ProductBound.compact_cutoff_c3_product_bound
      χ hχ3 f hf K N (le_of_lt hKpos) (le_of_lt hNpos) hKbound
      (by
        intro k hk x hx
        apply hδsmall r
        · change |δ| ≤ δ
          rw [abs_of_nonneg hδpos.le]
        · exact hk
        · exact hx)
  have hbound : ∀ (k : ℕ), k ≤ 3 → ∀ x : E3,
      ‖iteratedFDeriv ℝ k U x‖ ≤ epsilon := by
    intro k hk x
    change ‖iteratedFDeriv ℝ k (fun y : E3 => χ y • f y) x‖ ≤ epsilon
    calc
      ‖iteratedFDeriv ℝ k (fun y : E3 => χ y • f y) x‖ ≤ 8 * K * N :=
        hproduct k hk x
      _ = epsilon := by
        dsimp [N]
        field_simp [ne_of_gt hKpos]
  have hUcont : ContDiff ℝ 3 U := by
    change ContDiff ℝ 3 (fun y : E3 => χ y • f y)
    exact hχ3.smul hf
  have hUcompact : HasCompactSupport U := by
    change HasCompactSupport (fun y : E3 => χ y • f y)
    exact hχcompact.smul_right
  refine ⟨r, ?_, ?_, U, hUcont, hUcompact, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hδpos
  · exact hδone
  · intro x hx
    change χ x • u (p + r • x) = u (p + r • x)
    rw [hχinner x hx, one_smul]
  · intro x hx
    change χ x • u (p + r • x) = 0
    rw [hχouter x hx]
    exact zero_smul ℝ (u (p + r • x))
  · intro x
    have hid := C3IteratedNormIdentification.c3_iterated_norms U x
    calc
      ‖U x‖ = ‖iteratedFDeriv ℝ 0 U x‖ := hid.1.symm
      _ ≤ epsilon := hbound 0 (by norm_num) x
  · intro x
    have hid := C3IteratedNormIdentification.c3_iterated_norms U x
    calc
      ‖fderiv ℝ U x‖ = ‖iteratedFDeriv ℝ 1 U x‖ := hid.2.1.symm
      _ ≤ epsilon := hbound 1 (by norm_num) x
  · intro x
    have hid := C3IteratedNormIdentification.c3_iterated_norms U x
    calc
      ‖fderiv ℝ (fderiv ℝ U) x‖ = ‖iteratedFDeriv ℝ 2 U x‖ := hid.2.2.1.symm
      _ ≤ epsilon := hbound 2 (by norm_num) x
  · intro x
    have hid := C3IteratedNormIdentification.c3_iterated_norms U x
    calc
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ U)) x‖ = ‖iteratedFDeriv ℝ 3 U x‖ :=
        hid.2.2.2.symm
      _ ≤ epsilon := hbound 3 (by norm_num) x
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.LocalizedNormalizedC3Extension
