import Mathlib
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OpenPositiveOperatorExtension
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_open_positive_operator_extension
    (s : Set E3) (hs : IsOpen s) (p : E3) (hp : p ∈ s)
    (A : E3 → (E3 →L[ℝ] E3)) (hA : ContDiffOn ℝ ∞ A s)
    (hsym : ∀ x ∈ s, ∀ v w : E3, inner ℝ (A x v) w=inner ℝ (A x w) v)
    (hpos : ∀ x ∈ s, ∀ v : E3, v ≠ 0 → 0 < inner ℝ (A x v) v) :

    ∃ rho : ℝ, 0 < rho ∧ Metric.closedBall p rho ⊆ s ∧
    ∃ B : E3 → (E3 →L[ℝ] E3), ContDiff ℝ ∞ B ∧
      (∀ x ∈ Metric.closedBall p rho, B x=A x) ∧ HasCompactSupport (fun x => B x-1) ∧
      (∀ x v w : E3, inner ℝ (B x v) w=inner ℝ (B x w) v) ∧
      ∀ x v : E3, v ≠ 0 → 0 < inner ℝ (B x v) v :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hs.mem_nhds hp)
  let bump : ContDiffBump p := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let χ : E3 → ℝ := bump
  have hχsmooth : ContDiff ℝ ∞ χ := bump.contDiff (n := ⊤)
  have hχtsupp : tsupport χ = Metric.closedBall p (ε / 2) := by
    simpa [χ, bump] using bump.tsupport_eq
  have hχsupp : Function.support χ = Metric.ball p (ε / 2) := by
    simpa [χ, bump] using bump.support_eq
  have htsupp : tsupport χ ⊆ s := by
    rw [hχtsupp]
    exact (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hχcompact : IsCompact (tsupport χ) := by
    rw [hχtsupp]
    exact isCompact_closedBall p (ε / 2)
  have hχne_mem_s : ∀ x : E3, χ x ≠ 0 → x ∈ s := by
    intro x hχx
    have hxball : x ∈ Metric.ball p (ε / 2) := by
      rw [← hχsupp]
      change χ x ≠ 0
      exact hχx
    exact hball ((Metric.ball_subset_ball (by linarith)) hxball)
  let B : E3 → (E3 →L[ℝ] E3) := fun x =>
    (1 : E3 →L[ℝ] E3) + χ x • (A x - 1)
  have hBformula (x v : E3) :
      B x v = (1 - χ x) • v + χ x • A x v := by
    simp [B, sub_smul]
    module
  have hBinner (x v w : E3) :
      inner ℝ (B x v) w =
        (1 - χ x) * inner ℝ v w + χ x * inner ℝ (A x v) w := by
    simp [hBformula x v, inner_add_left, inner_smul_left]
  have hBsym : ∀ x v w : E3, inner ℝ (B x v) w = inner ℝ (B x w) v := by
    intro x v w
    by_cases hχzero : χ x = 0
    · rw [hBinner x v w, hBinner x w v]
      simp [hχzero, real_inner_comm]
    · have hx_s : x ∈ s := hχne_mem_s x hχzero
      calc
        inner ℝ (B x v) w =
            (1 - χ x) * inner ℝ v w + χ x * inner ℝ (A x v) w := hBinner x v w
        _ = (1 - χ x) * inner ℝ w v + χ x * inner ℝ (A x w) v := by
          rw [real_inner_comm v w, hsym x hx_s v w]
        _ = inner ℝ (B x w) v := (hBinner x w v).symm
  have hBsmooth : ContDiff ℝ ∞ B := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ s
    · have hAx : ContDiffAt ℝ ∞ A x := (hA x hx).contDiffAt (hs.mem_nhds hx)
      have hχx : ContDiffAt ℝ ∞ χ x := hχsmooth.contDiffAt
      change ContDiffAt ℝ ∞ (fun y =>
        (1 : E3 →L[ℝ] E3) + χ y • (A y - 1)) x
      exact contDiffAt_const.add (hχx.smul (hAx.sub contDiffAt_const))
    · have hnot : x ∉ tsupport χ := fun h => hx (htsupp h)
      have hχzero : χ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) :=
        (notMem_tsupport_iff_eventuallyEq).mp hnot
      have hBeq : B =ᶠ[𝓝 x] (fun _ => (1 : E3 →L[ℝ] E3)) := by
        filter_upwards [hχzero] with y hy
        simp [B, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hBeq
  refine ⟨ε / 4, by positivity, ?_, B, hBsmooth, ?_, ?_, hBsym, ?_⟩
  · exact (Metric.closedBall_subset_ball (by linarith)).trans hball
  · intro x hx
    have hb1 : χ x = 1 := by
      apply bump.one_of_mem_closedBall
      simpa [bump] using hx
    simp [B, hb1]
  · have hBcompact : HasCompactSupport (fun x => B x - 1) := by
      apply HasCompactSupport.of_support_subset_isCompact hχcompact
      intro x hx
      have hχx : χ x ≠ 0 := by
        intro hz
        apply hx
        simp [B, hz]
      have hx_support : x ∈ Function.support χ := by
        change χ x ≠ 0
        exact hχx
      exact subset_closure hx_support
    exact hBcompact
  · intro x v hv
    by_cases hχzero : χ x = 0
    · have hnorm : 0 < inner ℝ v v := by
        rw [real_inner_self_eq_norm_sq]
        exact pow_pos (norm_pos_iff.mpr hv) 2
      simpa [hBformula x v, hχzero] using hnorm
    · by_cases hχone : χ x = 1
      · have hx_s : x ∈ s := hχne_mem_s x (by rw [hχone]; exact one_ne_zero)
        simpa [hBformula x v, hχone] using hpos x hx_s v hv
      · have hx_s : x ∈ s := hχne_mem_s x hχzero
        have hχpos : 0 < χ x := by
          by_contra h
          exact hχzero (le_antisymm (le_of_not_gt h) (bump.nonneg))
        have hχlt : χ x < 1 := by
          by_contra h
          exact hχone (le_antisymm bump.le_one (le_of_not_gt h))
        have hcoefpos : 0 < 1 - χ x := by linarith
        have hnorm : 0 < inner ℝ v v := by
          rw [real_inner_self_eq_norm_sq]
          exact pow_pos (norm_pos_iff.mpr hv) 2
        have hApos : 0 < inner ℝ (A x v) v := hpos x hx_s v hv
        rw [hBinner x v v]
        exact add_pos (mul_pos hcoefpos hnorm) (mul_pos hχpos hApos)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OpenPositiveOperatorExtension
