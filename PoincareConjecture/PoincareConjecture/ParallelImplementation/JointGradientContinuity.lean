import PoincareConjecture.ParallelImplementation.GradientFiniteDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.JointGradientContinuity
open scoped Topology ContDiff BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Joint continuity of values and a uniform true Hessian bound imply joint gradient continuity. -/
theorem joint_gradient_continuity
    {P V : Type*} [TopologicalSpace P] [NormedAddCommGroup V]
    [NormedSpace ℝ V] [CompleteSpace V]
    (f : P → E3 → V) (hf : Continuous (fun p : P × E3 => f p.1 p.2))
    (hC2 : ∀ p, ContDiff ℝ 2 (f p))
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ p x, ‖fderiv ℝ (fderiv ℝ (f p)) x‖ ≤ M) :
    Continuous (fun p : P × E3 => fderiv ℝ (f p.1) p.2) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let e : Fin 3 → E3 := fun i => EuclideanSpace.single i 1
  let r : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let col : ℕ → Fin 3 → P × E3 → V := fun n i q =>
    (r n)⁻¹ • (f q.1 (q.2 + r n • e i) - f q.1 q.2)
  let approx : ℕ → P × E3 → E3 →L[ℝ] V := fun n q =>
    ∑ i : Fin 3, (EuclideanSpace.proj i).smulRight (col n i q)
  let grad : P × E3 → E3 →L[ℝ] V := fun q => fderiv ℝ (f q.1) q.2
  have hrpos (n : ℕ) : 0 < r n := by
    dsimp [r]
    positivity
  have hcol_cont (n : ℕ) (i : Fin 3) : Continuous (col n i) := by
    have hshift : Continuous (fun q : P × E3 => (q.1, q.2 + r n • e i)) := by
      exact Continuous.prodMk continuous_fst (continuous_snd.add continuous_const)
    dsimp [col]
    exact (continuous_const_smul ((r n)⁻¹)).comp
      ((hf.comp hshift).sub hf)
  have happ_cont (n : ℕ) : Continuous (approx n) := by
    dsimp [approx]
    refine continuous_finsetSum Finset.univ ?_
    intro i hi
    exact (ContinuousLinearMap.smulRightL ℝ E3 V).continuous₂.comp
      (Continuous.prodMk continuous_const (hcol_cont n i))
  have hdecomp (v : E3) : v = ∑ i : Fin 3, v i • e i := by
    simpa [e, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm
  have hcoord (v : E3) (i : Fin 3) : ‖v i‖ ≤ ‖v‖ := by
    simpa using (PiLp.norm_apply_le v i)
  have hcol_error (n : ℕ) (i : Fin 3) (q : P × E3) :
      ‖grad q (e i) - col n i q‖ ≤ M * r n := by
    simpa [grad, e, col] using GradientFiniteDifference.gradient_finite_difference_error
      (f q.1) (hC2 q.1) M (r n) hM (hrpos n) (hbound q.1) q.2 i
  have happrox_error (n : ℕ) (q : P × E3) :
      ‖approx n q - grad q‖ ≤ 3 * M * r n := by
    have happrox_col (i : Fin 3) : approx n q (e i) = col n i q := by
      dsimp [approx]
      simp [e]
    have hexpand : approx n q - grad q =
        ∑ i : Fin 3, (EuclideanSpace.proj i).smulRight
          (col n i q - grad q (e i)) := by
      ext v
      calc
        (approx n q - grad q) v =
            (approx n q - grad q) (∑ i : Fin 3, v i • e i) :=
          congrArg (approx n q - grad q) (hdecomp v)
        _ = ∑ i : Fin 3, v i • (approx n q - grad q) (e i) := by simp
        _ = ∑ i : Fin 3, v i • (col n i q - grad q (e i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [sub_apply, happrox_col]
    have hval (v : E3) :
        ‖(approx n q - grad q) v‖ ≤ (3 * M * r n) * ‖v‖ := by
      rw [hexpand]
      calc
        ‖∑ i : Fin 3, (EuclideanSpace.proj i) v •
            (col n i q - grad q (e i))‖ ≤
              ∑ i : Fin 3, ‖(EuclideanSpace.proj i) v •
                (col n i q - grad q (e i))‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin 3, ‖v‖ * (M * r n) := by
          apply Finset.sum_le_sum
          intro i hi
          rw [norm_smul]
          have hscalar : ‖(EuclideanSpace.proj i) v‖ ≤ ‖v‖ := by
            simpa using hcoord v i
          have hrev : ‖col n i q - grad q (e i)‖ ≤ M * r n := by
            simpa [norm_sub_rev] using hcol_error n i q
          exact mul_le_mul hscalar hrev (norm_nonneg _) (norm_nonneg _)
        _ = (3 * M * r n) * ‖v‖ := by simp; ring
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    exact hval v
  have hrseq : Filter.Tendsto (fun n : ℕ => r n) Filter.atTop (𝓝 0) := by
    change Filter.Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) Filter.atTop (𝓝 0)
    exact (tendsto_inv_atTop_zero.comp
      (Filter.tendsto_atTop_add_const_right Filter.atTop 1
        tendsto_natCast_atTop_atTop)).congr fun n => by simp
  have hErrSeq : Filter.Tendsto (fun n : ℕ => 3 * M * r n) Filter.atTop (𝓝 0) := by
    simpa [mul_assoc] using hrseq.const_mul (3 * M)
  change Continuous grad
  apply continuous_iff_continuousAt.mpr
  intro q
  rw [Metric.continuousAt_iff']
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  have hsmall : ∀ᶠ n : ℕ in Filter.atTop, 3 * M * r n < ε / 3 := by
    filter_upwards [(Metric.tendsto_nhds.mp hErrSeq) (ε / 3) hε3] with n hn
    have hnonneg : 0 ≤ 3 * M * r n := by positivity
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_mul, abs_of_nonneg hM,
      abs_of_nonneg (le_of_lt (hrpos n))] using hn
  obtain ⟨n, hn⟩ := hsmall.exists
  have hnerr : 3 * M * r n < ε / 3 := hn
  have hAn : ContinuousAt (approx n) q := (happ_cont n).continuousAt
  have hev : ∀ᶠ z : P × E3 in 𝓝 q,
      dist (approx n z) (approx n q) < ε / 3 :=
    (Metric.tendsto_nhds.mp hAn) (ε / 3) hε3
  filter_upwards [hev] with z hz
  have hleft : dist (grad z) (approx n z) ≤ 3 * M * r n := by
    rw [dist_eq_norm]
    simpa [norm_sub_rev] using happrox_error n z
  have hright : dist (approx n q) (grad q) ≤ 3 * M * r n := by
    rw [dist_eq_norm]
    exact happrox_error n q
  have hmid : dist (approx n z) (grad q) ≤
      dist (approx n z) (approx n q) + 3 * M * r n := by
    calc
      dist (approx n z) (grad q) ≤
          dist (approx n z) (approx n q) + dist (approx n q) (grad q) :=
        dist_triangle _ _ _
      _ ≤ dist (approx n z) (approx n q) + 3 * M * r n :=
        by nlinarith [hright]
  calc
    dist (grad z) (grad q) ≤
        dist (grad z) (approx n z) + dist (approx n z) (grad q) := dist_triangle _ _ _
    _ ≤ 3 * M * r n + (dist (approx n z) (approx n q) + 3 * M * r n) :=
      add_le_add hleft hmid
    _ < ε := by nlinarith [hnerr, hz]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.JointGradientContinuity
