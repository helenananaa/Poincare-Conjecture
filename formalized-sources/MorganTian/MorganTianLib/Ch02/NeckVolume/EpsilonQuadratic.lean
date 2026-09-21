import MorganTianLib.Ch02.EpsilonClose
import MorganTianLib.Ch01.CurvatureFrameBridge

open Set MeasureTheory Riemannian Matrix Function
open scoped ContDiff Manifold Topology ENNReal Bundle BigOperators

noncomputable section
namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Tensor-norm closeness bounds the actual metric quadratic forms. -/
theorem epsilonClose_metricInner_comparison
    {epsilon : ℝ} {g0 g : RiemannianMetric I M}
    (hclose : EpsilonClose epsilon g0 g) (p : M) (v : TangentSpace I p) :
    (1 - epsilon) * g0.metricInner p v v ≤ g.metricInner p v v ∧
      g.metricInner p v v ≤ (1 + epsilon) * g0.metricInner p v v := by
/- SWARM_PROOF_BEGIN -/
  rcases hclose with ⟨hepsilon, hepsilon_half, C, hC, hCp⟩
  have hderiv :
      0 ≤ ∑ l ∈ Finset.Icc 1 (epsilonDerivativeOrder epsilon),
        metricCovariantDerivativeNormSq g0 g l p := by
    apply Finset.sum_nonneg
    intro l hl
    unfold metricCovariantDerivativeNormSq
    exact Finset.sum_nonneg fun indices _ => sq_nonneg _
  have hzero : metricCovariantDerivativeNormSq g0 g 0 p < epsilon ^ 2 := by
    have h0 : metricCovariantDerivativeNormSq g0 g 0 p ≤
        epsilonClosenessDensity epsilon g0 g p := by
      unfold epsilonClosenessDensity
      linarith
    exact lt_of_le_of_lt (h0.trans (hCp p)) hC

  let e : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => orthoFrameField g0 p i p
  let a : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => g0.metricInner p v (e i)
  let A : (Fin 2 → Fin (Module.finrank ℝ E)) → ℝ :=
    fun ij => g.metricInner p (e (ij 0)) (e (ij 1)) -
      g0.metricInner p (e (ij 0)) (e (ij 1))
  let D : (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) → ℝ :=
    fun ij => g.metricInner p (e ij.1) (e ij.2) -
      g0.metricInner p (e ij.1) (e ij.2)

  have hA : (∑ ij : Fin 2 → Fin (Module.finrank ℝ E), A ij ^ 2) < epsilon ^ 2 := by
    simpa [metricCovariantDerivativeNormSq, iteratedCovariantMetricDifference, A, e] using hzero
  have hD :
      (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), D ij ^ 2) <
        epsilon ^ 2 := by
    calc
      (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), D ij ^ 2) =
          ∑ ij : Fin 2 → Fin (Module.finrank ℝ E), A ij ^ 2 := by
            symm
            refine Fintype.sum_equiv (piFinTwoEquiv (fun _ => Fin (Module.finrank ℝ E)))
              _ _ ?_
            intro ij
            rfl
      _ < epsilon ^ 2 := hA

  have hv : v = ∑ i, a i • e i := by
    simpa [a, e] using
      (orthoFrameField_expansion g0 p
        (mem_orthoFrameSet_self (I := I) p) v)
  have hq : (∑ i : Fin (Module.finrank ℝ E), a i ^ 2) =
      g0.metricInner p v v := by
    calc
      (∑ i : Fin (Module.finrank ℝ E), a i ^ 2) =
          ∑ i, a i * g0.metricInner p (e i) v := by
            apply Finset.sum_congr rfl
            intro i hi
            change (g0.metricInner p v (e i)) ^ 2 =
              g0.metricInner p v (e i) * g0.metricInner p (e i) v
            rw [g0.metricInner_comm p (e i) v]
            ring
      _ = g0.metricInner p (∑ i, a i • e i) v := by
            rw [metricInner_sum_smul_left]
      _ = g0.metricInner p v v := by rw [← hv]

  have hbilin (k : RiemannianMetric I M) :
      k.metricInner p v v =
        ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (a ij.1 * a ij.2) * k.metricInner p (e ij.1) (e ij.2) := by
    simp only [hv]
    rw [metricInner_sum_smul_left]
    simp_rw [metricInner_sum_smul_right k p
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) a]
    rw [Fintype.sum_prod_type]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

  have hdiff :
      g.metricInner p v v - g0.metricInner p v v =
        ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (a ij.1 * a ij.2) * D ij := by
    rw [hbilin g, hbilin g0]
    unfold D
    calc
      (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          a ij.1 * a ij.2 * g.metricInner p (e ij.1) (e ij.2)) -
          ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            a ij.1 * a ij.2 * g0.metricInner p (e ij.1) (e ij.2) =
        ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ((a ij.1 * a ij.2 * g.metricInner p (e ij.1) (e ij.2)) -
            (a ij.1 * a ij.2 * g0.metricInner p (e ij.1) (e ij.2))) := by
              symm
              rw [Finset.sum_sub_distrib]
      _ = ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          a ij.1 * a ij.2 *
            (g.metricInner p (e ij.1) (e ij.2) -
              g0.metricInner p (e ij.1) (e ij.2)) := by
            apply Finset.sum_congr rfl
            intro ij hij
            ring

  have hCS :
      (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        (a ij.1 * a ij.2) * D ij) ^ 2 ≤
        (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          (a ij.1 * a ij.2) ^ 2) * ∑ ij, D ij ^ 2 := by
    simpa using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)))
        (fun ij => a ij.1 * a ij.2) (fun ij => D ij))
  have hcoeff :
      (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        (a ij.1 * a ij.2) ^ 2) =
        (∑ i : Fin (Module.finrank ℝ E), a i ^ 2) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [mul_pow]
    calc
      (∑ i, ∑ j, a i ^ 2 * a j ^ 2) =
          ∑ i, a i ^ 2 * (∑ j, a j ^ 2) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
      _ = (∑ i, a i ^ 2) * (∑ j, a j ^ 2) := by
            rw [Finset.sum_mul]
      _ = (∑ i, a i ^ 2) ^ 2 := by ring

  have hdiff_sq :
      (g.metricInner p v v - g0.metricInner p v v) ^ 2 ≤
        (epsilon * g0.metricInner p v v) ^ 2 := by
    have hsqle :
        (g.metricInner p v v - g0.metricInner p v v) ^ 2 ≤
          (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            (a ij.1 * a ij.2) ^ 2) * ∑ ij, D ij ^ 2 := by
      rw [hdiff]
      exact hCS
    have hprod :
        (∑ i : Fin (Module.finrank ℝ E), a i ^ 2) ^ 2 *
            (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), D ij ^ 2) ≤
          (∑ i : Fin (Module.finrank ℝ E), a i ^ 2) ^ 2 * epsilon ^ 2 :=
      mul_le_mul_of_nonneg_left hD.le (sq_nonneg _)
    rw [hcoeff] at hsqle
    rw [hq] at hsqle hprod
    calc
      (g.metricInner p v v - g0.metricInner p v v) ^ 2 ≤
          g0.metricInner p v v ^ 2 *
            (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E), D ij ^ 2) := hsqle
      _ ≤ g0.metricInner p v v ^ 2 * epsilon ^ 2 := hprod
      _ = (epsilon * g0.metricInner p v v) ^ 2 := by ring
  have hdiff_abs :
      |g.metricInner p v v - g0.metricInner p v v| ≤
        epsilon * g0.metricInner p v v := by
    have hright : 0 ≤ epsilon * g0.metricInner p v v :=
      mul_nonneg hepsilon.le (g0.metricInner_self_nonneg p v)
    exact abs_le_of_sq_le_sq hdiff_sq hright
  have hdiff_bounds := (abs_le.mp hdiff_abs)
  constructor <;> nlinarith [hdiff_bounds.1, hdiff_bounds.2]
/- SWARM_PROOF_END -/

end MorganTianLib
