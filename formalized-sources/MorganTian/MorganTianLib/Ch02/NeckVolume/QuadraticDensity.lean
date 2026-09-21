import MorganTianLib.Ch01.FrameChartDeterminant
import MorganTianLib.Ch01.OrthoFrame
import Mathlib.Analysis.Matrix.PosDef

open Set MeasureTheory Riemannian Matrix Function
open scoped ContDiff Manifold Topology ENNReal Bundle BigOperators

noncomputable section
namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A pointwise quadratic-form sandwich gives the actual chart-density sandwich. -/
theorem chartVolumeDensity_comparison_of_metricInner
    {g0 g : RiemannianMetric I M} {c0 c1 : ℝ}
    (hc0 : 0 ≤ c0) (hc1 : 0 ≤ c1)
    (alpha : M) {y : E} (hy : y ∈ (extChartAt I alpha).target)
    (hform : ∀ v : TangentSpace I ((extChartAt I alpha).symm y),
      c0 * g0.metricInner _ v v ≤ g.metricInner _ v v ∧
        g.metricInner _ v v ≤ c1 * g0.metricInner _ v v) :
    Real.sqrt (c0 ^ Module.finrank ℝ E) * chartVolumeDensity (I := I) g0 alpha y ≤
      chartVolumeDensity (I := I) g alpha y ∧
    chartVolumeDensity (I := I) g alpha y ≤
      Real.sqrt (c1 ^ Module.finrank ℝ E) * chartVolumeDensity (I := I) g0 alpha y := by
/- SWARM_PROOF_BEGIN -/
  classical
  let x : M := (extChartAt I alpha).symm y
  have hx : x ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    dsimp [x]
    rw [← extChartAt_source I]
    exact (extChartAt I alpha).map_target hy
  let e := orthoFrameBasis (I := I) g0 x (mem_orthoFrameSet_self x)
  let f : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun i => e i
  have hf (i j : Fin (Module.finrank ℝ E)) :
      g0.metricInner x (f i) (f j) = if i = j then 1 else 0 := by
    change g0.metricInner x (e i) (e j) = _
    dsimp [e]
    simpa only [RiemannianMetric.metricInner_apply, orthoFrameBasis_apply] using
      (orthoFrameField_orthonormal g0 x (mem_orthoFrameSet_self x) i j)
  let B : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ := Matrix.of fun i j =>
    g.metricInner x (f i) (f j)
  have hB : B.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa [B] using g.metricInner_comm x (f j) (f i)
  have hq0 (z : Fin (Module.finrank ℝ E) → ℝ) :
      g0.metricInner x (∑ i, z i • f i) (∑ j, z j • f j) = ∑ i, z i ^ 2 := by
    calc
      g0.metricInner x (∑ i, z i • f i) (∑ j, z j • f j) =
          ∑ i, z i * g0.metricInner x (f i) (∑ j, z j • f j) := by
        simpa using (metricInner_sum_smul_left g0 x (Finset.univ)
          z f (∑ j, z j • f j))
      _ = ∑ i, z i * (∑ j, z j * g0.metricInner x (f i) (f j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [metricInner_sum_smul_right]
      _ = ∑ i, z i ^ 2 := by
        simp only [RiemannianMetric.metricInner_apply] at hf ⊢
        simp [hf, pow_two]
  have hq (z w : Fin (Module.finrank ℝ E) → ℝ) :
      g.metricInner x (∑ i, z i • f i) (∑ j, w j • f j) =
        ∑ i, ∑ j, z i * w j * B i j := by
    calc
      g.metricInner x (∑ i, z i • f i) (∑ j, w j • f j) =
          ∑ i, z i * g.metricInner x (f i) (∑ j, w j • f j) := by
        simpa using (metricInner_sum_smul_left g x (Finset.univ)
          z f (∑ j, w j • f j))
      _ = ∑ i, z i * (∑ j, w j * g.metricInner x (f i) (f j)) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [metricInner_sum_smul_right]
      _ = ∑ i, ∑ j, z i * w j * B i j := by
        simp only [B, Matrix.of_apply]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have hquad (z : Fin (Module.finrank ℝ E) → ℝ) :
      (∑ i, ∑ j, z i * z j * B i j) = z ⬝ᵥ (B *ᵥ z) := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have heigen_lower : ∀ i : Fin (Module.finrank ℝ E), c0 ≤ hB.eigenvalues i := by
    intro i
    let z : Fin (Module.finrank ℝ E) → ℝ := hB.eigenvectorBasis i
    have hnorm : ∑ j, z j ^ 2 = 1 := by
      have hz := hB.eigenvectorBasis.orthonormal.1 i
      have hz' := congrArg (fun t : ℝ => t ^ 2) hz
      rw [EuclideanSpace.real_norm_sq_eq] at hz'
      simpa [z] using hz'
    have heq : g.metricInner x (∑ j, z j • f j) (∑ j, z j • f j) =
        hB.eigenvalues i := by
      rw [hq, hquad]
      change z ⬝ᵥ (B *ᵥ z) = _
      rw [hB.mulVec_eigenvectorBasis]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      calc
        (∑ j, z j * (hB.eigenvalues i * z j)) =
            ∑ j, hB.eigenvalues i * z j ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = hB.eigenvalues i * ∑ j, z j ^ 2 := by
          rw [Finset.mul_sum]
        _ = hB.eigenvalues i := by rw [hnorm, mul_one]
    have hineq := hform (∑ j, z j • f j)
    rw [hq0 z, hnorm, heq] at hineq
    nlinarith [hineq.1]
  have heigen_upper : ∀ i : Fin (Module.finrank ℝ E), hB.eigenvalues i ≤ c1 := by
    intro i
    let z : Fin (Module.finrank ℝ E) → ℝ := hB.eigenvectorBasis i
    have hnorm : ∑ j, z j ^ 2 = 1 := by
      have hz := hB.eigenvectorBasis.orthonormal.1 i
      have hz' := congrArg (fun t : ℝ => t ^ 2) hz
      rw [EuclideanSpace.real_norm_sq_eq] at hz'
      simpa [z] using hz'
    have heq : g.metricInner x (∑ j, z j • f j) (∑ j, z j • f j) =
        hB.eigenvalues i := by
      rw [hq, hquad]
      change z ⬝ᵥ (B *ᵥ z) = _
      rw [hB.mulVec_eigenvectorBasis]
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
      calc
        (∑ j, z j * (hB.eigenvalues i * z j)) =
            ∑ j, hB.eigenvalues i * z j ^ 2 := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = hB.eigenvalues i * ∑ j, z j ^ 2 := by
          rw [Finset.mul_sum]
        _ = hB.eigenvalues i := by rw [hnorm, mul_one]
    have hineq := hform (∑ j, z j • f j)
    rw [hq0 z, hnorm, heq] at hineq
    nlinarith [hineq.2]
  have hdet_lower : c0 ^ Module.finrank ℝ E ≤ B.det := by
    rw [hB.det_eq_prod_eigenvalues]
    simpa using (Finset.prod_le_prod (s := Finset.univ) (fun i _ => hc0)
      (fun i _ => heigen_lower i))
  have hdet_upper : B.det ≤ c1 ^ Module.finrank ℝ E := by
    rw [hB.det_eq_prod_eigenvalues]
    simpa using (Finset.prod_le_prod (s := Finset.univ)
      (fun i _ => hc0.trans (heigen_lower i))
      (fun i _ => heigen_upper i))
  let b := Riemannian.Tensor.chartBasisFamily (I := I) alpha hx
  let M := b.toMatrix f
  let G := Riemannian.Tensor.chartGramMatrix (I := I) g alpha x
  let G0 := Riemannian.Tensor.chartGramMatrix (I := I) g0 alpha x
  have hmid : Matrix.of (fun i j => g.metricInner x (b i) (b j)) = G := by
    ext i j
    dsimp [G, b]
    simp only [Riemannian.Tensor.chartBasisFamily_apply]
  have hmid0 : Matrix.of (fun i j => g0.metricInner x (b i) (b j)) = G0 := by
    ext i j
    dsimp [G0, b]
    simp only [Riemannian.Tensor.chartBasisFamily_apply]
  have hconj : B = Mᵀ * G * M := by
    have h := bilinGram_eq_conj b f (metricBilin (I := I) g x)
    change (Matrix.of fun i j => g.metricInner x (f i) (f j)) =
      (b.toMatrix f)ᵀ * (Matrix.of fun i j => g.metricInner x (b i) (b j)) *
        b.toMatrix f at h
    rw [hmid] at h
    simpa [B, M] using h
  have hdetrel : B.det = (M.det) ^ 2 * G.det := by
    rw [hconj, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    ring
  have hGpos : 0 < G.det := by
    exact Riemannian.Tensor.chartGramMatrix_det_pos (I := I) g alpha hx
  have hG0pos : 0 < G0.det := by
    exact Riemannian.Tensor.chartGramMatrix_det_pos (I := I) g0 alpha hx
  have hconj0 : (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) =
      Mᵀ * G0 * M := by
    have h := bilinGram_eq_conj b f (metricBilin (I := I) g0 x)
    change (Matrix.of fun i j => g0.metricInner x (f i) (f j)) =
      (b.toMatrix f)ᵀ * (Matrix.of fun i j => g0.metricInner x (b i) (b j)) *
        b.toMatrix f at h
    have hleft : Matrix.of (fun i j => g0.metricInner x (f i) (f j)) =
        (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
      ext i j
      simp only [Matrix.of_apply]
      rw [hf, Matrix.one_apply]
    rw [hleft, hmid0] at h
    simpa [M] using h
  have hsq0 : (M.det) ^ 2 * G0.det = 1 :=
    sq_det_mul_det_eq_one hconj0.symm
  have hframe0 : |M.det| * Real.sqrt G0.det = 1 :=
    abs_det_mul_sqrt_det_eq_one hG0pos hsq0
  have hsqrt : Real.sqrt B.det = |M.det| * Real.sqrt G.det := by
    rw [hdetrel, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  have hratio : Real.sqrt G.det = Real.sqrt B.det * Real.sqrt G0.det := by
    calc
      Real.sqrt G.det = 1 * Real.sqrt G.det := by ring
      _ = (|M.det| * Real.sqrt G0.det) * Real.sqrt G.det := by rw [hframe0]
      _ = Real.sqrt B.det * Real.sqrt G0.det := by rw [hsqrt]; ring
  have hdensity : chartVolumeDensity (I := I) g alpha y =
      Real.sqrt B.det * chartVolumeDensity (I := I) g0 alpha y := by
    simpa [chartVolumeDensity, x, G, G0] using hratio
  have hsqrt_lower : Real.sqrt (c0 ^ Module.finrank ℝ E) ≤ Real.sqrt B.det :=
    Real.sqrt_le_sqrt hdet_lower
  have hsqrt_upper : Real.sqrt B.det ≤ Real.sqrt (c1 ^ Module.finrank ℝ E) :=
    Real.sqrt_le_sqrt hdet_upper
  constructor
  · rw [hdensity]
    exact mul_le_mul_of_nonneg_right hsqrt_lower
      (by
        unfold chartVolumeDensity
        exact Real.sqrt_nonneg _)
  · rw [hdensity]
    exact mul_le_mul_of_nonneg_right hsqrt_upper
      (by
        unfold chartVolumeDensity
        exact Real.sqrt_nonneg _)
/- SWARM_PROOF_END -/

end MorganTianLib
