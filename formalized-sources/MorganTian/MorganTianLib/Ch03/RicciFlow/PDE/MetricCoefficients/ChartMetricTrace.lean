import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCoefficientOperator
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.OperatorMatrixInverse
import MorganTianLib.Ch01.InvGramTrace
import MorganTianLib.Ch01.PointwiseCurvature
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "JBg" => J3 × (T3 × (Fin 3 → T3))
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** chart metric trace. -/
theorem chart_metric_trace {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M] (g : Riemannian.RiemannianMetric (𝓡 3) M) (a p : M)
    (hp : p ∈ (chartAt E3 a).source) (e : Fin 3 ≃ Fin (Module.finrank ℝ E3))
    (D : TangentSpace (𝓡 3) p →ₗ[ℝ] TangentSpace (𝓡 3) p →ₗ[ℝ] TangentSpace (𝓡 3) p) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) := ⟨g.toRiemannianMetric⟩;
    let b := stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p);
    let A := chartCoefficientOperator g a p e;
    let v := fun k : Fin 3 => Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p;
    (∑ i, D (b i) (b i)) = ∑ i : Fin 3, ∑ j : Fin 3,
      (A.inverse (EuclideanSpace.single j 1)) i • D (v i) (v j) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change
    (∑ i : Fin (Module.finrank ℝ E3),
      D (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p) i)
        (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p) i)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (chartCoefficientOperator g a p e).inverse (EuclideanSpace.single j 1) i •
          D (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
            (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p)
  let b := stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p)
  let v := Riemannian.Tensor.chartBasisFamily (I := 𝓡 3) a hp
  let b₃ := b.reindex e.symm
  let v₃ := v.reindex e.symm
  let A := chartCoefficientOperator g a p e
  let Q : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) (e j)
  let C : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => (A.inverse (EuclideanSpace.single j 1)) i
  let Qinv : Matrix (Fin 3) (Fin 3) ℝ :=
    fun i j => Riemannian.Tensor.chartInvGramMatrix (I := 𝓡 3) g a p (e i) (e j)
  have hbase : p ∈
      (trivializationAt E3 (TangentSpace (𝓡 3)) a).baseSet := hp
  have hG : ∀ i j : Fin 3, Q i j = inner ℝ (v₃ i) (v₃ j) := by
    intro i j
    have hvi : v₃ i = v (e i) := by simp [v₃]
    have hvj : v₃ j = v (e j) := by simp [v₃]
    rw [hvi, hvj]
    dsimp only [Q]
    rw [Riemannian.Tensor.chartBasisFamily_apply,
      Riemannian.Tensor.chartBasisFamily_apply]
    exact (Riemannian.Tensor.chartGramMatrix_apply (I := 𝓡 3) g a p (e i) (e j)).symm
  have hQ : Q =
      (Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p).reindex e.symm e.symm := by
    ext i j
    rfl
  have hQinv : Q⁻¹ = Qinv := by
    rw [hQ, Matrix.inv_reindex]
    ext i j
    rfl
  have hprod := Riemannian.Tensor.chartGramMatrix_mul_chartInvGramMatrix
    (I := 𝓡 3) g a hbase
  have hQprod : Q * Qinv = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Q, Qinv]
    calc
      (∑ k : Fin 3,
          Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) (e k) *
            Riemannian.Tensor.chartInvGramMatrix (I := 𝓡 3) g a p (e k) (e j)) =
          ∑ m : Fin (Module.finrank ℝ E3),
            Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) m *
              Riemannian.Tensor.chartInvGramMatrix (I := 𝓡 3) g a p m (e j) := by
        exact Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = (Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p *
          Riemannian.Tensor.chartInvGramMatrix (I := 𝓡 3) g a p) (e i) (e j) := by
        rw [Matrix.mul_apply]
      _ = (1 : Matrix (Fin (Module.finrank ℝ E3))
          (Fin (Module.finrank ℝ E3)) ℝ) (e i) (e j) := by rw [hprod]
      _ = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        rw [Matrix.one_apply, Matrix.one_apply]
        exact if_congr e.injective.eq_iff rfl rfl
  obtain ⟨c, hc, hcoercive, _⟩ :=
    chart_coefficient_coercivity g a p e hbase
  have htoCLM (B : Matrix (Fin 3) (Fin 3) ℝ) :
      (fun i j : Fin 3 =>
        (Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ) B
          (EuclideanSpace.single j 1)) i) = B := by
    ext i j
    change ((Matrix.toLin (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis B)
        (EuclideanSpace.single j 1)).ofLp i = B i j
    rw [Matrix.toLin_apply]
    simp [EuclideanSpace.basisFun_apply, Matrix.mulVec, dotProduct,
      Pi.single_apply]
  have hentries :
      (fun i j : Fin 3 => (A (EuclideanSpace.single j 1)) i) = Q := by
    simpa [A, chartCoefficientOperator, Q] using htoCLM Q
  have hinv := operator_matrix_inverse A c hc hcoercive
  have hAinv : C = Q⁻¹ := by
    calc
      C = @Inv.inv (Matrix (Fin 3) (Fin 3) ℝ) Matrix.inv
          (fun i j : Fin 3 => (A (EuclideanSpace.single j 1)) i) := hinv
      _ = Q⁻¹ := by rw [hentries]
  have hGinv : Q * C = 1 := by
    rw [hAinv, hQinv]
    exact hQprod
  have htrace := MorganTianLib.sum_orthonormalBasis_diagonal_eq_invGram
    b₃ v₃ D hG hGinv
  have hleft :
      (∑ i : Fin (Module.finrank ℝ E3), D (b i) (b i)) =
        ∑ i : Fin 3, D (b₃ i) (b₃ i) := by
    have hb₃ (i : Fin 3) : b₃ i = b (e i) := by
      simp [b₃]
      rfl
    simp_rw [hb₃]
    exact Fintype.sum_equiv e.symm _ _ (by intro i; simp)
  calc
    (∑ i : Fin (Module.finrank ℝ E3), D (b i) (b i)) =
        ∑ i : Fin 3, D (b₃ i) (b₃ i) := hleft
    _ = ∑ i : Fin 3, ∑ j : Fin 3, C i j • D (v₃ i) (v₃ j) := htrace
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        (A.inverse (EuclideanSpace.single j 1)) i •
          D (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
            (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) := by
      simp [C, v₃, v, Riemannian.Tensor.chartBasisFamily_apply]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
