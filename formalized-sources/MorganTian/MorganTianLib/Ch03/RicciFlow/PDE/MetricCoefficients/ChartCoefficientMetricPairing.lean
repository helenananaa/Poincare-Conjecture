import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ChartCoefficientOperator
import MorganTianLib.Ch01.CurvatureFrameBridge
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** chart coefficient metric pairing. -/
theorem chart_coefficient_metric_pairing {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M) (a p : M)
    (e : Fin 3 ≃ Fin (Module.finrank ℝ E3)) (U V : E3) :
    g.metricInner p
      (∑ k : Fin 3, U k • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p)
      (∑ k : Fin 3, V k • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e k) p) =
      inner ℝ (chartCoefficientOperator g a p e U) V :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rw [metricInner_sum_smul_left]
  have hright : ∀ i : Fin 3, g.metricInner p
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
      (∑ j : Fin 3, V j • Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) =
      ∑ j : Fin 3, V j * g.metricInner p
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
        (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) := by
    intro i
    simpa using (metricInner_sum_smul_right g p Finset.univ V.ofLp
      (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
      (fun j => Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p))
  simp_rw [hright]
  have hgram : ∀ i j : Fin 3,
      g.metricInner p (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e i) p)
          (Riemannian.Tensor.chartBasisVecFiber (I := 𝓡 3) a (e j) p) =
        Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) (e j) := by
    intro i j
    exact Riemannian.Tensor.chartGramMatrix_apply (I := 𝓡 3) g a p (e i) (e j)
  simp_rw [hgram]
  have hsym : ∀ i j : Fin 3,
      Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) (e j) =
        Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e j) (e i) := by
    intro i j
    have h := (Riemannian.Tensor.chartGramMatrix_isHermitian (I := 𝓡 3) g a p).apply
      (e j) (e i)
    simpa only [star_trivial] using h
  rw [real_inner_comm, chartCoefficientOperator, Matrix.inner_toEuclideanCLM]
  change (∑ i : Fin 3, U.ofLp i *
      ∑ j : Fin 3, V.ofLp j *
        Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) (e j)) =
    ∑ j : Fin 3, V.ofLp j *
      ∑ i : Fin 3, Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e j) (e i) * U.ofLp i
  calc
    (∑ i : Fin 3, U.ofLp i *
        ∑ j : Fin 3, V.ofLp j *
          Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) (e j))
        = ∑ i : Fin 3, ∑ j : Fin 3,
            U.ofLp i * (V.ofLp j *
              Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) (e j)) := by
            simp only [Finset.mul_sum]
    _ = ∑ j : Fin 3, ∑ i : Fin 3,
          U.ofLp i * (V.ofLp j *
            Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) (e j)) :=
          Finset.sum_comm
    _ = ∑ j : Fin 3, V.ofLp j *
          ∑ i : Fin 3,
            Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e j) (e i) * U.ofLp i := by
          apply Finset.sum_congr rfl
          intro j _
          calc
            (∑ i : Fin 3, U.ofLp i * (V.ofLp j *
                Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e i) (e j)))
                = ∑ i : Fin 3, V.ofLp j *
                    (Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e j) (e i) *
                      U.ofLp i) := by
                    apply Finset.sum_congr rfl
                    intro i _
                    rw [hsym i j]
                    ring
            _ = V.ofLp j *
                  ∑ i : Fin 3,
                    Riemannian.Tensor.chartGramMatrix (I := 𝓡 3) g a p (e j) (e i) *
                      U.ofLp i := by rw [Finset.mul_sum]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
