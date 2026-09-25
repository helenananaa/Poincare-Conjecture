import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.IntrinsicMetricLieBilinear
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_metric_lie_bilinear
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3)
    (W : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3) (x : E3) :

    ∃ B : E3 →ₗ[ℝ] E3 →ₗ[ℝ] ℝ, ∀ v w : E3,
      B v w = MorganTianLib.metricLieDerivativeAt g W x v w :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let nabla := g.leviCivitaConnection
  let lie : E3 → E3 → ℝ := fun v w =>
    MorganTianLib.metricLieDerivativeAt g W x v w
  have hcov_add (v v' : E3) :
      (nabla.cov (MorganTianLib.extendVector x (v + v')) W) x =
        (nabla.cov (MorganTianLib.extendVector x v) W) x +
          (nabla.cov (MorganTianLib.extendVector x v') W) x := by
    calc
      (nabla.cov (MorganTianLib.extendVector x (v + v')) W) x =
          (nabla.cov (MorganTianLib.extendVector x v + MorganTianLib.extendVector x v') W) x := by
            apply nabla.cov_congr_apply_left W
            simp only [Riemannian.SmoothVectorField.add_apply, MorganTianLib.extendVector_apply]
      _ = (nabla.cov (MorganTianLib.extendVector x v) W) x +
            (nabla.cov (MorganTianLib.extendVector x v') W) x := by
        rw [nabla.add_left, Riemannian.SmoothVectorField.add_apply]
  have hcov_smul (c : ℝ) (v : E3) :
      (nabla.cov (MorganTianLib.extendVector x (c • v)) W) x =
        c • (nabla.cov (MorganTianLib.extendVector x v) W) x := by
    let f : E3 → ℝ := fun _ => c
    have hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f := by
      exact contMDiff_const
    calc
      (nabla.cov (MorganTianLib.extendVector x (c • v)) W) x =
          (nabla.cov (Riemannian.SmoothVectorField.smul f hf
            (MorganTianLib.extendVector x v)) W) x := by
            apply nabla.cov_congr_apply_left W
            simp [f, Riemannian.SmoothVectorField.smul_apply,
              MorganTianLib.extendVector_apply]
      _ = c • (nabla.cov (MorganTianLib.extendVector x v) W) x := by
        have h := congrArg (fun Z : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3 => Z x)
          (nabla.smul_left f hf (MorganTianLib.extendVector x v) W)
        simpa [f] using h
  have hadd (v v' w : E3) : lie (v + v') w = lie v w + lie v' w := by
    unfold lie MorganTianLib.metricLieDerivativeAt
    rw [hcov_add, g.metricInner_add_left]
    rw [g.metricInner_add_left]
    abel
  have hsmul (c : ℝ) (v w : E3) : lie (c • v) w = c • lie v w := by
    unfold lie MorganTianLib.metricLieDerivativeAt
    rw [hcov_smul, g.metricInner_smul_left, g.metricInner_smul_left]
    simp only [smul_eq_mul]
    ring
  have hadd_right (v w w' : E3) : lie v (w + w') = lie v w + lie v w' := by
    have hsymm (a b : E3) : lie a b = lie b a := by
      dsimp [lie]
      exact MorganTianLib.metricLieDerivativeAt_symm g W x a b
    calc
      lie v (w + w') = lie (w + w') v := hsymm v (w + w')
      _ = lie w v + lie w' v := hadd w w' v
      _ = lie v w + lie v w' := by
        rw [hsymm w v, hsymm w' v]
  have hsmul_right (c : ℝ) (v w : E3) : lie v (c • w) = c • lie v w := by
    have hsymm (a b : E3) : lie a b = lie b a := by
      dsimp [lie]
      exact MorganTianLib.metricLieDerivativeAt_symm g W x a b
    calc
      lie v (c • w) = lie (c • w) v := hsymm v (c • w)
      _ = c • lie w v := hsmul c w v
      _ = c • lie v w := by
        rw [hsymm w v]
  refine ⟨LinearMap.mk₂ ℝ lie hadd hsmul hadd_right hsmul_right, ?_⟩
  intro v w
  rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.IntrinsicMetricLieBilinear
