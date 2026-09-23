import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalMetricCoercivity
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeLowering
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricJetSymmetry
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** The actual lowered vector agrees near the base point with its coefficient formula. -/
theorem actual_gauge_lowering_eventually (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w))
    (x : E3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ v : E3, c * ‖v‖ ^ 2 ≤ inner ℝ (G x v) v) (j : Fin 3) :
    (fun y : E3 => (G y (WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k))) j)
      =ᶠ[𝓝 x]
    (fun y : E3 => loweredDeTurckGauge (G y)
      (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) j) :=
/- SWARM_PROOF_BEGIN -/
by
  have hcont : ContinuousAt G x := hG.continuous.continuousAt
  have hlocal := metric_coercive_eventually G x hcont c hc hpos
  filter_upwards [hlocal] with y hy
  have hdiff : DifferentiableAt ℝ G y := hG.differentiable (by norm_num) y
  have hjet := metric_jet_selfadjoint G y hdiff hsym
  let P : Fin 3 → E3 →L[ℝ] E3 := fun a =>
    fderiv ℝ G y (EuclideanSpace.single a 1)
  have hP : ∀ r : Fin 3, ∀ v w : E3,
      inner ℝ (P r v) w = inner ℝ v (P r w) := by
    intro r v w
    exact hjet (EuclideanSpace.single r 1) v w
  let V : E3 := WithLp.toLp 2 (fun k : Fin 3 => coordinateDeTurckGauge (G y) P k)
  have hV : (∑ k : Fin 3, V k • EuclideanSpace.single k (1 : ℝ)) = V := by
    simpa [V] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr V
  have hExpand : (G y V) j =
      ∑ k : Fin 3, (G y (EuclideanSpace.single k 1)) j *
        coordinateDeTurckGauge (G y) P k := by
    calc
      (G y V) j =
          (G y (∑ k : Fin 3, V k • EuclideanSpace.single k (1 : ℝ))) j := by
        exact congrArg (fun z : E3 => (G y z) j) hV.symm
      _ = (∑ k : Fin 3, G y (V k • EuclideanSpace.single k (1 : ℝ))) j := by
        rw [map_sum]
      _ = ∑ k : Fin 3, (G y (EuclideanSpace.single k 1)) j *
          coordinateDeTurckGauge (G y) P k := by
        simp [map_smul, smul_eq_mul, V, mul_comm]
  change (G y V) j = loweredDeTurckGauge (G y) P j
  calc
    (G y V) j =
        ∑ k : Fin 3, (G y (EuclideanSpace.single k 1)) j *
          coordinateDeTurckGauge (G y) P k := hExpand
    _ = loweredDeTurckGauge (G y) P j := by
      exact coordinate_deturck_gauge_lowering (G y) P (c / 2)
        (by linarith) hy hP j
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
