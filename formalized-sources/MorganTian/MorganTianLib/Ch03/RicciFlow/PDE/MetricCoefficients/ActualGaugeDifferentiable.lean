import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Differentiability of the actual DeTurck vector built from a twice smooth metric field. -/
theorem actual_deturck_gauge_differentiable (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G) (x : E3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ v : E3, c * ‖v‖ ^ 2 ≤ inner ℝ (G x v) v) :
    DifferentiableAt ℝ (fun y : E3 => (WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k) : E3)) x :=
/- SWARM_PROOF_BEGIN -/
by
  let firstJet : E3 → Fin 3 → E3 →L[ℝ] E3 := fun y a =>
    fderiv ℝ G y (EuclideanSpace.single a 1)
  let gauge : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) → E3 := fun z =>
    (WithLp.toLp 2 (fun k : Fin 3 => coordinateDeTurckGauge z.1 z.2 k) : E3)
  have hGdiff : DifferentiableAt ℝ G x :=
    hG.contDiffAt.differentiableAt (by norm_num)
  have hDf : ContDiff ℝ 1 (fderiv ℝ G) :=
    hG.fderiv_right (by norm_num)
  have hJetDiff : DifferentiableAt ℝ firstJet x := by
    rw [differentiableAt_pi]
    intro a
    have hcoord : ContDiffAt ℝ 1
        (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single a 1)) x := by
      exact hDf.contDiffAt.clm_apply contDiffAt_const
    exact hcoord.differentiableAt_one
  have hPairDiff : DifferentiableAt ℝ (fun y : E3 => (G y, firstJet y)) x :=
    hGdiff.prodMk hJetDiff
  have hGaugeDiff : DifferentiableAt ℝ gauge (G x, firstJet x) := by
    apply (coordinate_deturck_gauge_smooth (G x) (firstJet x) c hc hpos).differentiableAt
    simp
  simpa [gauge, firstJet, Function.comp_def] using hGaugeDiff.comp x hPairDiff
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
