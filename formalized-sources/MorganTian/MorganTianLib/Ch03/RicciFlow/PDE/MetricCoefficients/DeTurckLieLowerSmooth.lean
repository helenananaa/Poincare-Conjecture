import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LoweredGaugeJetSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckLieLowerOrder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Math.** deturck lie lower order smooth. -/
theorem deturck_lie_lower_order_smooth (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3)
    (c : ℝ) (hc : 0 < c) (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (i j : Fin 3) :
    ContDiffAt ℝ ∞ (fun q : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
      deturckLieLowerOrder q.1 q.2 i j) (A,P) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hLower₁ : ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        loweredGaugeJet z.1 z.2 i j) (A, P) :=
    lowered_gauge_jet_smooth A P c hc hA i j
  have hLower₂ : ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        loweredGaugeJet z.1 z.2 j i) (A, P) :=
    lowered_gauge_jet_smooth A P c hc hA j i
  have hGaugeVec := coordinate_deturck_gauge_smooth A P c hc hA
  have hGauge : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        coordinateDeTurckGauge z.1 z.2 k) (A, P) := by
    intro k
    simpa [Function.comp_def, EuclideanSpace.coe_proj] using
      ((EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.contDiffAt.comp (A, P)
        hGaugeVec)
  have hCoord : ∀ (r l s : Fin 3), ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        (z.2 r (EuclideanSpace.single l 1)) s) (A, P) := by
    intro r l s
    fun_prop
  have hTerm : ∀ k : Fin 3, ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        coordinateDeTurckGauge z.1 z.2 k *
        ((z.2 k (EuclideanSpace.single j 1)) i -
          (z.2 i (EuclideanSpace.single k 1)) j -
          (z.2 j (EuclideanSpace.single k 1)) i)) (A, P) := by
    intro k
    have hBracket : ContDiffAt ℝ ∞
        (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          (z.2 k (EuclideanSpace.single j 1)) i -
          (z.2 i (EuclideanSpace.single k 1)) j -
          (z.2 j (EuclideanSpace.single k 1)) i) (A, P) := by
      exact ((hCoord k j i).sub (hCoord i k j)).sub (hCoord j k i)
    exact (hGauge k).mul hBracket
  have hSum : ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
        ∑ k : Fin 3, coordinateDeTurckGauge z.1 z.2 k *
        ((z.2 k (EuclideanSpace.single j 1)) i -
          (z.2 i (EuclideanSpace.single k 1)) j -
          (z.2 j (EuclideanSpace.single k 1)) i)) (A, P) := by
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun k _ => hTerm k))
  simpa [deturckLieLowerOrder] using (hLower₁.add hLower₂).add hSum
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
