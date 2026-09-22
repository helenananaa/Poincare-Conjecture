import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeVector
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual gauge vector depends smoothly on the coefficient operator and first jets. -/
theorem coordinate_deturck_gauge_smooth (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) :
    ContDiffAt ℝ ∞ (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
      (WithLp.toLp 2 (fun k : Fin 3 => coordinateDeTurckGauge z.1 z.2 k) : E3)) (A,P) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  apply contDiffAt_euclidean.mpr
  intro k
  change ContDiffAt ℝ ∞
    (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
      coordinateDeTurckGauge z.1 z.2 k) (A, P)
  have hInv : ContDiffAt ℝ ∞
      (fun B : E3 →L[ℝ] E3 => B.inverse) A :=
    (coercive_inverse_differential A c hc hA).1
  have hInv' : ContDiffAt ℝ ∞
      (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) => z.1.inverse) (A, P) :=
    hInv.comp (A, P) contDiffAt_fst
  have hterm : ∀ p q : Fin 3,
      ContDiffAt ℝ ∞
        (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          z.1.inverse (EuclideanSpace.single q 1) p *
            coordinateChristoffel z.1 z.2 k p q) (A, P) := by
    intro p q
    have hinv : ContDiffAt ℝ ∞
        (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          z.1.inverse (EuclideanSpace.single q 1) p) (A, P) := by
      simpa [Function.comp_def, EuclideanSpace.coe_proj] using
        ((EuclideanSpace.proj (𝕜 := ℝ) p).contDiff.contDiffAt.comp (A, P)
          (hInv'.clm_apply contDiffAt_const))
    exact hinv.mul (coordinate_christoffel_smooth A c hc hA P k p q)
  have hsumq : ∀ p : Fin 3,
      ContDiffAt ℝ ∞
        (fun z : (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3) =>
          ∑ q : Fin 3,
            z.1.inverse (EuclideanSpace.single q 1) p *
              coordinateChristoffel z.1 z.2 k p q) (A, P) := by
    intro p
    simpa using (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
      (fun q _ => hterm p q))
  simpa [coordinateDeTurckGauge] using
    (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 3)))
    (fun p _ => hsumq p))
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
