import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualDeTurckEquationSplit
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalSelfadjointExtension
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualRicciGerm
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualGaugeLieGerm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ

/-- **Math.** local deturck equation split. -/
theorem local_deturck_equation_split (G : E3 → (E3 →L[ℝ] E3)) (x : E3) (hG : ContDiffAt ℝ 2 G x)
    (hsym : ∀ᶠ y : E3 in 𝓝 x, ∀ v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w))
    (c : ℝ) (hc : 0 < c) (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (i j : Fin 3) :
    let P := fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1);
    let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y) (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k);
    -2*actualCoordinateRicci G x i j + coordinateLieMetricExpr G W x i j =
      (∑ p : Fin 3, ∑ q : Fin 3, ((G x).inverse (EuclideanSpace.single q 1)) p *
        (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single q 1)) x
          (EuclideanSpace.single p 1) (EuclideanSpace.single j 1)) i) +
      (-2*ricciLowerOrder (G x) P i j + deturckLieLowerOrder (G x) P i j) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨H, hHcont, hHsym, hHG⟩ := local_selfadjoint_extension G x hG hsym
  have hGH : G =ᶠ[𝓝 x] H := hHG.symm
  have hGx : G x = H x := hGH.eq_of_nhds
  have hposH : ∀ v : E3, c * ‖v‖^2 ≤ inner ℝ (H x v) v := by
    intro v
    simpa [hGx] using hpos v
  have hsplit := actual_deturck_equation_split H hHcont hHsym x c hc hposH i j
  dsimp only at hsplit ⊢
  have hRicci := actual_coordinate_ricci_germ G H x hGH i j
  have hLie := actual_gauge_lie_germ G H x hGH i j
  have hJets := metric_germ_first_second_jets G H x hGH
  obtain ⟨hValue, hFirst, hSecond⟩ := hJets
  have hP : (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) =
      (fun r : Fin 3 => fderiv ℝ H x (EuclideanSpace.single r 1)) := by
    funext r
    exact congrArg (fun D : E3 →L[ℝ] (E3 →L[ℝ] E3) => D (EuclideanSpace.single r 1)) hFirst
  have hPrincipal (p q : Fin 3) :
      fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single q 1)) x
        (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) i =
        fderiv ℝ (fun y : E3 => fderiv ℝ H y (EuclideanSpace.single q 1)) x
          (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) i := by
    have hq := hSecond (EuclideanSpace.single q 1)
    exact congrArg (fun D : E3 →L[ℝ] (E3 →L[ℝ] E3) =>
      (D (EuclideanSpace.single p 1)) (EuclideanSpace.single j 1) i) hq
  have hSum :
      (∑ p : Fin 3, ∑ q : Fin 3, ((G x).inverse (EuclideanSpace.single q 1)) p *
        (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single q 1)) x
          (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) i)) =
      (∑ p : Fin 3, ∑ q : Fin 3, ((H x).inverse (EuclideanSpace.single q 1)) p *
        (fderiv ℝ (fun y : E3 => fderiv ℝ H y (EuclideanSpace.single q 1)) x
          (EuclideanSpace.single p 1) (EuclideanSpace.single j 1) i)) := by
    simp_rw [hValue, hPrincipal]
  have hLower :
      -2 * ricciLowerOrder (G x)
          (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) i j +
        deturckLieLowerOrder (G x)
          (fun r : Fin 3 => fderiv ℝ G x (EuclideanSpace.single r 1)) i j =
      -2 * ricciLowerOrder (H x)
          (fun r : Fin 3 => fderiv ℝ H x (EuclideanSpace.single r 1)) i j +
        deturckLieLowerOrder (H x)
          (fun r : Fin 3 => fderiv ℝ H x (EuclideanSpace.single r 1)) i j := by
    rw [hValue, hP]
  rw [hRicci, hLie, hSum, hLower]
  exact hsplit
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
