import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricGermJets
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualCoordinateRicci
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ

/-- **Math.** actual coordinate ricci germ. -/
theorem actual_coordinate_ricci_germ (G H : E3 → (E3 →L[ℝ] E3)) (x : E3) (h : G =ᶠ[𝓝 x] H)
    (i j : Fin 3) : actualCoordinateRicci G x i j = actualCoordinateRicci H x i j :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨h₀, h₁, _⟩ := metric_germ_first_second_jets G H x h
  have hP : (fun y : E3 => fun a : Fin 3 =>
      fderiv ℝ G y (EuclideanSpace.single a 1)) =ᶠ[𝓝 x]
      (fun y : E3 => fun a : Fin 3 =>
      fderiv ℝ H y (EuclideanSpace.single a 1)) := by
    exact h.fderiv.mono fun y hy => funext fun a => by
      exact congrArg
        (fun L : E3 →L[ℝ] (E3 →L[ℝ] E3) => L (EuclideanSpace.single a 1)) hy
  have hC (k a b : Fin 3) :
      (fun y : E3 => coordinateChristoffel (G y)
        (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k a b) =ᶠ[𝓝 x]
      (fun y : E3 => coordinateChristoffel (H y)
        (fun r : Fin 3 => fderiv ℝ H y (EuclideanSpace.single r 1)) k a b) := by
    apply (h.and hP).mono
    intro y hy
    rcases hy with ⟨hGy, hPy⟩
    change (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) =
      (fun a : Fin 3 => fderiv ℝ H y (EuclideanSpace.single a 1)) at hPy
    change coordinateChristoffel (G y)
        (fun r : Fin 3 => fderiv ℝ G y (EuclideanSpace.single r 1)) k a b =
      coordinateChristoffel (H y)
        (fun r : Fin 3 => fderiv ℝ H y (EuclideanSpace.single r 1)) k a b
    rw [hGy]
    exact congrArg (fun P : Fin 3 → E3 →L[ℝ] E3 => coordinateChristoffel (H y) P k a b) hPy
  have hD1 (k : Fin 3) :
      fderiv ℝ (fun y : E3 => coordinateChristoffel (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k i j) x
          (EuclideanSpace.single k 1) =
      fderiv ℝ (fun y : E3 => coordinateChristoffel (H y)
        (fun a : Fin 3 => fderiv ℝ H y (EuclideanSpace.single a 1)) k i j) x
          (EuclideanSpace.single k 1) := by
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single k 1))
      (hC k i j).fderiv.eq_of_nhds
  have hD2 (k : Fin 3) :
      fderiv ℝ (fun y : E3 => coordinateChristoffel (G y)
        (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k i k) x
          (EuclideanSpace.single j 1) =
      fderiv ℝ (fun y : E3 => coordinateChristoffel (H y)
        (fun a : Fin 3 => fderiv ℝ H y (EuclideanSpace.single a 1)) k i k) x
          (EuclideanSpace.single j 1) := by
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single j 1))
      (hC k i k).fderiv.eq_of_nhds
  have hQ : quadraticRicciProduct (G x)
      (fun a : Fin 3 => fderiv ℝ G x (EuclideanSpace.single a 1)) i j =
      quadraticRicciProduct (H x)
      (fun a : Fin 3 => fderiv ℝ H x (EuclideanSpace.single a 1)) i j := by
    rw [h₀]
    congr 1
    exact funext fun a => by
      exact congrArg
        (fun L : E3 →L[ℝ] (E3 →L[ℝ] E3) => L (EuclideanSpace.single a 1)) h₁
  unfold actualCoordinateRicci
  simp_rw [hD1, hD2, hQ]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
