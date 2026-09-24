import PoincareConjecture.ParallelImplementation.DuhamelRightTimeDerivative
import PoincareConjecture.ParallelImplementation.DuhamelGeneratorContinuity
import MorganTianLib.Ch03.RicciFlow.PDE.HeatKernel.ContinuousRightDerivative
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.DuhamelForcedHeatEquation
open MorganTianLib.ParabolicPDE Set MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The actual Duhamel integral solves the forced heat equation with genuine two-sided interior derivatives. -/
theorem duhamel_forced_heat_equation
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ) (hL : 0 ≤ L) (hT : 0 < T)
    (hholder : ∀ s ∈ Icc (0:ℝ) T, ∀ x y : E3,
      |F (s,x)-F (s,y)| ≤ L*‖x-y‖^alpha) :
    let u : ℝ → E3 → ℝ := fun t x => ∫ s in (0:ℝ)..t,
      ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)
    u 0 = 0 ∧ ∀ t ∈ Ioo (0:ℝ) T, ∀ x : E3,
      HasDerivAt (fun s => u s x)
        ((∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ (u t) y
          (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) + F (t,x)) t :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  constructor
  · funext x
    simp
  · intro t ht x
    let u : ℝ → E3 → ℝ := fun t x => ∫ s in (0:ℝ)..t,
      ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y) * F (s,y)
    have hright := PoincareConjecture.ParallelImplementation.DuhamelRightTimeDerivative.duhamel_right_time_derivative
      alpha ha ha1 F L T hL hT hholder
    have hcontinuous := PoincareConjecture.ParallelImplementation.DuhamelGeneratorContinuity.duhamel_generator_continuity
      alpha ha ha1 F L T hL hT hholder x
    rcases hcontinuous with ⟨hvalue, hgenerator⟩
    exact continuous_right_derivative_is_derivative
      (fun s : ℝ => u s x)
      (fun s : ℝ => (∑ i : Fin 3,
        fderiv ℝ (fun y => fderiv ℝ (u s) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single i 1)) + F (s,x))
      0 T hvalue hgenerator (by
        intro s hs
        exact hright s hs x) t ht
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.DuhamelForcedHeatEquation
