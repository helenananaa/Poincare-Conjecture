import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
import PoincareConjecture.ParallelImplementation.CoordinateRicciQuadraticSymmetry
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateDeTurckSymmetry
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open MorganTianLib.MetricCoefficient
theorem deturck_quadratic_symmetric
    (h : Mat) (d : First) (hh : ∀ i j : Idx, h i j = h j i)
    (hd : ∀ a i j : Idx, d a i j = d a j i) :

    ∀ i j : Idx, deturckQuadratic h h d d i j = deturckQuadratic h h d d j i :=
/- SWARM_PROOF_BEGIN -/
by
  intro i j
  have hRicci :=
    PoincareConjecture.ParallelImplementation.CoordinateRicciQuadraticSymmetry.ricci_quadratic_symmetric
      h d hh hd i j
  have hfirst :
      (∑ r : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
        h a b * h r l * lowerChristoffel d l a b * d r i j) =
      (∑ r : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
        h a b * h r l * lowerChristoffel d l a b * d r j i) := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro l hl
    rw [hd r i j]
  have hsecond :
      (∑ a : Idx, ∑ b : Idx,
        (inverseDerivativePolar h h d i a b * lowerChristoffel d j a b +
          inverseDerivativePolar h h d j a b * lowerChristoffel d i a b)) =
      (∑ a : Idx, ∑ b : Idx,
        (inverseDerivativePolar h h d j a b * lowerChristoffel d i a b +
          inverseDerivativePolar h h d i a b * lowerChristoffel d j a b)) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  have hLie : lieQuadratic h h d d i j = lieQuadratic h h d d j i := by
    unfold lieQuadratic
    rw [hfirst, hsecond]
    ring
  unfold deturckQuadratic
  rw [hRicci, hLie]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateDeTurckSymmetry
