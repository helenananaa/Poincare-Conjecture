import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.CoordinateInverseCurveDerivative
import PoincareConjecture.ParallelImplementation.CoordinateChristoffelCurveDerivative
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateActualGammaDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem actual_gamma_derivative
    (g h : ℝ → Mat) (d : ℝ → First) (dh : Mat) (dd : Second) (t : ℝ) (a : Idx)
    (hg : ∀ i j, HasDerivAt (fun r => g r i j) (d t a i j) t)
    (hh : ∀ i j, HasDerivAt (fun r => h r i j) (dh i j) t)
    (hd : ∀ b i j, HasDerivAt (fun r => d r b i j) (dd a b i j) t)
    (hInv : ∀ᶠ r in 𝓝 t, ∀ i j : Idx, (∑ k : Idx, g r i k * h r k j) = if i = j then 1 else 0)
    (hLeft : ∀ i j : Idx, (∑ k : Idx, h t i k * g t k j) = if i = j then 1 else 0) :

    ∀ k i j : Idx, HasDerivAt (fun r => christoffel (h r) (d r) k i j)
      (gammaDerivative (h t) (d t) dd a k i j) t :=
/- SWARM_PROOF_BEGIN -/
by
  have hdh : ∀ k l : Idx,
      dh k l = inverseDerivativePolar (h t) (h t) (d t) a k l := by
    intro k l
    simpa [inverseDerivativePolar] using
      (CoordinateInverseCurveDerivative.inverse_derivative_formula
        g h (d t a) dh t (fun i j => hg i j) hh hInv hLeft k l)
  have hprincipal (k i j : Idx) :
      (∑ l : Idx, h t k l * lowerChristoffel (dd a) l i j) =
        gammaPrincipal (h t) dd a k i j := by
    unfold gammaPrincipal lowerChristoffel
    calc
      (∑ l : Idx, h t k l * (1 / 2 *
          (dd a i j l + dd a j i l - dd a l i j))) =
          ∑ l : Idx, (1 / 2 : ℝ) *
            (h t k l * (dd a i j l + dd a j i l - dd a l i j)) := by
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = (1 / 2 : ℝ) *
          ∑ l : Idx, h t k l *
            (dd a i j l + dd a j i l - dd a l i j) := by
        rw [Finset.mul_sum]
  have hquadratic (k i j : Idx) :
      (∑ l : Idx, dh k l * lowerChristoffel (d t) l i j) =
        gammaQuadratic (h t) (h t) (d t) (d t) a k i j := by
    simp_rw [hdh]
    rfl
  intro k i j
  have hcurve :=
    CoordinateChristoffelCurveDerivative.christoffel_hasDerivAt
      h d dh (dd a) t hh (fun b i j => hd b i j)
  have hvalue :
      (∑ l : Idx, (dh k l * lowerChristoffel (d t) l i j +
        h t k l * lowerChristoffel (dd a) l i j)) =
        gammaDerivative (h t) (d t) dd a k i j := by
    rw [Finset.sum_add_distrib, hquadratic, hprincipal]
    unfold gammaDerivative
    ring
  rw [← hvalue]
  exact hcurve k i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateActualGammaDerivative
