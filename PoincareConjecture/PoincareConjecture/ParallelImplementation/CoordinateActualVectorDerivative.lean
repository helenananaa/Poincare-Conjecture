import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.CoordinateInverseCurveDerivative
import PoincareConjecture.ParallelImplementation.CoordinateDeTurckCurveDerivative
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateActualVectorDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem actual_vector_derivative
    (g h : ℝ → Mat) (d : ℝ → First) (dh : Mat) (dd : Second) (t : ℝ) (a : Idx)
    (hg : ∀ i j, HasDerivAt (fun r => g r i j) (d t a i j) t)
    (hh : ∀ i j, HasDerivAt (fun r => h r i j) (dh i j) t)
    (hd : ∀ b i j, HasDerivAt (fun r => d r b i j) (dd a b i j) t)
    (hInv : ∀ᶠ r in 𝓝 t, ∀ i j : Idx, (∑ k : Idx, g r i k * h r k j) = if i = j then 1 else 0)
    (hLeft : ∀ i j : Idx, (∑ k : Idx, h t i k * g t k j) = if i = j then 1 else 0) :

    ∀ k : Idx, HasDerivAt (fun r => deturckVector (h r) (d r) k)
      (vectorDerivative (h t) (d t) dd a k) t :=
/- SWARM_PROOF_BEGIN -/
by
  let e : First := fun b i j => dd a b i j
  have hdh : ∀ i j : Idx,
      dh i j = inverseDerivativePolar (h t) (h t) (d t) a i j := by
    intro i j
    simpa [inverseDerivativePolar] using
      (CoordinateInverseCurveDerivative.inverse_derivative_formula
        g h (d t a) dh t (fun i j => hg i j) hh hInv hLeft i j)
  have hdd : ∀ b i j : Idx,
      HasDerivAt (fun r => d r b i j) (e b i j) t := by
    intro b i j
    exact hd b i j
  have hcurve :=
    CoordinateDeTurckCurveDerivative.deturck_vector_hasDerivAt
      h d dh e t hh hdd
  have hprincipal (k p q : Idx) :
      (∑ l : Idx, h t k l * lowerChristoffel e l p q) =
        gammaPrincipal (h t) dd a k p q := by
    change (∑ l : Idx, h t k l *
      ((1 / 2 : ℝ) * (dd a p q l + dd a q p l - dd a l p q))) = _
    change _ = (1 / 2 : ℝ) *
      (∑ l : Idx, h t k l *
        (dd a p q l + dd a q p l - dd a l p q))
    calc
      (∑ l : Idx, h t k l *
          ((1 / 2 : ℝ) * (dd a p q l + dd a q p l - dd a l p q))) =
          ∑ l : Idx, (1 / 2 : ℝ) *
            (h t k l * (dd a p q l + dd a q p l - dd a l p q)) := by
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = (1 / 2 : ℝ) *
          (∑ l : Idx, h t k l *
            (dd a p q l + dd a q p l - dd a l p q)) := by
        rw [← Finset.mul_sum]
  have hvalue (k : Idx) :
      (∑ p : Idx, ∑ q : Idx,
        (dh p q * christoffel (h t) (d t) k p q +
          h t p q * (∑ l : Idx,
            (dh k l * lowerChristoffel (d t) l p q +
              h t k l * lowerChristoffel e l p q)))) =
        vectorDerivative (h t) (d t) dd a k := by
    simp [vectorDerivative, vectorPrincipal, vectorQuadratic,
      gammaQuadratic, christoffel, hdh, hprincipal,
      Finset.sum_add_distrib, Finset.mul_sum, mul_add]
    ring
  intro k
  simpa only [hvalue k] using hcurve k
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateActualVectorDerivative
