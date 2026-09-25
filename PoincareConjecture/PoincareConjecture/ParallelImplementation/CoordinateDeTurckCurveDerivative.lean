import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.CoordinateChristoffelCurveDerivative
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateDeTurckCurveDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem deturck_vector_hasDerivAt
    (h : ℝ → Mat) (d : ℝ → First) (dh : Mat) (dd : First) (t : ℝ)
    (hh : ∀ i j, HasDerivAt (fun r => h r i j) (dh i j) t)
    (hd : ∀ a i j, HasDerivAt (fun r => d r a i j) (dd a i j) t) :

    ∀ k : Idx, HasDerivAt (fun r => deturckVector (h r) (d r) k)
      (∑ a : Idx, ∑ b : Idx, (dh a b * christoffel (h t) (d t) k a b +
        h t a b * (∑ l : Idx, (dh k l * lowerChristoffel (d t) l a b +
          h t k l * lowerChristoffel dd l a b)))) t :=
/- SWARM_PROOF_BEGIN -/
by
  intro k
  have hgamma : ∀ a b : Idx,
      HasDerivAt (fun r => christoffel (h r) (d r) k a b)
        (∑ l : Idx, (dh k l * lowerChristoffel (d t) l a b +
          h t k l * lowerChristoffel dd l a b)) t := by
    intro a b
    exact CoordinateChristoffelCurveDerivative.christoffel_hasDerivAt
      h d dh dd t hh hd k a b
  have hterm : ∀ a b : Idx,
      HasDerivAt (fun r => h r a b * christoffel (h r) (d r) k a b)
        (dh a b * christoffel (h t) (d t) k a b +
          h t a b * (∑ l : Idx, (dh k l * lowerChristoffel (d t) l a b +
            h t k l * lowerChristoffel dd l a b))) t := by
    intro a b
    exact (hh a b).mul (hgamma a b)
  have hinner : ∀ a : Idx,
      HasDerivAt
        (fun r => ∑ b : Idx, h r a b * christoffel (h r) (d r) k a b)
        (∑ b : Idx, (dh a b * christoffel (h t) (d t) k a b +
          h t a b * (∑ l : Idx, (dh k l * lowerChristoffel (d t) l a b +
            h t k l * lowerChristoffel dd l a b)))) t := by
    intro a
    simpa using (HasDerivAt.fun_sum (u := Finset.univ)
      (fun b _ => hterm a b))
  change HasDerivAt
    (fun r => ∑ a : Idx, ∑ b : Idx,
      h r a b * christoffel (h r) (d r) k a b)
    (∑ a : Idx, ∑ b : Idx,
      (dh a b * christoffel (h t) (d t) k a b +
        h t a b * (∑ l : Idx, (dh k l * lowerChristoffel (d t) l a b +
          h t k l * lowerChristoffel dd l a b)))) t
  simpa using (HasDerivAt.fun_sum (u := Finset.univ)
    (fun a _ => hinner a))
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateDeTurckCurveDerivative
