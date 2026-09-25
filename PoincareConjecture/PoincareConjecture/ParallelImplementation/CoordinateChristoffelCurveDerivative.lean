import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateChristoffelCurveDerivative
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem christoffel_hasDerivAt
    (h : ℝ → Mat) (d : ℝ → First) (dh : Mat) (dd : First) (t : ℝ)
    (hh : ∀ i j, HasDerivAt (fun r => h r i j) (dh i j) t)
    (hd : ∀ a i j, HasDerivAt (fun r => d r a i j) (dd a i j) t) :

    ∀ k i j, HasDerivAt (fun r => christoffel (h r) (d r) k i j)
      (∑ l : Idx, (dh k l * lowerChristoffel (d t) l i j +
        h t k l * lowerChristoffel dd l i j)) t :=
/- SWARM_PROOF_BEGIN -/
by
  have hlower : ∀ l i j, HasDerivAt (fun r => lowerChristoffel (d r) l i j)
      (lowerChristoffel dd l i j) t := by
    intro l i j
    have hsum := (hd i j l).add (hd j i l)
    have hsub := hsum.sub (hd l i j)
    simpa [lowerChristoffel] using hsub.const_mul (1 / 2 : ℝ)
  intro k i j
  have hterm : ∀ l : Idx,
      HasDerivAt
        (fun r => h r k l * lowerChristoffel (d r) l i j)
        (dh k l * lowerChristoffel (d t) l i j +
          h t k l * lowerChristoffel dd l i j) t := by
    intro l
    exact (hh k l).mul (hlower l i j)
  change HasDerivAt
    (fun r => ∑ l : Idx, h r k l * lowerChristoffel (d r) l i j)
    (∑ l : Idx, (dh k l * lowerChristoffel (d t) l i j +
      h t k l * lowerChristoffel dd l i j)) t
  simpa using (HasDerivAt.fun_sum (u := Finset.univ) (fun l _ => hterm l))
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateChristoffelCurveDerivative
