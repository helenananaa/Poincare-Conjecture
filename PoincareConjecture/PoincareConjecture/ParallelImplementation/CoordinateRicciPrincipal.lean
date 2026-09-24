import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateRicciPrincipal
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped BigOperators
theorem coordinate_ricci_principal
    (h : Mat) (dd : Second)
    (hh : ∀ i j : Idx, h i j=h j i)
    (hcomm : ∀ a b i j : Idx, dd a b i j=dd b a i j)
    (hmetric : ∀ a b i j : Idx, dd a b i j=dd a b j i) :
    ∀ i j : Idx, ricciPrincipal h dd i j =
      (1/2:ℝ)*∑ a : Idx, ∑ b : Idx, h a b*
        (dd a i b j+dd a j b i-dd a b i j-dd i j a b) :=
/- SWARM_PROOF_BEGIN -/
by
  intro i j
  simp only [ricciPrincipal, gammaPrincipal, Fin.sum_univ_three]
  simp only [hh, hcomm, hmetric]
  ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateRicciPrincipal
