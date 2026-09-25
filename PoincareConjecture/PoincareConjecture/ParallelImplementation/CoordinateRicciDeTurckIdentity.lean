import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.CoordinateRicciPrincipal
import PoincareConjecture.ParallelImplementation.CoordinateDeTurckPrincipal
import PoincareConjecture.ParallelImplementation.CoordinateDeTurckQuadratic
import PoincareConjecture.ParallelImplementation.CoordinateDeTurckFourlinear
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateRicciDeTurckIdentity
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped BigOperators
theorem coordinate_ricci_deturck_identity :
    ∃ Q : Mat →L[ℝ] Mat →L[ℝ] First →L[ℝ] First →L[ℝ] Mat,
      ‖Q‖ ≤ 10000 ∧
      ∀ (g h : Mat) (d : First) (dd : Second),
        (∀ i j : Idx, g i j=g j i) →
        (∀ i j : Idx, h i j=h j i) →
        (∀ i j : Idx, (∑ k : Idx, g i k*h k j) = if i=j then 1 else 0) →
        (∀ a i j : Idx, d a i j=d a j i) →
        (∀ a b i j : Idx, dd a b i j=dd b a i j) →
        (∀ a b i j : Idx, dd a b i j=dd a b j i) →
        ∀ i j : Idx, -2*ricci h d dd i j+lieMetric g h d dd i j =
          (∑ a : Idx, ∑ b : Idx, h a b*dd a b i j)+Q h h d d i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨Q, hQ, hQvalue⟩ :=
    CoordinateDeTurckFourlinear.exists_coordinate_deturck_fourlinear
  refine ⟨Q, hQ.trans (by norm_num), ?_⟩
  intro g h d dd hg hh hgh hd hddComm hddSym i j
  have hRicciSplit :
      ricci h d dd i j = ricciPrincipal h dd i j + ricciQuadratic h h d d i j := by
    simp only [ricci, ricciPrincipal, ricciQuadratic, gammaDerivative]
    have hderiv :
        (∑ k : Idx,
          ((gammaPrincipal h dd k k i j + gammaQuadratic h h d d k k i j) -
            (gammaPrincipal h dd j k i k + gammaQuadratic h h d d j k i k))) =
          (∑ k : Idx,
            (gammaPrincipal h dd k k i j - gammaPrincipal h dd j k i k)) +
          (∑ k : Idx,
            (gammaQuadratic h h d d k k i j - gammaQuadratic h h d d j k i k)) := by
      calc
        _ = ∑ k : Idx,
            ((gammaPrincipal h dd k k i j - gammaPrincipal h dd j k i k) +
              (gammaQuadratic h h d d k k i j - gammaQuadratic h h d d j k i k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = _ := Finset.sum_add_distrib
    rw [hderiv]
    ac_rfl
  have hLieSplit :
      lieMetric g h d dd i j = liePrincipal g h dd i j + lieQuadraticRaw g h d i j := by
    simp only [lieMetric, liePrincipal, lieQuadraticRaw, vectorDerivative,
      Finset.sum_add_distrib]
    simp only [mul_add]
    simp only [Finset.sum_add_distrib]
    ring
  have hPrincipal :
      -2 * ricciPrincipal h dd i j + liePrincipal g h dd i j =
        ∑ a : Idx, ∑ b : Idx, h a b * dd a b i j := by
    rw [CoordinateRicciPrincipal.coordinate_ricci_principal h dd hh hddComm hddSym i j,
      CoordinateDeTurckPrincipal.coordinate_deturck_principal g h dd hg hh hgh hddComm i j]
    simp only [Fin.sum_univ_three]
    simp only [hh, hddComm, hddSym]
    ring
  have hQuadratic :=
    CoordinateDeTurckQuadratic.coordinate_deturck_quadratic g h d hg hgh i j
  calc
    -2 * ricci h d dd i j + lieMetric g h d dd i j =
        (-2 * ricciPrincipal h dd i j + liePrincipal g h dd i j) +
          (-2 * ricciQuadratic h h d d i j + lieQuadraticRaw g h d i j) := by
      rw [hRicciSplit, hLieSplit]
      ring
    _ = (∑ a : Idx, ∑ b : Idx, h a b * dd a b i j) + Q h h d d i j := by
      rw [hPrincipal, hQuadratic]
      change (∑ a : Idx, ∑ b : Idx, h a b * dd a b i j) +
        deturckQuadratic h h d d i j =
        (∑ a : Idx, ∑ b : Idx, h a b * dd a b i j) + Q h h d d i j
      rw [← hQvalue h h d d i j]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateRicciDeTurckIdentity
