import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
import PoincareConjecture.ParallelImplementation.CoordinateRicciPrincipal
import PoincareConjecture.ParallelImplementation.CoordinateDeTurckPrincipal
import PoincareConjecture.ParallelImplementation.CoordinateDeTurckQuadratic
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateRawDeTurckIdentity
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem raw_coordinate_deturck_identity
    (g h : Mat) (d : First) (dd : Second)
    (hg : ∀ i j : Idx, g i j=g j i) (hh : ∀ i j : Idx, h i j=h j i)
    (hgh : ∀ i j : Idx, (∑ k : Idx, g i k*h k j) = if i=j then 1 else 0)
    (hd : ∀ a i j : Idx, d a i j=d a j i)
    (hddComm : ∀ a b i j : Idx, dd a b i j=dd b a i j)
    (hddSym : ∀ a b i j : Idx, dd a b i j=dd a b j i) :

    ∀ i j : Idx, -2*ricci h d dd i j+lieMetric g h d dd i j =
      (∑ a : Idx, ∑ b : Idx, h a b*dd a b i j)+deturckQuadratic h h d d i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro i j
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
    _ = (∑ a : Idx, ∑ b : Idx, h a b * dd a b i j) + deturckQuadratic h h d d i j := by
      rw [hPrincipal, hQuadratic] <;> rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateRawDeTurckIdentity
