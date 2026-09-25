import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
import PoincareConjecture.ParallelImplementation.SixActualMetricJets
import PoincareConjecture.ParallelImplementation.OperatorInverseCoordinateJets
import PoincareConjecture.ParallelImplementation.CoordinateRicciDerivativeIdentification
import PoincareConjecture.ParallelImplementation.CoordinateLieDerivativeIdentification
import PoincareConjecture.ParallelImplementation.CoordinateRawDeTurckIdentity
import PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricOperatorRealization
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixActualCoordinateGeometry
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
theorem actual_coordinate_geometry
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j * v j)
    (u : E3 → E6) (hu : ContDiff ℝ 2 u) (x : E3) (hunit : IsUnit (metricOp E u x)) :

    (∀ i j : Idx, actualRicci E u x i j =
      ricci (inverseCoefficients E u x) (firstCoefficients u x) (secondCoefficients u x) i j) ∧
    (∀ i j : Idx, actualLie E u x i j =
      lieMetric (metricCoefficients u x) (inverseCoefficients E u x) (firstCoefficients u x) (secondCoefficients u x) i j) ∧
    ∀ i j : Idx, -2*actualRicci E u x i j+actualLie E u x i j =
      (∑ a : Idx, ∑ b : Idx, inverseCoefficients E u x a b*secondCoefficients u x a b i j) +
      deturckQuadratic (inverseCoefficients E u x) (inverseCoefficients E u x)
        (firstCoefficients u x) (firstCoefficients u x) i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hreal :=
    PoincareConjecture.ParallelImplementation.SixMetricOperatorRealization.metric_operator_realization
      E hE u hu
  rcases hreal with ⟨hmetricC2, hmetricOperator⟩

  have hjets :=
    PoincareConjecture.ParallelImplementation.SixActualMetricJets.actual_metric_coordinate_jets
      u hu x
  dsimp only at hjets
  rcases hjets with ⟨hg0, hd0, hgsym0, hdsym0, hddComm0, hddSym0⟩
  have hg : ∀ a i j, HasDerivAt
      (fun t : ℝ => metricCoefficients u (x + t • EuclideanSpace.single a 1) i j)
      (firstCoefficients u x a i j) 0 := by
    intro a i j
    simpa [metricCoefficients, firstCoefficients] using hg0 a i j
  have hd : ∀ a b i j, HasDerivAt
      (fun t : ℝ => firstCoefficients u (x + t • EuclideanSpace.single a 1) b i j)
      (secondCoefficients u x a b i j) 0 := by
    intro a b i j
    simpa [firstCoefficients, secondCoefficients] using hd0 a b i j
  have hgsym : ∀ y i j, metricCoefficients u y i j = metricCoefficients u y j i := by
    intro y i j
    simpa [metricCoefficients] using hgsym0 y i j
  have hdsym : ∀ y a i j, firstCoefficients u y a i j = firstCoefficients u y a j i := by
    intro y a i j
    simpa [firstCoefficients] using hdsym0 y a i j
  have hddComm : ∀ a b i j,
      secondCoefficients u x a b i j = secondCoefficients u x b a i j := by
    intro a b i j
    simpa [secondCoefficients] using hddComm0 a b i j
  have hddSym : ∀ a b i j,
      secondCoefficients u x a b i j = secondCoefficients u x a b j i := by
    intro a b i j
    simpa [secondCoefficients] using hddSym0 a b i j

  have hentry (y : E3) (i j : Idx) :
      (metricOp E u y (EuclideanSpace.single j 1)) i = metricCoefficients u y i j :=
    (hmetricOperator y).1 i j
  have hmetricFDeriv :
      HasFDerivAt (metricOp E u) (E.comp (fderiv ℝ u x)) x :=
    (hmetricOperator x).2
  rcases PoincareConjecture.ParallelImplementation.OperatorInverseCoordinateJets.inverse_coordinate_jets
      (metricOp E u) (E.comp (fderiv ℝ u x)) x hmetricFDeriv hunit with
    ⟨dh, hInvDeriv0, hInv0, hLeft0⟩
  have hInvDeriv : ∀ a i j, HasDerivAt
      (fun t : ℝ => inverseCoefficients E u (x + t • EuclideanSpace.single a 1) i j)
      (dh a i j) 0 := by
    intro a i j
    simpa [inverseCoefficients] using hInvDeriv0 a i j

  have hab : (1 + E (u x)) * Ring.inverse (metricOp E u x) = 1 := by
    simpa [metricOp] using
      Ring.isUnit_iff_mul_inverse_cancel.mp hunit
  have hba : Ring.inverse (metricOp E u x) * (1 + E (u x)) = 1 := by
    simpa [metricOp] using
      (Ring.isUnit_iff_inverse_mul_cancel (metricOp E u x)).mp hunit
  rcases PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra.six_inverse_coordinate_algebra
      E hE (u x) (Ring.inverse (metricOp E u x)) hab hba with
    ⟨hgSymAlg, hhSymAlg, hghAlg, hhgAlg⟩
  have hgSym : ∀ i j : Idx,
      metricCoefficients u x i j = metricCoefficients u x j i := by
    intro i j
    simpa [metricCoefficients] using hgSymAlg i j
  have hhSym : ∀ i j : Idx,
      inverseCoefficients E u x i j = inverseCoefficients E u x j i := by
    intro i j
    simpa [inverseCoefficients] using hhSymAlg i j
  have hgh : ∀ i j : Idx,
      (∑ k : Idx, metricCoefficients u x i k * inverseCoefficients E u x k j) =
        if i = j then 1 else 0 := by
    intro i j
    simpa [metricCoefficients, inverseCoefficients] using hghAlg i j
  have hhg : ∀ i j : Idx,
      (∑ k : Idx, inverseCoefficients E u x i k * metricCoefficients u x k j) =
        if i = j then 1 else 0 := by
    intro i j
    simpa [metricCoefficients, inverseCoefficients] using hhgAlg i j

  have hInv : ∀ a : Idx, ∀ᶠ t : ℝ in 𝓝 0, ∀ i j : Idx,
      (∑ k : Idx,
        metricCoefficients u (x + t • EuclideanSpace.single a 1) i k *
          inverseCoefficients E u (x + t • EuclideanSpace.single a 1) k j) =
        if i = j then 1 else 0 := by
    intro a
    filter_upwards [hInv0 a] with t ht
    intro i j
    calc
      (∑ k : Idx,
          metricCoefficients u (x + t • EuclideanSpace.single a 1) i k *
            inverseCoefficients E u (x + t • EuclideanSpace.single a 1) k j) =
        ∑ k : Idx,
          (metricOp E u (x + t • EuclideanSpace.single a 1)
            (EuclideanSpace.single k 1)) i *
            (Ring.inverse (metricOp E u (x + t • EuclideanSpace.single a 1))
              (EuclideanSpace.single j 1)) k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [← hentry (x + t • EuclideanSpace.single a 1) i k]
          rfl
      _ = if i = j then 1 else 0 := ht i j

  have hRicciIdent :=
    PoincareConjecture.ParallelImplementation.CoordinateRicciDerivativeIdentification.ricci_eq_actual_coordinate_derivatives
      (metricCoefficients u) (inverseCoefficients E u) (firstCoefficients u)
      (secondCoefficients u x) dh x hg hInvDeriv hd hInv hhg
  have hRicci : ∀ i j : Idx,
      actualRicci E u x i j =
        ricci (inverseCoefficients E u x) (firstCoefficients u x)
          (secondCoefficients u x) i j := by
    intro i j
    simpa [actualRicci, christoffelField] using hRicciIdent i j

  have hLieIdent :=
    PoincareConjecture.ParallelImplementation.CoordinateLieDerivativeIdentification.lie_eq_actual_coordinate_derivatives
      (metricCoefficients u) (inverseCoefficients E u) (firstCoefficients u)
      (secondCoefficients u x) dh x hg hInvDeriv hd hInv hhg
  have hLie : ∀ i j : Idx,
      actualLie E u x i j =
        lieMetric (metricCoefficients u x) (inverseCoefficients E u x)
          (firstCoefficients u x) (secondCoefficients u x) i j := by
    intro i j
    simpa [actualLie, deturckField] using hLieIdent i j

  refine ⟨hRicci, hLie, ?_⟩
  intro i j
  rw [hRicci i j, hLie i j]
  exact PoincareConjecture.ParallelImplementation.CoordinateRawDeTurckIdentity.raw_coordinate_deturck_identity
    (metricCoefficients u x) (inverseCoefficients E u x) (firstCoefficients u x)
    (secondCoefficients u x) hgSym hhSym hgh (hdsym x) hddComm hddSym i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixActualCoordinateGeometry
