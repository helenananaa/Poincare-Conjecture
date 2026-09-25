import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.SixCoordinateDeTurckNonlinearity
import PoincareConjecture.ParallelImplementation.SixActualCoordinateGeometry
import PoincareConjecture.ParallelImplementation.OperatorTwoSidedInverse
import PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra
import PoincareConjecture.ParallelImplementation.SymmetricSixMatrixLinear
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ConcreteSixGeometricRHS
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance standardGroup0 : NormedAddCommGroup (E3 →L[ℝ] E3) := inferInstance
local instance standardSpace0 : NormedSpace ℝ (E3 →L[ℝ] E3) := inferInstance
local instance standardGroup1 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance standardSpace1 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance standardGroup2 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace2 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup3 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace3 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup4 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace4 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup5 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace5 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
local instance derivativeGroup0 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance derivativeSpace0 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance derivativeGroup1 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance derivativeSpace1 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
theorem exists_concrete_six_geometric_rhs :

    ∃ B : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ]
      (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6, ‖B‖ ≤ 30000 ∧
      ∀ E : E6 →L[ℝ] (E3 →L[ℝ] E3),
      (∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j) →
      ∀ (u : E3 → E6), ContDiff ℝ 2 u → ∀ (x : E3) (b : E3 →L[ℝ] E3),
      (1+E (u x))*b=1 → b*(1+E (u x))=1 → ∀ i j : Idx,
      symmetricSixMatrix ((∑ a : Idx, ∑ c : Idx, (b (EuclideanSpace.single c 1)) a •
        fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) +
        B b b (fderiv ℝ u x) (fderiv ℝ u x)) i j =
        -2*actualRicci E u x i j+actualLie E u x i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rcases PoincareConjecture.ParallelImplementation.SixCoordinateDeTurckNonlinearity.exists_concrete_six_deturck_nonlinearity with
    ⟨B, hBnorm, hBentry, hBdiagonal⟩
  refine ⟨B, hBnorm, ?_⟩
  intro E hE u hu x b hab hba i j

  have hcanonical :=
    PoincareConjecture.ParallelImplementation.OperatorTwoSidedInverse.two_sided_inverse_is_canonical
      (1 + E (u x)) b hab hba
  have hunit : IsUnit (metricOp E u x) := by
    simpa [metricOp] using hcanonical.1
  have hbinv : b = Ring.inverse (metricOp E u x) := by
    simpa [metricOp] using hcanonical.2

  have hAlg :=
    PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra.six_inverse_coordinate_algebra
      E hE (u x) b hab hba
  have hbsym : ∀ r s : Idx,
      (b (EuclideanSpace.single s 1)) r =
        (b (EuclideanSpace.single r 1)) s := by
    intro r s
    simpa using hAlg.2.1 r s

  have hgeom :=
    PoincareConjecture.ParallelImplementation.SixActualCoordinateGeometry.actual_coordinate_geometry
      E hE u hu x hunit

  have hInvCoeff (r s : Idx) :
      inverseCoefficients E u x r s = (b (EuclideanSpace.single s 1)) r := by
    change (Ring.inverse (metricOp E u x) (EuclideanSpace.single s 1)) r = _
    exact congrArg (fun A : E3 →L[ℝ] E3 => (A (EuclideanSpace.single s 1)) r) hbinv.symm

  have hBdiag := hBdiagonal b (fderiv ℝ u x) hbsym i j
  have hInvMatrix :
      (fun r s : Idx => (b (EuclideanSpace.single s 1)) r) =
        inverseCoefficients E u x := by
    funext r s
    exact (hInvCoeff r s).symm
  have hGradMatrix :
      (fun a r s : Idx =>
        symmetricSixMatrix ((fderiv ℝ u x) (EuclideanSpace.single a 1)) r s) =
        firstCoefficients u x := by
    funext a r s
    rfl
  rw [hInvMatrix, hGradMatrix] at hBdiag
  have hBcoord :
      symmetricSixMatrix (B b b (fderiv ℝ u x) (fderiv ℝ u x)) i j =
        deturckQuadratic (inverseCoefficients E u x) (inverseCoefficients E u x)
          (firstCoefficients u x) (firstCoefficients u x) i j := hBdiag

  have hsymAdd (q r : E6) (a c : Idx) :
      symmetricSixMatrix (q + r) a c = symmetricSixMatrix q a c + symmetricSixMatrix r a c := by
    fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
  have hsymSmul (t : ℝ) (q : E6) (a c : Idx) :
      symmetricSixMatrix (t • q) a c = t * symmetricSixMatrix q a c := by
    fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
  have hsymZero (a c : Idx) : symmetricSixMatrix (0 : E6) a c = 0 := by
    fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
  have hsumFinset (s : Finset Idx) (f : Idx → E6) (a c : Idx) :
      symmetricSixMatrix (s.sum f) a c = s.sum (fun k => symmetricSixMatrix (f k) a c) := by
    induction s using Finset.induction_on with
    | empty => simpa using hsymZero a c
    | @insert k s hk ih =>
        rw [Finset.sum_insert hk, Finset.sum_insert hk, hsymAdd, ih]
  have hsum (f : Idx → E6) :
      symmetricSixMatrix (∑ a : Idx, f a) i j =
        ∑ a : Idx, symmetricSixMatrix (f a) i j := by
    simpa using hsumFinset Finset.univ f i j

  let principal : ℝ := ∑ a : Idx, ∑ c : Idx,
    (b (EuclideanSpace.single c 1)) a *
      symmetricSixMatrix (fderiv ℝ (fderiv ℝ u) x
        (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j
  have hprincipal :
      symmetricSixMatrix
          (∑ a : Idx, ∑ c : Idx,
            (b (EuclideanSpace.single c 1)) a •
              fderiv ℝ (fderiv ℝ u) x
                (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j = principal := by
    dsimp [principal]
    calc
      symmetricSixMatrix
          (∑ a : Idx, ∑ c : Idx,
            (b (EuclideanSpace.single c 1)) a •
              fderiv ℝ (fderiv ℝ u) x
                (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j =
          ∑ a : Idx, symmetricSixMatrix
            (∑ c : Idx,
              (b (EuclideanSpace.single c 1)) a •
                fderiv ℝ (fderiv ℝ u) x
                  (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j := by
            exact hsum _
      _ = ∑ a : Idx, ∑ c : Idx,
            (b (EuclideanSpace.single c 1)) a *
              symmetricSixMatrix (fderiv ℝ (fderiv ℝ u) x
                (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j := by
            apply Finset.sum_congr rfl
            intro a ha
            calc
              symmetricSixMatrix
                  (∑ c : Idx,
                    (b (EuclideanSpace.single c 1)) a •
                      fderiv ℝ (fderiv ℝ u) x
                        (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j =
                  ∑ c : Idx, symmetricSixMatrix
                    ((b (EuclideanSpace.single c 1)) a •
                      fderiv ℝ (fderiv ℝ u) x
                        (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j := by
                    exact hsum _
              _ = ∑ c : Idx,
                    (b (EuclideanSpace.single c 1)) a *
                      symmetricSixMatrix (fderiv ℝ (fderiv ℝ u) x
                        (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j := by
                    apply Finset.sum_congr rfl
                    intro c hc
                    exact hsymSmul _ _ i j

  have hprincipalActual : principal =
      ∑ a : Idx, ∑ c : Idx,
        inverseCoefficients E u x a c * secondCoefficients u x a c i j := by
    dsimp [principal]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro c hc
    rw [← hInvCoeff a c]
    rfl

  calc
    symmetricSixMatrix
        ((∑ a : Idx, ∑ c : Idx,
          (b (EuclideanSpace.single c 1)) a •
            fderiv ℝ (fderiv ℝ u) x
              (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) +
          B b b (fderiv ℝ u x) (fderiv ℝ u x)) i j =
        principal + symmetricSixMatrix (B b b (fderiv ℝ u x) (fderiv ℝ u x)) i j := by
          rw [hsymAdd, hprincipal]
    _ = (∑ a : Idx, ∑ c : Idx,
          inverseCoefficients E u x a c * secondCoefficients u x a c i j) +
          deturckQuadratic (inverseCoefficients E u x) (inverseCoefficients E u x)
            (firstCoefficients u x) (firstCoefficients u x) i j := by
          rw [hprincipalActual, hBcoord]
    _ = -2 * actualRicci E u x i j + actualLie E u x i j :=
          (hgeom.2.2 i j).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConcreteSixGeometricRHS
