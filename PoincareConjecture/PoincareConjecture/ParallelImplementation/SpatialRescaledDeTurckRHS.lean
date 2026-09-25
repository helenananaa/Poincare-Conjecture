import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.ConcreteSixGeometricRHS
import PoincareConjecture.ParallelImplementation.ScaledSpatialC2Derivatives
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SpatialRescaledDeTurckRHS
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
theorem spatial_rescaled_deturck_rhs
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : E3 → E6) (hu : ContDiff ℝ 2 u) (x0 : E3) (r : ℝ) (x : E3)
    (hunit : IsUnit (metricOp E u (x0+r • x))) :

    ∀ i j : Idx, -2*actualRicci E (fun y : E3 => u (x0+r • y)) x i j +
      actualLie E (fun y : E3 => u (x0+r • y)) x i j =
      r^2 * (-2*actualRicci E u (x0+r • x) i j + actualLie E u (x0+r • x) i j) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rcases PoincareConjecture.ParallelImplementation.ConcreteSixGeometricRHS.exists_concrete_six_geometric_rhs with
    ⟨B, hBnorm, hConcrete⟩

  let uR : E3 → E6 := fun y => u (x0 + r • y)
  let z : E3 := x0 + r • x
  have hscaled :=
    PoincareConjecture.ParallelImplementation.ScaledSpatialC2Derivatives.scaled_spatial_c2_derivatives
      u hu x0 r
  have huR : ContDiff ℝ 2 uR := by
    simpa [uR] using hscaled.1
  have hD1 : fderiv ℝ uR x = r • fderiv ℝ u z := by
    simpa [uR, z] using hscaled.2.1 x
  have hD2 : fderiv ℝ (fderiv ℝ uR) x =
      r^2 • fderiv ℝ (fderiv ℝ u) z := by
    simpa [uR, z] using hscaled.2.2 x

  have hunitBase : IsUnit (metricOp E u z) := by
    simpa [z] using hunit
  let b : E3 →L[ℝ] E3 := Ring.inverse (metricOp E u z)
  have hab : (1 + E (u z)) * b = 1 := by
    simpa [b, metricOp] using
      (Ring.isUnit_iff_mul_inverse_cancel.mp hunitBase)
  have hba : b * (1 + E (u z)) = 1 := by
    simpa [b, metricOp] using
      (Ring.isUnit_iff_inverse_mul_cancel (metricOp E u z)).mp hunitBase
  have habR : (1 + E (uR x)) * b = 1 := by
    simpa [uR, z] using hab
  have hbaR : b * (1 + E (uR x)) = 1 := by
    simpa [uR, z] using hba

  have hGeomBase := hConcrete E hE u hu z b hab hba
  have hGeomR := hConcrete E hE uR huR x b habR hbaR

  have hD2coord (a c : Idx) :
      fderiv ℝ (fderiv ℝ uR) x (EuclideanSpace.single a 1)
          (EuclideanSpace.single c 1) =
        r^2 • fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
          (EuclideanSpace.single c 1) := by
    calc
      fderiv ℝ (fderiv ℝ uR) x (EuclideanSpace.single a 1)
          (EuclideanSpace.single c 1) =
        (r^2 • fderiv ℝ (fderiv ℝ u) z) (EuclideanSpace.single a 1)
          (EuclideanSpace.single c 1) := by rw [hD2]
      _ = r^2 • fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
          (EuclideanSpace.single c 1) := by simp

  have hsumSmul (s : Finset Idx) (f : Idx → E6) :
      s.sum (fun k => r^2 • f k) = r^2 • s.sum f := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert k s hk ih =>
        simp [Finset.sum_insert, hk, ih, smul_add]

  have hprincipal :
      (∑ a : Idx, ∑ c : Idx,
        (b (EuclideanSpace.single c 1)) a •
          fderiv ℝ (fderiv ℝ uR) x (EuclideanSpace.single a 1)
            (EuclideanSpace.single c 1)) =
      r^2 • (∑ a : Idx, ∑ c : Idx,
        (b (EuclideanSpace.single c 1)) a •
          fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
            (EuclideanSpace.single c 1)) := by
    calc
      (∑ a : Idx, ∑ c : Idx,
        (b (EuclideanSpace.single c 1)) a •
          fderiv ℝ (fderiv ℝ uR) x (EuclideanSpace.single a 1)
            (EuclideanSpace.single c 1)) =
        ∑ a : Idx, ∑ c : Idx,
          r^2 • ((b (EuclideanSpace.single c 1)) a •
            fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
              (EuclideanSpace.single c 1)) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro c hc
        rw [hD2coord]
        rw [smul_smul, smul_smul]
        congr 1
        ring
      _ = r^2 • (∑ a : Idx, ∑ c : Idx,
          (b (EuclideanSpace.single c 1)) a •
            fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
            (EuclideanSpace.single c 1)) := by
        calc
          (∑ a : Idx, ∑ c : Idx,
            r^2 • ((b (EuclideanSpace.single c 1)) a •
              fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
                (EuclideanSpace.single c 1))) =
            ∑ a : Idx, r^2 • (∑ c : Idx,
              (b (EuclideanSpace.single c 1)) a •
                fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
                  (EuclideanSpace.single c 1)) := by
              apply Finset.sum_congr rfl
              intro a ha
              simpa using hsumSmul Finset.univ (fun c : Idx =>
                (b (EuclideanSpace.single c 1)) a •
                  fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
                    (EuclideanSpace.single c 1))
          _ = r^2 • (∑ a : Idx, ∑ c : Idx,
              (b (EuclideanSpace.single c 1)) a •
                fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
                  (EuclideanSpace.single c 1)) := by
              simpa using hsumSmul Finset.univ (fun a : Idx =>
                ∑ c : Idx,
                  (b (EuclideanSpace.single c 1)) a •
                    fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
                      (EuclideanSpace.single c 1))

  have hBscale :
      B b b (fderiv ℝ uR x) (fderiv ℝ uR x) =
        r^2 • B b b (fderiv ℝ u z) (fderiv ℝ u z) := by
    rw [hD1]
    calc
      B b b (r • fderiv ℝ u z) (r • fderiv ℝ u z) =
        r • B b b (r • fderiv ℝ u z) (fderiv ℝ u z) := by
          rw [map_smul]
      _ = r • (r • B b b (fderiv ℝ u z) (fderiv ℝ u z)) := by
          rw [map_smul, smul_apply]
      _ = r^2 • B b b (fderiv ℝ u z) (fderiv ℝ u z) := by
          rw [smul_smul, pow_two]

  have hsymSmul (t : ℝ) (q : E6) (i j : Idx) :
      symmetricSixMatrix (t • q) i j = t * symmetricSixMatrix q i j := by
    fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix]

  intro i j
  calc
    -2 * actualRicci E uR x i j + actualLie E uR x i j =
      symmetricSixMatrix
        ((∑ a : Idx, ∑ c : Idx,
          (b (EuclideanSpace.single c 1)) a •
            fderiv ℝ (fderiv ℝ uR) x (EuclideanSpace.single a 1)
              (EuclideanSpace.single c 1)) +
          B b b (fderiv ℝ uR x) (fderiv ℝ uR x)) i j :=
        (hGeomR i j).symm
    _ = r^2 * symmetricSixMatrix
        ((∑ a : Idx, ∑ c : Idx,
          (b (EuclideanSpace.single c 1)) a •
            fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
              (EuclideanSpace.single c 1)) +
          B b b (fderiv ℝ u z) (fderiv ℝ u z)) i j := by
      have hvec :
          (∑ a : Idx, ∑ c : Idx,
            (b (EuclideanSpace.single c 1)) a •
              fderiv ℝ (fderiv ℝ uR) x (EuclideanSpace.single a 1)
                (EuclideanSpace.single c 1)) +
              B b b (fderiv ℝ uR x) (fderiv ℝ uR x) =
          r^2 • ((∑ a : Idx, ∑ c : Idx,
            (b (EuclideanSpace.single c 1)) a •
              fderiv ℝ (fderiv ℝ u) z (EuclideanSpace.single a 1)
                (EuclideanSpace.single c 1)) +
              B b b (fderiv ℝ u z) (fderiv ℝ u z)) := by
        rw [hprincipal, hBscale, ← smul_add]
      rw [hvec, hsymSmul]
    _ = r^2 * (-2 * actualRicci E u z i j + actualLie E u z i j) := by
      rw [hGeomBase i j]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SpatialRescaledDeTurckRHS
