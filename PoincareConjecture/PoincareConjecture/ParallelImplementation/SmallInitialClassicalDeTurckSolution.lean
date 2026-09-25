import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.SmallInitialRationalHeatSolution
import PoincareConjecture.ParallelImplementation.SixPrincipalCoordinateIdentity
import PoincareConjecture.ParallelImplementation.SixMetricTimeDerivative
import PoincareConjecture.ParallelImplementation.OperatorTwoSidedInverse
import PoincareConjecture.ParallelImplementation.NonzeroTraceClassicalSlices
import PoincareConjecture.ParallelImplementation.ConcreteSixGeometricRHS
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmallInitialClassicalDeTurckSolution
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
theorem exists_small_initial_classical_deturck_solution
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :

    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Idx), (E q v) i=∑ j : Idx, symmetricSixMatrix q i j*v j) ∧
      ∃ epsilon delta C : ℝ, 0 < epsilon ∧ 0 < delta ∧ delta ≤ 1 ∧ 0 < C ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ delta →
        ∀ (u0 : E3 →ᵇ E6) (A0 : E3 →ᵇ (E3 →L[ℝ] E6)) (H0 : E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6)),
          (∀ x : E3, HasFDerivAt u0 (A0 x) x) → (∀ x : E3, HasFDerivAt A0 (H0 x) x) →
          ‖u0‖ ≤ epsilon → ‖A0‖ ≤ epsilon → ‖H0‖ ≤ epsilon →
          (∀ x y : E3, ‖u0 x-u0 y‖ ≤ epsilon*‖x-y‖^alpha) →
          (∀ x y : E3, ‖A0 x-A0 y‖ ≤ epsilon*‖x-y‖^alpha) →
          (∀ x y : E3, ‖H0 x-H0 y‖ ≤ epsilon*‖x-y‖^alpha) →
          ∀ F : ForcingJet E6 T, F ∈ forcingGraph E6 T alpha → ‖F‖ ≤ 1 →
          ∃ z : FullJet T, z.1.1 ∈ parabolicC2HolderSet T alpha ∧
            (z.1.1.1.1,z.1.2) ∈ slabTimeDerivativeGraph T ∧
            (∀ p : Pair T, z.2 p=(parabolicRho p.1.1 p.1.2^alpha)⁻¹ • (z.1.2 p.1.1-z.1.2 p.1.2)) ∧
            ‖z‖ ≤ C ∧ (∀ x : E3, z.1.1.1.1 (⟨0,le_rfl,hT.le⟩,x)=u0 x) ∧
            (∀ t : Set.Icc (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x))) ∧
            (∀ p : Slab T, IsUnit (metricOp E (fun y => z.1.1.1.1 (p.1,y)) p.2) ∧
              ∀ v : E3, (1/2:ℝ)*‖v‖^2 ≤ inner ℝ ((1+E (z.1.1.1.1 p)) v) v) ∧
            ∀ t : Set.Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ (x : E3) (i j : Idx),
              HasDerivAt (fun s : ℝ => (if i=j then 1 else 0)+symmetricSixMatrix (timeExtension z.1.1.1.1 x s) i j)
                (symmetricSixMatrix (F.1 (t,x)) i j - 2*actualRicci E (fun y => z.1.1.1.1 (t,y)) x i j +
                  actualLie E (fun y => z.1.1.1.1 (t,y)) x i j) (t:ℝ) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rcases PoincareConjecture.ParallelImplementation.ConcreteSixGeometricRHS.exists_concrete_six_geometric_rhs with
    ⟨B, hBnorm, hBidentity⟩
  rcases PoincareConjecture.ParallelImplementation.SmallInitialRationalHeatSolution.exists_small_initial_rational_heat_solution
      alpha ha ha1 B with
    ⟨E, hEinj, hEnorm, hEaction, epsilon, delta, C, hepsilon, hdelta, hdelta1,
      hC, hsolution⟩
  refine ⟨E, hEinj, hEnorm, hEaction, epsilon, delta, C, hepsilon, hdelta,
    hdelta1, hC, ?_⟩
  intro T hT hTdelta u0 A0 H0 hu0 hA0 hu0norm hA0norm hH0norm
    hu0holder hA0holder hH0holder F hFgraph hFnorm
  obtain ⟨z, hz, hztimeGraph, hzinc, hzbound, hzinitial, b, hbgraph, hbdata⟩ :=
    hsolution T hT hTdelta u0 A0 H0 hu0 hA0 hu0norm hA0norm hH0norm
      hu0holder hA0holder hH0holder F hFgraph hFnorm
  have hslices :=
    PoincareConjecture.ParallelImplementation.NonzeroTraceClassicalSlices.nonzero_trace_classical_slices
      T alpha z hz

  refine ⟨z, hz, hztimeGraph, hzinc, hzbound, hzinitial, ?_, ?_, ?_⟩
  · intro t
    exact (hslices t).1
  · intro p
    let u : E3 → E6 := fun y => z.1.1.1.1 (p.1, y)
    have hab : (1 + E (u p.2)) * b.1 p = 1 := by
      simpa [u] using (hbdata p).1.1
    have hba : b.1 p * (1 + E (u p.2)) = 1 := by
      simpa [u] using (hbdata p).1.2
    have hcanonical :=
      PoincareConjecture.ParallelImplementation.OperatorTwoSidedInverse.two_sided_inverse_is_canonical
        (metricOp E u p.2) (b.1 p)
        (by simpa [metricOp] using hab) (by simpa [metricOp] using hba)
    refine ⟨hcanonical.1, ?_⟩
    intro v
    simpa [metricOp] using (hbdata p).2.1 v
  · intro t ht0 htT x i j
    let p : Slab T := (t, x)
    let u : E3 → E6 := fun y => z.1.1.1.1 (t, y)
    let G : E3 →L[ℝ] E6 := fderiv ℝ u x
    let H : E3 →L[ℝ] E3 →L[ℝ] E6 := fderiv ℝ (fderiv ℝ u) x
    let traceVec : E6 := ∑ a : Idx,
      H (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)
    let correctionVec : E6 := ∑ a : Idx, ∑ c : Idx,
      ((b.1 p - 1) (EuclideanSpace.single c 1)) a •
        H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)
    let principalVec : E6 := ∑ a : Idx, ∑ c : Idx,
      (b.1 p (EuclideanSpace.single c 1)) a •
        H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)

    have hslice := hslices t
    have hgrad : z.1.1.1.2.1 p = G := by
      simpa [G, p, u] using hslice.2.1 x
    have hhess : z.1.1.1.2.2 p = H := by
      simpa [H, p, u] using hslice.2.2 x
    have hab : (1 + E (u x)) * b.1 p = 1 := by
      simpa [p, u] using (hbdata p).1.1
    have hba : b.1 p * (1 + E (u x)) = 1 := by
      simpa [p, u] using (hbdata p).1.2
    have hcanonical :=
      PoincareConjecture.ParallelImplementation.OperatorTwoSidedInverse.two_sided_inverse_is_canonical
        (metricOp E u x) (b.1 p)
        (by simpa [metricOp] using hab) (by simpa [metricOp] using hba)
    have hbinv : b.1 p = Ring.inverse (metricOp E u x) := by
      simpa [metricOp] using hcanonical.2
    have hInvCoeff (r s : Idx) :
        inverseCoefficients E u x r s = (b.1 p (EuclideanSpace.single s 1)) r := by
      change (Ring.inverse (metricOp E u x) (EuclideanSpace.single s 1)) r = _
      exact congrArg (fun A : E3 →L[ℝ] E3 =>
        (A (EuclideanSpace.single s 1)) r) hbinv.symm

    have hdata := hbdata p
    have hpde : z.1.2 p - traceVec =
        F.1 p + correctionVec + B (b.1 p) (b.1 p) G G := by
      have h := hdata.2.2
      rw [hhess, hgrad] at h
      simpa [traceVec, correctionVec] using h

    have hsymAdd (q r : E6) (a c : Idx) :
        symmetricSixMatrix (q + r) a c =
          symmetricSixMatrix q a c + symmetricSixMatrix r a c := by
      fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
    have hsymSub (q r : E6) (a c : Idx) :
        symmetricSixMatrix (q - r) a c =
          symmetricSixMatrix q a c - symmetricSixMatrix r a c := by
      fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
    have hsymSmul (r : ℝ) (q : E6) (a c : Idx) :
        symmetricSixMatrix (r • q) a c = r * symmetricSixMatrix q a c := by
      fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
    have hsymZero (a c : Idx) : symmetricSixMatrix (0 : E6) a c = 0 := by
      fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
    have hsumFinset (s : Finset Idx) (f : Idx → E6) (a c : Idx) :
        symmetricSixMatrix (s.sum f) a c =
          s.sum (fun k => symmetricSixMatrix (f k) a c) := by
      induction s using Finset.induction_on with
      | empty => simpa using hsymZero a c
      | @insert k s hk ih =>
          rw [Finset.sum_insert hk, Finset.sum_insert hk, hsymAdd, ih]
    have hsum (f : Idx → E6) :
        symmetricSixMatrix (∑ a : Idx, f a) i j =
          ∑ a : Idx, symmetricSixMatrix (f a) i j := by
      simpa using hsumFinset Finset.univ f i j

    have hprincipalIdentity :=
      PoincareConjecture.ParallelImplementation.SixPrincipalCoordinateIdentity.six_principal_coordinate_identity
        H (b.1 p) i j
    have hprincipalIdentity' :
        symmetricSixMatrix (traceVec + correctionVec) i j =
          ∑ a : Idx, ∑ c : Idx,
            (b.1 p (EuclideanSpace.single c 1)) a *
              symmetricSixMatrix (H (EuclideanSpace.single a 1)
                (EuclideanSpace.single c 1)) i j := by
      simpa [traceVec, correctionVec] using hprincipalIdentity
    have hprincipalVecCoord :
        symmetricSixMatrix principalVec i j =
          ∑ a : Idx, ∑ c : Idx,
            (b.1 p (EuclideanSpace.single c 1)) a *
              symmetricSixMatrix (H (EuclideanSpace.single a 1)
                (EuclideanSpace.single c 1)) i j := by
      calc
        symmetricSixMatrix principalVec i j =
            ∑ a : Idx, symmetricSixMatrix
              (∑ c : Idx, (b.1 p (EuclideanSpace.single c 1)) a •
                H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j := by
                  simpa [principalVec] using hsum (fun a : Idx =>
                    ∑ c : Idx, (b.1 p (EuclideanSpace.single c 1)) a •
                      H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1))
        _ = ∑ a : Idx, ∑ c : Idx,
            symmetricSixMatrix
              ((b.1 p (EuclideanSpace.single c 1)) a •
                H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  simpa using hsum (fun c : Idx =>
                    (b.1 p (EuclideanSpace.single c 1)) a •
                      H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1))
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro c hc
          exact hsymSmul _ _ i j
    have hprincipalInvCoord :
        symmetricSixMatrix principalVec i j =
          ∑ a : Idx, ∑ c : Idx,
            inverseCoefficients E u x a c *
              symmetricSixMatrix (H (EuclideanSpace.single a 1)
                (EuclideanSpace.single c 1)) i j := by
      calc
        symmetricSixMatrix principalVec i j =
            ∑ a : Idx, ∑ c : Idx,
              (b.1 p (EuclideanSpace.single c 1)) a *
                symmetricSixMatrix (H (EuclideanSpace.single a 1)
                  (EuclideanSpace.single c 1)) i j := hprincipalVecCoord
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          apply Finset.sum_congr rfl
          intro c hc
          rw [← hInvCoeff a c]
    have hflatCorrection :
        symmetricSixMatrix (traceVec + correctionVec) i j =
          symmetricSixMatrix principalVec i j := by
      calc
        symmetricSixMatrix (traceVec + correctionVec) i j =
            ∑ a : Idx, ∑ c : Idx,
              inverseCoefficients E u x a c *
                symmetricSixMatrix (H (EuclideanSpace.single a 1)
                  (EuclideanSpace.single c 1)) i j := by
                    rw [hprincipalIdentity']
                    apply Finset.sum_congr rfl
                    intro a ha
                    apply Finset.sum_congr rfl
                    intro c hc
                    rw [hInvCoeff a c]
        _ = symmetricSixMatrix principalVec i j := hprincipalInvCoord.symm

    have hConcreteCoord :
        symmetricSixMatrix (principalVec + B (b.1 p) (b.1 p) G G) i j =
          -2 * actualRicci E u x i j + actualLie E u x i j := by
      simpa [principalVec, G, H] using
        hBidentity E hEaction u hslice.1 x (b.1 p) hab hba i j
    have hcoord :
        symmetricSixMatrix (z.1.2 p) i j -
            symmetricSixMatrix traceVec i j =
          symmetricSixMatrix (F.1 p) i j +
            symmetricSixMatrix correctionVec i j +
              symmetricSixMatrix (B (b.1 p) (b.1 p) G G) i j := by
      have h := congrArg (fun q : E6 => symmetricSixMatrix q i j) hpde
      calc
        _ = symmetricSixMatrix (z.1.2 p - traceVec) i j :=
          (hsymSub _ _ i j).symm
        _ = symmetricSixMatrix
              (F.1 p + correctionVec + B (b.1 p) (b.1 p) G G) i j := h
        _ = _ := by rw [hsymAdd, hsymAdd]
    have hcoordinate :
        symmetricSixMatrix (z.1.2 p) i j =
          symmetricSixMatrix (F.1 p) i j - 2 * actualRicci E u x i j +
            actualLie E u x i j := by
      have hsplit :
          symmetricSixMatrix traceVec i j +
              symmetricSixMatrix correctionVec i j =
            symmetricSixMatrix principalVec i j := by
        calc
          _ = symmetricSixMatrix (traceVec + correctionVec) i j :=
            (hsymAdd _ _ i j).symm
          _ = symmetricSixMatrix principalVec i j := hflatCorrection
      calc
        symmetricSixMatrix (z.1.2 p) i j =
            symmetricSixMatrix (F.1 p) i j +
              (symmetricSixMatrix traceVec i j +
                symmetricSixMatrix correctionVec i j +
                symmetricSixMatrix (B (b.1 p) (b.1 p) G G) i j) := by
                  linarith only [hcoord]
        _ = symmetricSixMatrix (F.1 p) i j +
              (symmetricSixMatrix principalVec i j +
                symmetricSixMatrix (B (b.1 p) (b.1 p) G G) i j) := by
                  rw [hsplit]
        _ = symmetricSixMatrix (F.1 p) i j +
              symmetricSixMatrix
                (principalVec + B (b.1 p) (b.1 p) G G) i j := by
                  rw [hsymAdd]
        _ = _ := by rw [hConcreteCoord]; ring

    have htime := hztimeGraph t ht0 htT x
    have hmetricDeriv :=
      PoincareConjecture.ParallelImplementation.SixMetricTimeDerivative.six_metric_time_derivative
        (timeExtension z.1.1.1.1 x) (z.1.2 p) (t : ℝ) htime
    rw [← hcoordinate]
    exact hmetricDeriv i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmallInitialClassicalDeTurckSolution
