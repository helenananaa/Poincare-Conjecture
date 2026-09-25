import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
import PoincareConjecture.ParallelImplementation.RationalInverseMetricHeatSolution
import PoincareConjecture.ParallelImplementation.SixCoordinateDeTurckNonlinearity
import PoincareConjecture.ParallelImplementation.SixPrincipalCoordinateIdentity
import PoincareConjecture.ParallelImplementation.OperatorTwoSidedInverse
import PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra
import PoincareConjecture.ParallelImplementation.FullJetClassicalSlices
import PoincareConjecture.ParallelImplementation.SixMetricTimeDerivative
import PoincareConjecture.ParallelImplementation.SixActualCoordinateGeometry
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixClassicalDeTurckSolution
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
theorem exists_classical_coordinate_deturck_solution
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :

    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j * v j) ∧
      ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ delta →
        ∀ F : PoincareConjecture.ParallelImplementation.ParabolicForcingSpace.ForcingJet E6 T,
          F ∈ PoincareConjecture.ParallelImplementation.ParabolicForcingSpace.forcingGraph E6 T alpha → ‖F‖ ≤ 1 →
        ∃ z : FullJet T, z ∈ fullParabolicJetSet T alpha hT.le ∧ ‖z‖ ≤ C ∧
          (∀ t : Set.Icc (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x))) ∧
          (∀ p : Slab T, IsUnit (metricOp E (fun x => z.1.1.1.1 (p.1,x)) p.2) ∧
            ∀ v : E3, (1/2:ℝ)*‖v‖^2 ≤ inner ℝ ((1+E (z.1.1.1.1 p)) v) v) ∧
          ∀ t : Set.Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ (x : E3) (i j : Idx),
            HasDerivAt (fun s : ℝ => (if i=j then 1 else 0)+symmetricSixMatrix (timeExtension z.1.1.1.1 x s) i j)
              (symmetricSixMatrix (F.1 (t,x)) i j - 2*actualRicci E (fun y => z.1.1.1.1 (t,y)) x i j +
                actualLie E (fun y => z.1.1.1.1 (t,y)) x i j) (t:ℝ) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rcases PoincareConjecture.ParallelImplementation.SixCoordinateDeTurckNonlinearity.exists_concrete_six_deturck_nonlinearity with
    ⟨B, hBnorm, hBentry, hBdiagonal⟩
  rcases PoincareConjecture.ParallelImplementation.RationalInverseMetricHeatSolution.exists_rational_inverse_metric_heat_solution
      alpha ha ha1 B with
    ⟨E, hEinj, hEnorm, hEaction, C, delta, hC, hdelta, hdelta1, hsolution⟩
  refine ⟨E, hEinj, hEnorm, hEaction, C, delta, hC, hdelta, hdelta1, ?_⟩
  intro T hT hTdelta F hFgraph hFnorm
  obtain ⟨z, hz, hzbound, b, hbgraph, hbdata⟩ :=
    hsolution T hT hTdelta F hFgraph hFnorm
  have hslices :=
    PoincareConjecture.ParallelImplementation.FullJetClassicalSlices.full_jet_classical_slices
      T alpha hT.le z hz

  have hrelations (p : Slab T) :
      metricOp E (fun y : E3 => z.1.1.1.1 (p.1, y)) p.2 * b.1 p = 1 ∧
        b.1 p * metricOp E (fun y : E3 => z.1.1.1.1 (p.1, y)) p.2 = 1 := by
    rcases hbdata p with ⟨⟨hab, hba⟩, _, _⟩
    constructor
    · simpa [metricOp] using hab
    · simpa [metricOp] using hba

  have hcanonicalAt (p : Slab T) :
      IsUnit (metricOp E (fun y : E3 => z.1.1.1.1 (p.1, y)) p.2) ∧
        b.1 p = Ring.inverse (metricOp E (fun y : E3 => z.1.1.1.1 (p.1, y)) p.2) := by
    exact PoincareConjecture.ParallelImplementation.OperatorTwoSidedInverse.two_sided_inverse_is_canonical
      (metricOp E (fun y : E3 => z.1.1.1.1 (p.1, y)) p.2) (b.1 p)
      (hrelations p).1 (hrelations p).2

  refine ⟨z, hz, hzbound, ?_, ?_, ?_⟩
  · intro t
    exact (hslices.1 t).1
  · intro p
    refine ⟨(hcanonicalAt p).1, ?_⟩
    rcases hbdata p with ⟨_, hcoercive, _⟩
    simpa [metricOp] using hcoercive
  · intro t ht0 htT x i j
    let p : Slab T := (t, x)
    let u : E3 → E6 := fun y => z.1.1.1.1 (t, y)
    let G : E3 →L[ℝ] E6 := fderiv ℝ u x
    let H : E3 →L[ℝ] E3 →L[ℝ] E6 := fderiv ℝ (fderiv ℝ u) x
    let traceVec : E6 := ∑ a : Idx, H (EuclideanSpace.single a 1) (EuclideanSpace.single a 1)
    let correctionVec : E6 := ∑ a : Idx, ∑ c : Idx,
      ((b.1 p - 1) (EuclideanSpace.single c 1)) a •
        H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)
    let principal : ℝ := ∑ a : Idx, ∑ c : Idx,
      (b.1 p (EuclideanSpace.single c 1)) a *
        symmetricSixMatrix (H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j

    have hslice := hslices.1 t
    have hgrad : z.1.1.1.2.1 p = G := by
      simpa [G, p, u] using hslice.2.1 x
    have hhess : z.1.1.1.2.2 p = H := by
      simpa [H, p, u] using hslice.2.2 x

    have hab : (1 + E (u x)) * b.1 p = 1 := by
      simpa [metricOp, p, u] using (hrelations p).1
    have hba : b.1 p * (1 + E (u x)) = 1 := by
      simpa [metricOp, p, u] using (hrelations p).2
    have hunit : IsUnit (metricOp E u x) := by
      simpa [p, u] using (hcanonicalAt p).1
    have hbinv : b.1 p = Ring.inverse (metricOp E u x) := by
      simpa [p, u] using (hcanonicalAt p).2
    have hInvCoeff (r s : Idx) :
        inverseCoefficients E u x r s = (b.1 p (EuclideanSpace.single s 1)) r := by
      change (Ring.inverse (metricOp E u x) (EuclideanSpace.single s 1)) r = _
      exact congrArg (fun A : E3 →L[ℝ] E3 => (A (EuclideanSpace.single s 1)) r) hbinv.symm

    have hAlg :=
      PoincareConjecture.ParallelImplementation.SixInverseCoordinateAlgebra.six_inverse_coordinate_algebra
        E hEaction (u x) (b.1 p) (by simpa [metricOp] using hab)
        (by simpa [metricOp] using hba)
    have hbsym : ∀ r s : Idx,
        (b.1 p (EuclideanSpace.single s 1)) r =
          (b.1 p (EuclideanSpace.single r 1)) s := by
      intro r s
      simpa using hAlg.2.1 r s

    have hgeom :=
      PoincareConjecture.ParallelImplementation.SixActualCoordinateGeometry.actual_coordinate_geometry
        E hEaction u hslice.1 x hunit

    have hBdiag := hBdiagonal (b.1 p) G hbsym i j
    have hInvMatrix :
        (fun r s : Idx => (b.1 p (EuclideanSpace.single s 1)) r) =
          inverseCoefficients E u x := by
      funext r s
      exact (hInvCoeff r s).symm
    have hGradMatrix :
        (fun a r s : Idx => symmetricSixMatrix (G (EuclideanSpace.single a 1)) r s) =
          firstCoefficients u x := by
      funext a r s
      rfl
    rw [hInvMatrix, hGradMatrix] at hBdiag
    have hBcoord :
        symmetricSixMatrix (B (b.1 p) (b.1 p) G G) i j =
          deturckQuadratic (inverseCoefficients E u x) (inverseCoefficients E u x)
            (firstCoefficients u x) (firstCoefficients u x) i j := hBdiag

    have hprincipalIdentity :=
      PoincareConjecture.ParallelImplementation.SixPrincipalCoordinateIdentity.six_principal_coordinate_identity
        H (b.1 p) i j
    have hprincipalIdentity' :
        symmetricSixMatrix (traceVec + correctionVec) i j = principal := by
      simpa [traceVec, correctionVec, principal] using hprincipalIdentity

    have hsymAdd (q r : E6) (a c : Idx) :
        symmetricSixMatrix (q + r) a c = symmetricSixMatrix q a c + symmetricSixMatrix r a c := by
      fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
    have hsymSub (q r : E6) (a c : Idx) :
        symmetricSixMatrix (q - r) a c = symmetricSixMatrix q a c - symmetricSixMatrix r a c := by
      fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
    have hsymSmul (r : ℝ) (q : E6) (a c : Idx) :
        symmetricSixMatrix (r • q) a c = r * symmetricSixMatrix q a c := by
      fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
    have hsymZero (a c : Idx) : symmetricSixMatrix (0 : E6) a c = 0 := by
      fin_cases a <;> fin_cases c <;> simp [symmetricSixMatrix]
    have hsumFinset (s : Finset Idx) (f : Idx → E6)
        (a c : Idx) :
        symmetricSixMatrix (s.sum f) a c = s.sum (fun k => symmetricSixMatrix (f k) a c) := by
      classical
      induction s using Finset.induction_on with
      | empty => simpa using hsymZero a c
      | @insert k s hk ih =>
          rw [Finset.sum_insert hk, Finset.sum_insert hk, hsymAdd, ih]
    have hsum (f : Idx → E6) :
        symmetricSixMatrix (∑ a : Idx, f a) i j =
          ∑ a : Idx, symmetricSixMatrix (f a) i j := by
      simpa using hsumFinset Finset.univ f i j

    have hpde :
        z.1.2 p - traceVec = F.1 p + correctionVec + B (b.1 p) (b.1 p) G G := by
      have h := (hbdata p).2.2
      rw [hhess, hgrad] at h
      simpa [traceVec, correctionVec] using h
    have htrace :
        symmetricSixMatrix traceVec i j =
          ∑ a : Idx, symmetricSixMatrix (H (EuclideanSpace.single a 1)
            (EuclideanSpace.single a 1)) i j := by
      simpa [traceVec] using hsum (fun a : Idx =>
        H (EuclideanSpace.single a 1) (EuclideanSpace.single a 1))
    have hcorrection :
        symmetricSixMatrix correctionVec i j =
          ∑ a : Idx, ∑ c : Idx,
            ((b.1 p - 1) (EuclideanSpace.single c 1)) a *
              symmetricSixMatrix (H (EuclideanSpace.single a 1)
                (EuclideanSpace.single c 1)) i j := by
      calc
        symmetricSixMatrix correctionVec i j =
            ∑ a : Idx, symmetricSixMatrix
              (∑ c : Idx, ((b.1 p - 1) (EuclideanSpace.single c 1)) a •
                H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j := by
                  simpa [correctionVec] using hsum (fun a : Idx =>
                    ∑ c : Idx, ((b.1 p - 1) (EuclideanSpace.single c 1)) a •
                      H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1))
        _ = ∑ a : Idx, ∑ c : Idx,
            ((b.1 p - 1) (EuclideanSpace.single c 1)) a *
              symmetricSixMatrix (H (EuclideanSpace.single a 1)
                (EuclideanSpace.single c 1)) i j := by
              apply Finset.sum_congr rfl
              intro a ha
              calc
                symmetricSixMatrix
                    (∑ c : Idx, ((b.1 p - 1) (EuclideanSpace.single c 1)) a •
                      H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j =
                    ∑ c : Idx, symmetricSixMatrix
                      (((b.1 p - 1) (EuclideanSpace.single c 1)) a •
                        H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1)) i j := by
                          simpa using hsum (fun c : Idx =>
                            ((b.1 p - 1) (EuclideanSpace.single c 1)) a •
                              H (EuclideanSpace.single a 1) (EuclideanSpace.single c 1))
                _ = ∑ c : Idx,
                    ((b.1 p - 1) (EuclideanSpace.single c 1)) a *
                      symmetricSixMatrix (H (EuclideanSpace.single a 1)
                        (EuclideanSpace.single c 1)) i j := by
                      apply Finset.sum_congr rfl
                      intro c hc
                      exact hsymSmul _ _ i j

    have hprincipalSplit :
        symmetricSixMatrix traceVec i j + symmetricSixMatrix correctionVec i j = principal := by
      calc
        symmetricSixMatrix traceVec i j + symmetricSixMatrix correctionVec i j =
            symmetricSixMatrix (traceVec + correctionVec) i j := (hsymAdd _ _ i j).symm
        _ = principal := hprincipalIdentity'

    have hpdeCoord :
        symmetricSixMatrix (z.1.2 p) i j =
          symmetricSixMatrix (F.1 p) i j +
            (principal + symmetricSixMatrix (B (b.1 p) (b.1 p) G G) i j) := by
      have hcoord := congrArg (fun q : E6 => symmetricSixMatrix q i j) hpde
      have hcoord' :
          symmetricSixMatrix (z.1.2 p) i j - symmetricSixMatrix traceVec i j =
            symmetricSixMatrix (F.1 p) i j + symmetricSixMatrix correctionVec i j +
              symmetricSixMatrix (B (b.1 p) (b.1 p) G G) i j := by
        calc
          _ = symmetricSixMatrix (z.1.2 p - traceVec) i j := (hsymSub _ _ i j).symm
          _ = symmetricSixMatrix (F.1 p + correctionVec +
                B (b.1 p) (b.1 p) G G) i j := hcoord
          _ = _ := by rw [hsymAdd, hsymAdd]
      calc
        symmetricSixMatrix (z.1.2 p) i j =
            symmetricSixMatrix (F.1 p) i j +
              ((symmetricSixMatrix traceVec i j + symmetricSixMatrix correctionVec i j) +
                symmetricSixMatrix (B (b.1 p) (b.1 p) G G) i j) := by linarith
        _ = symmetricSixMatrix (F.1 p) i j +
              (principal + symmetricSixMatrix (B (b.1 p) (b.1 p) G G) i j) := by
                rw [hprincipalSplit]

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

    have hcoordinate :
        symmetricSixMatrix (z.1.2 p) i j =
          symmetricSixMatrix (F.1 p) i j - 2 * actualRicci E u x i j +
            actualLie E u x i j := by
      calc
        symmetricSixMatrix (z.1.2 p) i j =
            symmetricSixMatrix (F.1 p) i j +
              (principal + symmetricSixMatrix (B (b.1 p) (b.1 p) G G) i j) := hpdeCoord
        _ = symmetricSixMatrix (F.1 p) i j +
              ((∑ a : Idx, ∑ c : Idx,
                  inverseCoefficients E u x a c * secondCoefficients u x a c i j) +
                deturckQuadratic (inverseCoefficients E u x) (inverseCoefficients E u x)
                  (firstCoefficients u x) (firstCoefficients u x) i j) := by
                rw [hprincipalActual, hBcoord]
        _ = symmetricSixMatrix (F.1 p) i j +
              (-2 * actualRicci E u x i j + actualLie E u x i j) := by
                rw [← hgeom.2.2 i j]
        _ = _ := by ring

    have htime := hslices.2.1 t ht0 htT x
    have hmetricDeriv :=
      PoincareConjecture.ParallelImplementation.SixMetricTimeDerivative.six_metric_time_derivative
        (timeExtension z.1.1.1.1 x) (z.1.2 p) (t : ℝ) htime
    rw [← hcoordinate]
    exact hmetricDeriv i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixClassicalDeTurckSolution
