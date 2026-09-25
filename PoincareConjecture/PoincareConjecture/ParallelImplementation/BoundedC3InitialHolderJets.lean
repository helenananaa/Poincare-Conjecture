import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.BoundedDerivativeHolderEstimate
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BoundedC3InitialHolderJets
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
theorem exists_bounded_c3_initial_holder_jets
    (u : E3 → E6) (hu : ContDiff ℝ 3 u) (M alpha : ℝ)
    (hM : 0 ≤ M) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (h0 : ∀ x : E3, ‖u x‖ ≤ M)
    (h1 : ∀ x : E3, ‖fderiv ℝ u x‖ ≤ M)
    (h2 : ∀ x : E3, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ M)
    (h3 : ∀ x : E3, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ M) :

    ∃ u0 : E3 →ᵇ E6, ∃ A0 : E3 →ᵇ (E3 →L[ℝ] E6),
      ∃ H0 : E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6),
      (∀ x : E3, u0 x=u x ∧ A0 x=fderiv ℝ u x ∧ H0 x=fderiv ℝ (fderiv ℝ u) x) ∧
      (∀ x : E3, HasFDerivAt u0 (A0 x) x) ∧ (∀ x : E3, HasFDerivAt A0 (H0 x) x) ∧
      ‖u0‖ ≤ M ∧ ‖A0‖ ≤ M ∧ ‖H0‖ ≤ M ∧
      (∀ x y : E3, ‖u0 x-u0 y‖ ≤ (3*M)*‖x-y‖^alpha) ∧
      (∀ x y : E3, ‖A0 x-A0 y‖ ≤ (3*M)*‖x-y‖^alpha) ∧
      (∀ x y : E3, ‖H0 x-H0 y‖ ≤ (3*M)*‖x-y‖^alpha) :=
/- SWARM_PROOF_BEGIN -/
by
  let A : E3 → E3 →L[ℝ] E6 := fun x => fderiv ℝ u x
  let H : E3 → E3 →L[ℝ] E3 →L[ℝ] E6 := fun x => fderiv ℝ (fderiv ℝ u) x
  have hAcontDiff : ContDiff ℝ 2 A := by
    have h := hu.fderiv_right (m := 2) (by norm_num)
    simpa [A] using h
  have hHcontDiff : ContDiff ℝ 1 H := by
    have h := hu.fderiv_right (m := 2) (by norm_num)
    have h' := h.fderiv_right (m := 1) (by norm_num)
    simpa [A, H] using h'
  have huDiff : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hADiff : Differentiable ℝ A := hAcontDiff.differentiable (by norm_num)
  have hHDiff : Differentiable ℝ H := hHcontDiff.differentiable (by norm_num)
  have hAcont : Continuous A := hAcontDiff.continuous
  have hHcont : Continuous H := hHcontDiff.continuous
  let u0 : E3 →ᵇ E6 :=
    BoundedContinuousFunction.ofNormedAddCommGroup u hu.continuous M h0
  let A0 : E3 →ᵇ (E3 →L[ℝ] E6) :=
    BoundedContinuousFunction.ofNormedAddCommGroup A hAcont M h1
  let H0 : E3 →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6) :=
    BoundedContinuousFunction.ofNormedAddCommGroup H hHcont M h2
  have hu0 (x : E3) : u0 x = u x := rfl
  have hA0 (x : E3) : A0 x = fderiv ℝ u x := rfl
  have hH0 (x : E3) : H0 x = fderiv ℝ (fderiv ℝ u) x := rfl
  have hu0eq : (u0 : E3 → E6) = u := funext hu0
  have hA0eq : (A0 : E3 → (E3 →L[ℝ] E6)) = A := funext hA0
  have hUderiv (x : E3) : HasFDerivAt u (fderiv ℝ u x) x := by
    have hAt : DifferentiableAt ℝ u x := huDiff.differentiableAt
    exact hAt.hasFDerivAt
  have hAderiv (x : E3) : HasFDerivAt A (fderiv ℝ (fderiv ℝ u) x) x := by
    have hAt : DifferentiableAt ℝ A x := hADiff.differentiableAt
    have h := hAt.hasFDerivAt
    simpa [A, H] using h
  have huHolder : ∀ x y : E3, ‖u x-u y‖ ≤ (3*M)*‖x-y‖^alpha := by
    intro x y
    simpa [show 2*M+M = 3*M by ring] using
      (PoincareConjecture.ParallelImplementation.BoundedDerivativeHolderEstimate.holder_of_bounded_derivative
        u huDiff M M alpha hM hM ha ha1 h0 h1 x y)
  have hAHolder : ∀ x y : E3, ‖A x-A y‖ ≤ (3*M)*‖x-y‖^alpha := by
    intro x y
    simpa [show 2*M+M = 3*M by ring] using
      (PoincareConjecture.ParallelImplementation.BoundedDerivativeHolderEstimate.holder_of_bounded_derivative
        A hADiff M M alpha hM hM ha ha1 h1 h2 x y)
  have hHHolder : ∀ x y : E3, ‖H x-H y‖ ≤ (3*M)*‖x-y‖^alpha := by
    intro x y
    simpa [show 2*M+M = 3*M by ring] using
      (PoincareConjecture.ParallelImplementation.BoundedDerivativeHolderEstimate.holder_of_bounded_derivative
        H hHDiff M M alpha hM hM ha ha1 h2 h3 x y)
  refine ⟨u0, A0, H0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    exact ⟨hu0 x, hA0 x, hH0 x⟩
  · intro x
    rw [hu0eq, hA0 x]
    exact hUderiv x
  · intro x
    rw [hA0eq, hH0 x]
    exact hAderiv x
  · change ‖BoundedContinuousFunction.ofNormedAddCommGroup u hu.continuous M h0‖ ≤ M
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hu.continuous hM h0
  · change ‖BoundedContinuousFunction.ofNormedAddCommGroup A hAcont M h1‖ ≤ M
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hAcont hM h1
  · change ‖BoundedContinuousFunction.ofNormedAddCommGroup H hHcont M h2‖ ≤ M
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hHcont hM h2
  · intro x y
    simpa [hu0] using huHolder x y
  · intro x y
    simpa [hA0] using hAHolder x y
  · intro x y
    simpa [hH0] using hHHolder x y
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BoundedC3InitialHolderJets
