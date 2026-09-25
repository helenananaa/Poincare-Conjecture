import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BoundedDerivativeHolderEstimate
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
theorem holder_of_bounded_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E3 → V) (hf : Differentiable ℝ f) (M L alpha : ℝ)
    (hM : 0 ≤ M) (hL : 0 ≤ L) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hbound : ∀ x : E3, ‖f x‖ ≤ M) (hderiv : ∀ x : E3, ‖fderiv ℝ f x‖ ≤ L) :

    ∀ x y : E3, ‖f x-f y‖ ≤ (2*M+L)*‖x-y‖^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  intro x y
  let r : ℝ := ‖x - y‖
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact norm_nonneg _
  have hLip : ‖f x - f y‖ ≤ L * r := by
    dsimp [r]
    exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hf z) (fun z _ => hderiv z) (by trivial) (by trivial)
  by_cases hr : r ≤ 1
  · have hrpow : r ≤ r ^ alpha := by
      simpa [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_ge' hr0 hr ha.le ha1)
    have hsmall : ‖f x - f y‖ ≤ L * (r ^ alpha) := by
      calc
        ‖f x - f y‖ ≤ L * r := hLip
        _ ≤ L * (r ^ alpha) := mul_le_mul_of_nonneg_left hrpow hL
    have hcoef : L ≤ 2 * M + L := by linarith [hM]
    exact hsmall.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
  · have hr1 : 1 ≤ r := le_of_not_ge hr
    have hbounded : ‖f x - f y‖ ≤ 2 * M := by
      calc
        ‖f x - f y‖ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hbound x) (hbound y)
        _ = 2 * M := by ring
    have hrpow : 1 ≤ r ^ alpha := Real.one_le_rpow hr1 ha.le
    have hcoef : 0 ≤ 2 * M + L := by positivity
    calc
      ‖f x - f y‖ ≤ 2 * M := hbounded
      _ ≤ 2 * M + L := by linarith [hL]
      _ = (2 * M + L) * 1 := by ring
      _ ≤ (2 * M + L) * (r ^ alpha) := mul_le_mul_of_nonneg_left hrpow hcoef
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BoundedDerivativeHolderEstimate
