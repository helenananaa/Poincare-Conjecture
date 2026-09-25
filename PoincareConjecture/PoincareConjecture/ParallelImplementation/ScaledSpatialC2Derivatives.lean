import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ScaledSpatialC2Derivatives
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
theorem scaled_spatial_c2_derivatives
    (u : E3 → E6) (hu : ContDiff ℝ 2 u) (x0 : E3) (r : ℝ) :

    ContDiff ℝ 2 (fun y : E3 => u (x0+r • y)) ∧
      (∀ x : E3, fderiv ℝ (fun y : E3 => u (x0+r • y)) x =
        r • fderiv ℝ u (x0+r • x)) ∧
      ∀ x : E3, fderiv ℝ (fderiv ℝ (fun y : E3 => u (x0+r • y))) x =
        r^2 • fderiv ℝ (fderiv ℝ u) (x0+r • x) :=
/- SWARM_PROOF_BEGIN -/
by
  have hA : ContDiff ℝ 2 (fun y : E3 => x0 + r • y) := by
    fun_prop
  refine ⟨?_, ?_, ?_⟩
  · convert hu.comp hA using 1 <;> ext y <;> rfl
  · intro x
    calc
      fderiv ℝ (fun y : E3 => u (x0 + r • y)) x =
          r • fderiv ℝ (fun z : E3 => u (x0 + z)) (r • x) := by
        simpa using
          (fderiv_comp_smul (f := fun z : E3 => u (x0 + z)) (x := x) r)
      _ = r • fderiv ℝ u (x0 + r • x) := by
        rw [fderiv_comp_add_left x0]
  · intro x
    have hfirst : ∀ y : E3,
        fderiv ℝ (fun z : E3 => u (x0 + r • z)) y =
          r • fderiv ℝ u (x0 + r • y) := by
      intro y
      calc
        fderiv ℝ (fun z : E3 => u (x0 + r • z)) y =
            r • fderiv ℝ (fun z : E3 => u (x0 + z)) (r • y) := by
          simpa using
            (fderiv_comp_smul (f := fun z : E3 => u (x0 + z)) (x := y) r)
        _ = r • fderiv ℝ u (x0 + r • y) := by
          rw [fderiv_comp_add_left x0]
    have hfun :
        (fun y : E3 => fderiv ℝ (fun z : E3 => u (x0 + r • z)) y) =
          fun y : E3 => r • fderiv ℝ u (x0 + r • y) := funext hfirst
    calc
      fderiv ℝ (fderiv ℝ (fun y : E3 => u (x0 + r • y))) x =
          fderiv ℝ (fun y : E3 => r • fderiv ℝ u (x0 + r • y)) x := by
        change fderiv ℝ (fun y : E3 => fderiv ℝ (fun z : E3 => u (x0 + r • z)) y) x = _
        rw [hfun]
      _ = r • fderiv ℝ (fun y : E3 => fderiv ℝ u (x0 + r • y)) x := by
        change fderiv ℝ (r • (fun y : E3 => fderiv ℝ u (x0 + r • y))) x = _
        rw [fderiv_const_smul_field r]
        rfl
      _ = r • (r • fderiv ℝ (fun z : E3 => fderiv ℝ u (x0 + z)) (r • x)) := by
        congr 1
        simpa using
          (fderiv_comp_smul (f := fun z : E3 => fderiv ℝ u (x0 + z)) (x := x) r)
      _ = r ^ 2 • fderiv ℝ (fderiv ℝ u) (x0 + r • x) := by
        rw [fderiv_comp_add_left x0]
        rw [smul_smul, pow_two]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ScaledSpatialC2Derivatives
