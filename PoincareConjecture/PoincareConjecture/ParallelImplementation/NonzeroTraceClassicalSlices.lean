import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.NonzeroTraceClassicalSlices
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
theorem nonzero_trace_classical_slices
    (T alpha : ℝ) (z : FullJet T) (hz : z.1.1 ∈ parabolicC2HolderSet T alpha) :

    ∀ t : Set.Icc (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x)) ∧
      (∀ x : E3, z.1.1.1.2.1 (t,x)=fderiv ℝ (fun y : E3 => z.1.1.1.1 (t,y)) x) ∧
      (∀ x : E3, z.1.1.1.2.2 (t,x)=fderiv ℝ (fderiv ℝ (fun y : E3 => z.1.1.1.1 (t,y))) x) :=
/- SWARM_PROOF_BEGIN -/
by
  intro t
  have hjet : z.1.1.1 ∈ spaceTimeC2JetSet T := hz.1
  have hC2 : ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x)) :=
    (spaceTime_C2_jet_complete T).2 z.1.1.1 hjet t
  have hslice := hjet t
  have hgrad : (fun y : E3 => z.1.1.1.2.1 (t,y)) =
      (fun y : E3 => fderiv ℝ (fun w : E3 => z.1.1.1.1 (t,w)) y) := by
    funext y
    exact (hslice.1 y).fderiv.symm
  refine ⟨hC2, ?_, ?_⟩
  · intro x
    exact (hslice.1 x).fderiv.symm
  · intro x
    calc
      z.1.1.1.2.2 (t,x) =
          fderiv ℝ (fun y : E3 => z.1.1.1.2.1 (t,y)) x :=
            (hslice.2 x).fderiv.symm
      _ = fderiv ℝ (fderiv ℝ (fun y : E3 => z.1.1.1.1 (t,y))) x := by
        rw [hgrad]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.NonzeroTraceClassicalSlices
