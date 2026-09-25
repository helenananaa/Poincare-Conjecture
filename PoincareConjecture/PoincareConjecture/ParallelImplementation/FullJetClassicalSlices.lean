import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetClassicalSlices
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
theorem full_jet_classical_slices
    (T alpha : ℝ) (hT : 0 ≤ T) (z : FullJet T) (hz : z ∈ fullParabolicJetSet T alpha hT) :

    (∀ t : Set.Icc (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x)) ∧
      (∀ x : E3, z.1.1.1.2.1 (t,x)=fderiv ℝ (fun y : E3 => z.1.1.1.1 (t,y)) x) ∧
      (∀ x : E3, z.1.1.1.2.2 (t,x)=fderiv ℝ (fderiv ℝ (fun y : E3 => z.1.1.1.1 (t,y))) x)) ∧
    (∀ t : Set.Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ x : E3,
      HasDerivAt (timeExtension z.1.1.1.1 x) (z.1.2 (t,x)) (t:ℝ)) ∧
    ∀ x : E3, z.1.1.1.1 (⟨0,le_rfl,hT⟩,x)=0 :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro t
    have hC2 : ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x)) :=
      (spaceTime_C2_jet_complete T).2 z.1.1.1 hz.1.1 t
    have hspatial :=
      PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification.full_jet_spatial_identification
        T alpha hT z hz t
        (fun x : E3 => z.1.1.1.1 (t,x)) (by intro x; rfl)
    exact ⟨hC2, hspatial.1, hspatial.2⟩
  constructor
  · intro t ht0 htT x
    exact hz.2.1 t ht0 htT x
  · intro x
    exact hz.2.2.2 x
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetClassicalSlices
