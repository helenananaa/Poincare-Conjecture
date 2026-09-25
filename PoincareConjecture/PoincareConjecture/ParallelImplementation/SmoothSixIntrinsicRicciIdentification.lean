import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.Basic
import PoincareConjecture.ParallelImplementation.SixCurvatureTraceIndices
import PoincareConjecture.ParallelImplementation.IntrinsicRicciCoordinateTrace
import PoincareConjecture.ParallelImplementation.SmoothSixCurvatureIdentification
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicRicciIdentification
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_six_intrinsic_ricci_identification
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ (x v : E3), v ≠ 0 → 0 < inner ℝ (metricOp E u x v) v) :

    ∃ g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3,
      (∀ (x v w : E3), g.metricInner x v w = inner ℝ (metricOp E u x v) w) ∧
      ∀ (x : E3) (i j : Idx), MorganTianLib.ricciTensorAt g x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = actualRicci E u x i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨g, V, hg, hV, hcurv⟩ :=
    PoincareConjecture.ParallelImplementation.SmoothSixCurvatureIdentification.exists_six_curvature_identification
      E hE u hu hpos
  refine ⟨g, hg, ?_⟩
  intro x i j
  have hsymm :
      MorganTianLib.ricciTensorAt g x (EuclideanSpace.single i 1)
          (EuclideanSpace.single j 1) =
        MorganTianLib.ricciTensorAt g x (EuclideanSpace.single j 1)
          (EuclideanSpace.single i 1) := by
    open scoped Bundle in
    letI : NormedAddCommGroup (TangentSpace (𝓘(ℝ, E3)) x) :=
      (g.toRiemannianMetric.toCore x).toNormedAddCommGroupOfTopology
        (g.toRiemannianMetric.continuousAt x) (g.toRiemannianMetric.isVonNBounded x)
    letI : InnerProductSpace ℝ (TangentSpace (𝓘(ℝ, E3)) x) :=
      InnerProductSpace.ofCoreOfTopology (g.toRiemannianMetric.toCore x)
        (g.toRiemannianMetric.continuousAt x) (g.toRiemannianMetric.isVonNBounded x)
    letI : Bundle.RiemannianBundle (TangentSpace (𝓘(ℝ, E3)) : E3 → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let hLC : g.leviCivitaConnection.IsLeviCivita g :=
      g.leviCivitaConnection.isLeviCivita_of_koszulDual g
        (fun X Y Z q => g.koszulDualSection_dual X Y Z q)
    let hB : Riemannian.IsAlgCurvatureForm
        (g.leviCivitaConnection.curvatureFormAt g x) :=
      g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC x
    change Riemannian.ricciBilin hB (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) =
      Riemannian.ricciBilin hB (EuclideanSpace.single j 1)
        (EuclideanSpace.single i 1)
    rw [Riemannian.ricciBilin_apply, Riemannian.ricciBilin_apply]
    exact Riemannian.ricciForm_symm hB _ _
  calc
    MorganTianLib.ricciTensorAt g x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) =
      MorganTianLib.ricciTensorAt g x (EuclideanSpace.single j 1)
        (EuclideanSpace.single i 1) := hsymm
    _ = ∑ k : Idx,
        (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ)
          ((g.leviCivitaConnection.curvature (V j) (V k) (V i)) x) :=
      PoincareConjecture.ParallelImplementation.IntrinsicRicciCoordinateTrace.ricci_eq_coordinate_curvature_trace
        g V hV x j i
    _ = actualRicci E u x i j := by
      have htrace :
          (∑ k : Idx,
            (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ)
              ((g.leviCivitaConnection.curvature (V j) (V k) (V i)) x)) =
          ∑ k : Idx,
            (deriv (fun t : ℝ => (christoffelField E u)
                (x + t • EuclideanSpace.single k 1) k j i) 0 -
             deriv (fun t : ℝ => (christoffelField E u)
                (x + t • EuclideanSpace.single j 1) k k i) 0 +
             ∑ m : Idx,
               ((christoffelField E u) x m j i * (christoffelField E u) x k k m -
                (christoffelField E u) x m k i * (christoffelField E u) x k j m)) := by
        apply Finset.sum_congr rfl
        intro k hk
        exact hcurv x j k i k
      rw [htrace]
      exact PoincareConjecture.ParallelImplementation.SixCurvatureTraceIndices.six_curvature_trace_indices
        E u x i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothSixIntrinsicRicciIdentification
