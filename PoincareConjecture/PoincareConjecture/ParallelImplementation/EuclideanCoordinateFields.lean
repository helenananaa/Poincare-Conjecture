import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_coordinate_fields :

    ∃ V : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3,
      (∀ (i : Idx) (x : E3), V i x = EuclideanSpace.single i 1) ∧
      (∀ (i j : Idx) (x : E3), Riemannian.DCLieBracket (V i) (V j) x = 0) ∧
      ∀ (f : E3 → ℝ) (i : Idx) (x : E3),
        (V i).dir f x = fderiv ℝ f x (EuclideanSpace.single i 1) :=
/- SWARM_PROOF_BEGIN -/
by
  let V : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3 := fun i =>
    ⟨fun _ => EuclideanSpace.single i 1, by
      rw [contMDiff_vectorSpace_iff_contDiff]
      exact contDiff_const⟩
  refine ⟨V, ?_, ?_, ?_⟩
  · intro i x
    rfl
  · intro i j x
    simp only [Riemannian.DCLieBracket]
    rw [← VectorField.mlieBracketWithin_univ,
      VectorField.mlieBracketWithin_eq_lieBracketWithin,
      VectorField.lieBracketWithin_univ]
    simp [V, VectorField.lieBracket]
  · intro f i x
    change mfderiv 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) f x (V i x) = _
    rw [mfderiv_eq_fderiv]
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields
