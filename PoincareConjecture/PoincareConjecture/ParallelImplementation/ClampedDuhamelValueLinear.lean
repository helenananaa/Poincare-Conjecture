import PoincareConjecture.ParallelImplementation.SlabClampLinearExtension
import PoincareConjecture.ParallelImplementation.VectorDuhamelBoundedLinear
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ClampedDuhamelValueLinear
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open MorganTianLib.ParabolicPDE Set MeasureTheory
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- The exact clamped Duhamel value formula is linear on all bounded continuous slab data. -/
theorem exists_clamped_duhamel_value_linear (T : ℝ) (hT : 0 ≤ T) :
    ∃ v : (Slab T →ᵇ E6) →ₗ[ℝ] (Slab T →ᵇ E6),
      ∀ (F : Slab T →ᵇ E6) (p : Slab T) (k : Fin 6),
        (v F p) k = ∫ s in (0:ℝ)..(p.1:ℝ), ∫ y : E3,
          euclideanHeatKernel 3 ((p.1:ℝ)-s) (p.2-y) *
            (F (Set.projIcc 0 T hT s,y) k) := by
  obtain ⟨E, _, hE, _, _⟩ :=
    PoincareConjecture.ParallelImplementation.SlabClampLinearExtension.exists_slab_clamp_linear_extension E6 T hT
  obtain ⟨V, _, hV⟩ :=
    PoincareConjecture.ParallelImplementation.VectorDuhamelBoundedLinear.exists_vector_duhamel_boundedLinear T hT
  refine ⟨V.toLinearMap.comp E.toLinearMap, ?_⟩
  intro F p k
  change (V (E F) p) k = _
  rw [hV (E F) p k]
  apply intervalIntegral.integral_congr
  intro s hs
  apply integral_congr_ae
  filter_upwards [] with y
  rw [hE F (s,y)]
end PoincareConjecture.ParallelImplementation.ClampedDuhamelValueLinear
