import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Extended-distance comparisons give explicit ball inclusions without finiteness of distances. -/
theorem extended_distance_ball_sandwich {X : Type*} (d0 d1 : X → X → ℝ≥0∞)
    (l u : ℝ≥0∞) (hl0 : l ≠ 0) (hlt : l ≠ ⊤) (hu0 : u ≠ 0) (hut : u ≠ ⊤)
    (h : ∀ x y, l * d0 x y ≤ d1 x y ∧ d1 x y ≤ u * d0 x y)
    (x : X) (r : ℝ≥0∞) :
    {y | d0 x y < r/u} ⊆ {y | d1 x y < r} ∧
    {y | d1 x y < r} ⊆ {y | d0 x y < r/l} :=
/- SWARM_PROOF_BEGIN -/
by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · have hy' : d0 x y * u < r :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hu0) (Or.inl hut)).1 hy
    exact (h x y).2.trans_lt (by rwa [mul_comm])
  · have hy' : l * d0 x y < r := (h x y).1.trans_lt hy
    exact (ENNReal.lt_div_iff_mul_lt (Or.inl hl0) (Or.inl hlt)).2 (by rwa [mul_comm] at hy')
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
