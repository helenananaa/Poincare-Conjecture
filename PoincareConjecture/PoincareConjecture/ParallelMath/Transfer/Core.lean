import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transfer
open Set
/-- Two-vector area from its actual Gram matrix, including dependent pairs. -/
def gramArea {V : Type*} [AddCommGroup V] [Module ℝ V]
    (G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : V) : ℝ :=
  Real.sqrt (G v v * G w w - (G v w)^2)
/-- A continuous map is non-nullhomotopic when it is not homotopic to any constant. -/
def NonNull {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) : Prop := ¬ ∃ y : Y, f.Homotopic (ContinuousMap.const X y)
/-- The actual subtype of non-nullhomotopic continuous maps, not an abstract admissibility flag. -/
abbrev NonNullMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] :=
  {f : C(X,Y) // NonNull f}
end PoincareConjecture.ParallelMath.Transfer
