import PoincareConjecture.ParallelMath.Transfer
set_option autoImplicit false
noncomputable section
open PoincareConjecture.ParallelMath.Transfer
/-- **Math.** Collinear vectors really have zero Gram area. -/
example {V : Type*} [AddCommGroup V] [Module ℝ V]
    (G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v : V) : gramArea G v ((3 : ℝ) • v) = 0 :=
  gramArea_degenerate G v ((3 : ℝ) • v) (Or.inr ⟨3, rfl⟩)
/-- **Math.** Constant maps are not non-nullhomotopic. -/
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (y : Y) :
    ¬ NonNull (ContinuousMap.const X y) := by
  intro h
  exact h ⟨y, ContinuousMap.Homotopic.refl _⟩
