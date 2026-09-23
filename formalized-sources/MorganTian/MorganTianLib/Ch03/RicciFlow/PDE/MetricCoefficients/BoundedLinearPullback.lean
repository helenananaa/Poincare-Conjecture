import Mathlib
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** bounded linear pullback. -/
theorem bounded_linear_pullback (B : E3 ≃L[ℝ] E3) :
    ∃ P : (E3 →ᵇ ℝ) →L[ℝ] (E3 →ᵇ ℝ),
      (∀ (f : E3 →ᵇ ℝ) (x : E3), P f x = f (B x)) ∧
      (∀ f : E3 →ᵇ ℝ, ‖P f‖ = ‖f‖) ∧ Function.Bijective P :=
/- SWARM_PROOF_BEGIN -/
by
  let b : C(E3, E3) := ⟨B, B.continuous⟩
  let L : (E3 →ᵇ ℝ) →ₗ[ℝ] (E3 →ᵇ ℝ) := {
    toFun := fun f => BoundedContinuousFunction.compContinuous f b
    map_add' := by intro f g; ext x; simp [BoundedContinuousFunction.compContinuous_apply]
    map_smul' := by intro c f; ext x; simp [BoundedContinuousFunction.compContinuous_apply] }
  let P : (E3 →ᵇ ℝ) →L[ℝ] (E3 →ᵇ ℝ) := L.mkContinuous 1 (by
    intro f
    simpa [L] using BoundedContinuousFunction.norm_compContinuous_le f b)
  have hP (f : E3 →ᵇ ℝ) (x : E3) : P f x = f (B x) := by
    simp [P, L, b, BoundedContinuousFunction.compContinuous_apply]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro f x
    exact hP f x
  · intro f
    apply le_antisymm
    · exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).2 fun x => by
        rw [hP]
        exact f.norm_coe_le_norm (B x)
    · exact (BoundedContinuousFunction.norm_le (norm_nonneg (P f))).2 fun y => by
        obtain ⟨x, hx⟩ := B.surjective y
        rw [← hx]
        calc
          ‖f (B x)‖ = ‖P f x‖ := congrArg norm (hP f x).symm
          _ ≤ ‖P f‖ := (P f).norm_coe_le_norm x
  · constructor
    · intro f g h
      apply BoundedContinuousFunction.ext
      intro y
      obtain ⟨x, hx⟩ := B.surjective y
      calc
        f y = f (B x) := congrArg f hx.symm
        _ = P f x := (hP f x).symm
        _ = P g x := congrArg (fun q : E3 →ᵇ ℝ => q x) h
        _ = g (B x) := hP g x
        _ = g y := congrArg g hx
    · intro g
      let bInv : C(E3, E3) := ⟨B.symm, B.symm.continuous⟩
      refine ⟨BoundedContinuousFunction.compContinuous g bInv, ?_⟩
      apply BoundedContinuousFunction.ext
      intro x
      simp [P, L, b, bInv, BoundedContinuousFunction.compContinuous_apply]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
