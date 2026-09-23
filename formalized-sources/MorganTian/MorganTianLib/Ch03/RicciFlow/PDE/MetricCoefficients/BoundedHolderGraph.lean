import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "JBg" => J3 × (T3 × (Fin 3 → T3))
local notation "E9" => EuclideanSpace ℝ (Fin 3 × Fin 3)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
def boundedHolderGraph (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (alpha : ℝ) : Set ((E3 →ᵇ V) × (Ω →ᵇ V)) :=
  {z | ∀ p : Ω, z.2 p = (‖p.1.1-p.1.2‖^alpha)⁻¹ • (z.1 p.1.1-z.1 p.1.2)}

/-- **Math.** bounded holder graph closed. -/
theorem bounded_holder_graph_closed (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (alpha : ℝ) :
    IsClosed (boundedHolderGraph V alpha) :=
/- SWARM_PROOF_BEGIN -/
by
  have heq : boundedHolderGraph V alpha =
      ⋂ p : Ω, {z : (E3 →ᵇ V) × (Ω →ᵇ V) |
        z.2 p - (‖p.1.1 - p.1.2‖ ^ alpha)⁻¹ •
          (z.1 p.1.1 - z.1 p.1.2) = 0} := by
    ext z
    simp [boundedHolderGraph, sub_eq_zero]
  rw [heq]
  apply isClosed_iInter
  intro p
  have hleft : Continuous (fun z : (E3 →ᵇ V) × (Ω →ᵇ V) => z.2 p) :=
    (continuous_eval_const p).comp continuous_snd
  have hfirst : Continuous (fun z : (E3 →ᵇ V) × (Ω →ᵇ V) => z.1 p.1.1) :=
    (continuous_eval_const p.1.1).comp continuous_fst
  have hsecond : Continuous (fun z : (E3 →ᵇ V) × (Ω →ᵇ V) => z.1 p.1.2) :=
    (continuous_eval_const p.1.2).comp continuous_fst
  have hright : Continuous (fun z : (E3 →ᵇ V) × (Ω →ᵇ V) =>
      (‖p.1.1 - p.1.2‖ ^ alpha)⁻¹ • (z.1 p.1.1 - z.1 p.1.2)) := by
    exact continuous_const.smul (hfirst.sub hsecond)
  exact isClosed_eq (hleft.sub hright) continuous_const
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
