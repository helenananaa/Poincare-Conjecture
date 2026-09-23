import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedHolderGraph
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedHolderIncrement
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

/-- **Math.** bounded holder graph complete. -/
theorem bounded_holder_graph_complete (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] (alpha : ℝ) :
    IsComplete (boundedHolderGraph V alpha) ∧
      ∀ (H : ℝ), 0 ≤ H → ∀ f : E3 →ᵇ V,
        (∀ x y : E3, ‖f x-f y‖ ≤ H*‖x-y‖^alpha) →
        ∃ Q : Ω →ᵇ V, (f,Q) ∈ boundedHolderGraph V alpha ∧ ‖Q‖ ≤ H :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · exact (bounded_holder_graph_closed V alpha).isComplete
  · intro H hH f hf
    obtain ⟨Q, hQ, hQeq⟩ := bounded_holder_increment alpha H hH f hf
    refine ⟨Q, ?_, hQ⟩
    change ∀ p : Ω,
      Q p = (‖p.1.1 - p.1.2‖ ^ alpha)⁻¹ • (f p.1.1 - f p.1.2)
    exact hQeq
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
