import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedHolderGraph
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

/-- **Math.** bounded holder graph norm. -/
theorem bounded_holder_graph_norm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (alpha : ℝ)
    (z : (E3 →ᵇ V) × (Ω →ᵇ V)) (hz : z ∈ boundedHolderGraph V alpha) :
    (∀ x y : E3, ‖z.1 x-z.1 y‖ ≤ ‖z.2‖*‖x-y‖^alpha) ∧
      ∀ H : ℝ, 0 ≤ H → (∀ x y : E3, ‖z.1 x-z.1 y‖ ≤ H*‖x-y‖^alpha) → ‖z.2‖ ≤ H :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro x y
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, norm_zero]
      positivity
    · let p : Ω := ⟨(x, y), hxy⟩
      have hdist : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hpow : 0 < ‖x - y‖ ^ alpha := Real.rpow_pos_of_pos hdist alpha
      have hgraph : z.2 p = (‖x - y‖ ^ alpha)⁻¹ • (z.1 x - z.1 y) := by
        exact hz p
      have hnorm : ‖z.2 p‖ = (‖x - y‖ ^ alpha)⁻¹ * ‖z.1 x - z.1 y‖ := by
        rw [hgraph, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpow)]
      have hscaled : ‖z.1 x - z.1 y‖ = ‖z.2 p‖ * ‖x - y‖ ^ alpha := by
        rw [hnorm]
        field_simp [ne_of_gt hpow]
      calc
        ‖z.1 x - z.1 y‖ = ‖z.2 p‖ * ‖x - y‖ ^ alpha := hscaled
        _ ≤ ‖z.2‖ * ‖x - y‖ ^ alpha :=
          mul_le_mul_of_nonneg_right (BoundedContinuousFunction.norm_coe_le_norm z.2 p)
            (le_of_lt hpow)
  · intro H hH hbound
    apply (BoundedContinuousFunction.norm_le hH).2
    intro p
    have hdist : 0 < ‖p.1.1 - p.1.2‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr p.2)
    have hpow : 0 < ‖p.1.1 - p.1.2‖ ^ alpha :=
      Real.rpow_pos_of_pos hdist alpha
    have hgraph : z.2 p =
        (‖p.1.1 - p.1.2‖ ^ alpha)⁻¹ • (z.1 p.1.1 - z.1 p.1.2) := hz p
    have hnorm : ‖z.2 p‖ =
        (‖p.1.1 - p.1.2‖ ^ alpha)⁻¹ * ‖z.1 p.1.1 - z.1 p.1.2‖ := by
      rw [hgraph, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpow)]
    have hscaled : ‖z.1 p.1.1 - z.1 p.1.2‖ =
        ‖z.2 p‖ * ‖p.1.1 - p.1.2‖ ^ alpha := by
      rw [hnorm]
      field_simp [ne_of_gt hpow]
    have hmul : ‖z.2 p‖ * ‖p.1.1 - p.1.2‖ ^ alpha ≤
        H * ‖p.1.1 - p.1.2‖ ^ alpha := by
      rw [← hscaled]
      exact hbound p.1.1 p.1.2
    exact le_of_mul_le_mul_right hmul hpow
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
