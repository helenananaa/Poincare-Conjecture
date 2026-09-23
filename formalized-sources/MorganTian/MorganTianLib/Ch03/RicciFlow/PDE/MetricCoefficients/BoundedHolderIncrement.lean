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

/-- **Math.** bounded holder increment. -/
theorem bounded_holder_increment {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (alpha H : ℝ) (hH : 0 ≤ H) (f : E3 →ᵇ V)
    (hf : ∀ x y : E3, ‖f x-f y‖ ≤ H*‖x-y‖^alpha) :
    ∃ Q : Ω →ᵇ V, ‖Q‖ ≤ H ∧ ∀ p : Ω,
      Q p = (‖p.1.1-p.1.2‖^alpha)⁻¹ • (f p.1.1-f p.1.2) :=
/- SWARM_PROOF_BEGIN -/
by
  let d : Ω → ℝ := fun p => ‖p.1.1 - p.1.2‖
  have hdcont : Continuous d := by
    dsimp [d]
    exact continuous_norm.comp
      ((continuous_fst.comp continuous_subtype_val).sub
        (continuous_snd.comp continuous_subtype_val))
  have hdpos (p : Ω) : 0 < d p := by
    apply norm_pos_iff.mpr
    exact sub_ne_zero.mpr p.2
  have hpcont : Continuous (fun p : Ω => d p ^ alpha) :=
    hdcont.rpow_const fun p => Or.inl (ne_of_gt (hdpos p))
  have hinvcont : Continuous (fun p : Ω => (d p ^ alpha)⁻¹) :=
    hpcont.inv₀ fun p => (Real.rpow_pos_of_pos (hdpos p) alpha).ne'
  let q : Ω → V := fun p => (d p ^ alpha)⁻¹ • (f p.1.1 - f p.1.2)
  have hdiffcont : Continuous (fun p : Ω => f p.1.1 - f p.1.2) :=
    (f.continuous.comp (continuous_fst.comp continuous_subtype_val)).sub
      (f.continuous.comp (continuous_snd.comp continuous_subtype_val))
  have hqcont : Continuous q := by
    dsimp [q]
    exact hinvcont.smul hdiffcont
  have hqbound (p : Ω) : ‖q p‖ ≤ H := by
    dsimp [q]
    have hpow : 0 < d p ^ alpha := Real.rpow_pos_of_pos (hdpos p) alpha
    have hdiv : ‖f p.1.1 - f p.1.2‖ / (d p ^ alpha) ≤ H := by
      apply (div_le_iff₀ hpow).2
      simpa [d, mul_comm] using hf p.1.1 p.1.2
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hpow.le)]
    calc
      (d p ^ alpha)⁻¹ * ‖f p.1.1 - f p.1.2‖ =
          ‖f p.1.1 - f p.1.2‖ / (d p ^ alpha) := by
            rw [div_eq_mul_inv]
            ring
      _ ≤ H := hdiv
  refine ⟨BoundedContinuousFunction.ofNormedAddCommGroup q hqcont H hqbound, ?_, ?_⟩
  · exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hqcont hH hqbound
  · intro p
    rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
