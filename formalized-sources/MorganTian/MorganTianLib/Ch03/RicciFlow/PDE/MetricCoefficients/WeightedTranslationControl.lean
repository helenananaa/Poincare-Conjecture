import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Ω" => Subtype (fun p : E3 × E3 => Prod.fst p ≠ Prod.snd p)

/-- **Math.** weighted translation control. -/
theorem weighted_translation_control 
    (f : E3 → ℝ) (hf : ContDiff ℝ 1 f) (alpha R : ℝ) (ha : 0 < alpha) (hR : 0 ≤ R)
    (D : E3 → ℝ) (hDi : Integrable D volume) (hD : ∀ y, 0 ≤ D y)
    (hder : ∀ y u v : E3, ‖u‖ ≤ R →
      |fderiv ℝ f (y+u) v| * ‖y‖^alpha ≤ D y*‖v‖)
    (h : E3) (hh : ‖h‖ ≤ R) :
    Integrable (fun y : E3 => |f (y+h)-f y| * ‖y‖^alpha) volume ∧
      (∫ y : E3, |f (y+h)-f y| * ‖y‖^alpha) ≤ ‖h‖*(∫ y : E3, D y) :=
/- SWARM_PROOF_BEGIN -/
by
  have hpoint : ∀ y : E3,
      |f (y + h) - f y| * ‖y‖^alpha ≤ D y * ‖h‖ := by
    intro y
    let w : ℝ := ‖y‖^alpha
    have hw : 0 ≤ w := by
      dsimp [w]
      exact Real.rpow_nonneg (norm_nonneg y) alpha
    let g : ℝ → ℝ := fun s => w * f (y + s • h)
    have hline (s : ℝ) :
        HasDerivAt (fun t : ℝ => f (y + t • h))
          (fderiv ℝ f (y + s • h) h) s := by
      have hpath : HasDerivAt (fun t : ℝ => y + t • h) h s := by
        have hsmul : HasDerivAt (fun t : ℝ => t • h) h s := by
          simpa only [one_smul] using (hasDerivAt_id' s).smul_const h
        exact hsmul.const_add y
      have hcomp : HasDerivAt (fun t : ℝ => f (y + t • h))
          (fderiv ℝ f (y + s • h) h) s := by
        simpa only [Function.comp_def] using
          HasFDerivAt.comp_hasDerivAt
            (hl := (hf.differentiable_one (y + s • h)).hasFDerivAt) (hf := hpath)
      exact hcomp
    have hg (s : ℝ) : HasDerivAt g (w * fderiv ℝ f (y + s • h) h) s := by
      simpa [g] using (hline s).const_mul w
    have hmvt : ‖g 1 - g 0‖ ≤ D y * ‖h‖ := by
      apply norm_image_sub_le_of_norm_deriv_le_segment_01'
        (f := g)
        (f' := fun s => w * fderiv ℝ f (y + s • h) h)
        (C := D y * ‖h‖)
      · intro s hs
        exact (hg s).hasDerivWithinAt
      · intro s hs
        have hsabs : |s| ≤ 1 := abs_le.mpr
          ⟨by have hs0 : 0 ≤ s := hs.1; linarith, hs.2.le⟩
        have hu : ‖s • h‖ ≤ R := by
          calc
            ‖s • h‖ = |s| * ‖h‖ := by simp [norm_smul]
            _ ≤ 1 * ‖h‖ := mul_le_mul_of_nonneg_right hsabs (norm_nonneg h)
            _ = ‖h‖ := one_mul _
            _ ≤ R := hh
        calc
          ‖w * fderiv ℝ f (y + s • h) h‖
              = w * |fderiv ℝ f (y + s • h) h| := by
                rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
          _ = |fderiv ℝ f (y + s • h) h| * w := by ring
          _ ≤ D y * ‖h‖ := hder y (s • h) h hu
    have heq : ‖g 1 - g 0‖ = |f (y + h) - f y| * w := by
      calc
        ‖g 1 - g 0‖ = |w * (f (y + h) - f y)| := by
          simp only [Real.norm_eq_abs, g, one_smul, zero_smul, add_zero]
          rw [← mul_sub]
        _ = |f (y + h) - f y| * w := by
          rw [abs_mul, abs_of_nonneg hw]
          ring
    simpa [w] using (heq ▸ hmvt)
  have hweight : Continuous (fun y : E3 => ‖y‖^alpha) :=
    continuous_norm.rpow_const (fun _ => Or.inr ha.le)
  have hcont : Continuous (fun y : E3 => |f (y + h) - f y| * ‖y‖^alpha) := by
    exact (((hf.continuous.comp (continuous_id.add continuous_const)).sub hf.continuous).abs).mul
      hweight
  have hmajor : Integrable (fun y : E3 => ‖h‖ * D y) volume := hDi.const_mul ‖h‖
  have hnonneg : ∀ y : E3, 0 ≤ |f (y + h) - f y| * ‖y‖^alpha := by
    intro y
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg y) alpha)
  have hbound : ∀ y : E3,
      |f (y + h) - f y| * ‖y‖^alpha ≤ ‖h‖ * D y := by
    intro y
    calc
      |f (y + h) - f y| * ‖y‖^alpha ≤ D y * ‖h‖ := hpoint y
      _ = ‖h‖ * D y := by ring
  have hleft : Integrable (fun y : E3 => |f (y + h) - f y| * ‖y‖^alpha) volume :=
    hmajor.mono_nonneg hcont.aestronglyMeasurable
      (ae_of_all _ hnonneg) (ae_of_all _ hbound)
  refine ⟨hleft, ?_⟩
  calc
    ∫ y : E3, |f (y + h) - f y| * ‖y‖^alpha ∂volume
        ≤ ∫ y : E3, ‖h‖ * D y ∂volume := integral_mono hleft hmajor hbound
    _ = ‖h‖ * (∫ y : E3, D y ∂volume) := by rw [integral_const_mul]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
