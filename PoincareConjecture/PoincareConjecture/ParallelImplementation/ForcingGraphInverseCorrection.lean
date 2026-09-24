import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphInverseCorrection
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
theorem forcing_graph_inverse_correction_bound
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
    (T : ℝ) (a b : ForcingJet A T) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ p : Slab T, b.1 p*(1-a.1 p)=1)
    (hbi : ∀ p : Pair T, b.2 p = b.1 p.1.1*a.2 p*b.1 p.1.2)
    (hbN : ‖b.1‖ ≤ M) :
    ‖b-(BoundedContinuousFunction.const (Slab T) 1,0)‖ ≤ (M+M^2)*‖a‖ :=
/- SWARM_PROOF_BEGIN -/
by
  have hfirst :
      ‖b.1 - BoundedContinuousFunction.const (Slab T) 1‖ ≤ M * ‖a.1‖ := by
    apply (BoundedContinuousFunction.norm_le
      (mul_nonneg hM (norm_nonneg _))).2
    intro p
    rw [BoundedContinuousFunction.sub_apply,
      BoundedContinuousFunction.const_apply]
    have hvalue : b.1 p - 1 = b.1 p * a.1 p := by
      calc
        b.1 p - 1 = b.1 p - b.1 p * (1 - a.1 p) := by rw [hb p]
        _ = b.1 p * a.1 p := by noncomm_ring
    rw [hvalue]
    calc
      ‖b.1 p * a.1 p‖ ≤ ‖b.1 p‖ * ‖a.1 p‖ := norm_mul_le _ _
      _ ≤ M * ‖a.1‖ := by
        apply mul_le_mul
          ((b.1.norm_coe_le_norm p).trans hbN)
          (a.1.norm_coe_le_norm p)
          (norm_nonneg _)
          hM
  have hsecond : ‖b.2‖ ≤ M ^ 2 * ‖a.2‖ := by
    apply (BoundedContinuousFunction.norm_le
      (mul_nonneg (sq_nonneg M) (norm_nonneg _))).2
    intro p
    rw [hbi p]
    calc
      ‖b.1 p.1.1 * a.2 p * b.1 p.1.2‖ ≤
          ‖b.1 p.1.1 * a.2 p‖ * ‖b.1 p.1.2‖ := norm_mul_le _ _
      _ ≤ (‖b.1 p.1.1‖ * ‖a.2 p‖) * ‖b.1 p.1.2‖ := by
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (M * ‖a.2‖) * M := by
        apply mul_le_mul
          (mul_le_mul
            ((b.1.norm_coe_le_norm p.1.1).trans hbN)
            (a.2.norm_coe_le_norm p)
            (norm_nonneg _)
            hM)
          ((b.1.norm_coe_le_norm p.1.2).trans hbN)
          (norm_nonneg _)
          (mul_nonneg hM (norm_nonneg _))
      _ = M ^ 2 * ‖a.2‖ := by ring
  have hfirst' : ‖b.1 - BoundedContinuousFunction.const (Slab T) 1‖ ≤
      M * ‖a‖ := by
    calc
      ‖b.1 - BoundedContinuousFunction.const (Slab T) 1‖ ≤ M * ‖a.1‖ := hfirst
      _ ≤ M * ‖a‖ := mul_le_mul_of_nonneg_left (norm_fst_le a) hM
  have hsecond' : ‖b.2‖ ≤ M ^ 2 * ‖a‖ := by
    calc
      ‖b.2‖ ≤ M ^ 2 * ‖a.2‖ := hsecond
      _ ≤ M ^ 2 * ‖a‖ :=
        mul_le_mul_of_nonneg_left (norm_snd_le a) (sq_nonneg M)
  rw [Prod.norm_def]
  simp only [Prod.fst_sub, Prod.snd_sub, sub_zero]
  apply max_le
  · calc
      ‖b.1 - BoundedContinuousFunction.const (Slab T) 1‖ ≤ M * ‖a‖ := hfirst'
      _ ≤ (M + M ^ 2) * ‖a‖ := by
        nlinarith [mul_nonneg (sq_nonneg M) (norm_nonneg a)]
  · calc
      ‖b.2‖ ≤ M ^ 2 * ‖a‖ := hsecond'
      _ ≤ (M + M ^ 2) * ‖a‖ := by
        nlinarith [mul_nonneg hM (norm_nonneg a)]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphInverseCorrection
