import PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicIncrementBCF
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BoundedContinuousFunction
/-- Construct the actual normalized increment field on distinct space-time pairs. -/
theorem exists_bounded_parabolic_increment
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T alpha H : ℝ) (ha : 0 < alpha) (hH : 0 ≤ H)
    (f : Slab T → V) (hf : Continuous f)
    (hholder : ∀ p q, ‖f p-f q‖ ≤ H*parabolicRho p q ^ alpha) :
    ∃ Q : Pair T →ᵇ V, ‖Q‖ ≤ H ∧ ∀ p : Pair T,
      Q p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ • (f p.1.1-f p.1.2) :=
/- SWARM_PROOF_BEGIN -/
by
  have hpair : Continuous (fun p : Pair T => (p.1 : Slab T × Slab T)) :=
    continuous_subtype_val
  have hleft : Continuous (fun p : Pair T => p.1.1) :=
    continuous_fst.comp hpair
  have hright : Continuous (fun p : Pair T => p.1.2) :=
    continuous_snd.comp hpair
  have htime : Continuous (fun x : Slab T => (x.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hspace : Continuous (fun x : Slab T => x.2) :=
    continuous_snd
  have hrho_cont : Continuous (fun p : Pair T => parabolicRho p.1.1 p.1.2) := by
    unfold parabolicRho
    exact (continuous_norm.comp ((hspace.comp hleft).sub (hspace.comp hright))).add
      (Real.continuous_sqrt.comp
        (continuous_abs.comp ((htime.comp hleft).sub (htime.comp hright))))
  have hrho_pos (p : Pair T) : 0 < parabolicRho p.1.1 p.1.2 := by
    have htimeOrSpace :
        (p.1.1.1 : ℝ) ≠ (p.1.2.1 : ℝ) ∨ p.1.1.2 ≠ p.1.2.2 := by
      by_contra h
      push Not at h
      apply p.2
      apply Prod.ext
      · exact Subtype.ext h.1
      · exact h.2
    unfold parabolicRho
    rcases htimeOrSpace with ht | hx
    · exact add_pos_of_nonneg_of_pos (norm_nonneg _)
        (Real.sqrt_pos.2 (abs_pos.mpr (sub_ne_zero.mpr ht)))
    · exact add_pos_of_pos_of_nonneg
        (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) (Real.sqrt_nonneg _)
  let rhoPow : Pair T → ℝ := fun p => parabolicRho p.1.1 p.1.2 ^ alpha
  have hrhoPow_cont : Continuous rhoPow := by
    apply continuous_iff_continuousAt.mpr
    intro p
    dsimp [rhoPow]
    exact hrho_cont.continuousAt.rpow_const (Or.inl (ne_of_gt (hrho_pos p)))
  have hrhoPow_pos (p : Pair T) : 0 < rhoPow p :=
    Real.rpow_pos_of_pos (hrho_pos p) alpha
  have hrhoPowInv_cont : Continuous (fun p : Pair T => (rhoPow p)⁻¹) :=
    hrhoPow_cont.inv₀ fun p => (hrhoPow_pos p).ne'
  let raw : Pair T → V := fun p =>
    (rhoPow p)⁻¹ • (f p.1.1 - f p.1.2)
  have hraw_cont : Continuous raw := by
    dsimp [raw]
    exact continuous_smul.comp
      (hrhoPowInv_cont.prodMk ((hf.comp hleft).sub (hf.comp hright)))
  have hraw_bound : ∀ p : Pair T, ‖raw p‖ ≤ H := by
    intro p
    have hp := hrhoPow_pos p
    calc
      ‖raw p‖ = (rhoPow p)⁻¹ * ‖f p.1.1 - f p.1.2‖ := by
        simp only [raw, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
      _ ≤ (rhoPow p)⁻¹ * (H * rhoPow p) :=
        mul_le_mul_of_nonneg_left (hholder p.1.1 p.1.2)
          (inv_nonneg.mpr hp.le)
      _ = H * ((rhoPow p)⁻¹ * rhoPow p) := by ring
      _ = H := by rw [inv_mul_cancel₀ hp.ne']; simp
  let Q : Pair T →ᵇ V :=
    BoundedContinuousFunction.ofNormedAddCommGroup raw hraw_cont H hraw_bound
  refine ⟨Q, ?_, ?_⟩
  · change ‖BoundedContinuousFunction.ofNormedAddCommGroup raw hraw_cont H hraw_bound‖ ≤ H
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hraw_cont hH hraw_bound
  · intro p
    change raw p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
      (f p.1.1 - f p.1.2)
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ParabolicIncrementBCF
