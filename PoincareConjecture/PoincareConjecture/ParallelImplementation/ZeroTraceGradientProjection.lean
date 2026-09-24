import PoincareConjecture.ParallelImplementation.BoundedHolderLinearLift
import PoincareConjecture.ParallelImplementation.ZeroTraceGradientHolderSmallness
import PoincareConjecture.ParallelImplementation.ParabolicIncrementBCF
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ZeroTraceGradientProjection
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance (T : ℝ) : NormedAddCommGroup (FullJet T) := inferInstance
local instance (T : ℝ) : NormedSpace ℝ (FullJet T) := inferInstance
/-- Actual zero-trace gradients lift linearly into the forcing Holder space with a small norm. -/
theorem exists_zero_trace_gradient_projection (T alpha : ℝ)
    (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha < 1)
    (Y : Submodule ℝ (FullJet T))
    (hY : (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le) :
    ∃ P : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E6) T,
      ‖P‖ ≤ 3 * Real.sqrt T + 16 * T^((1-alpha)/2) ∧
      (∀ z : Y, ∀ p : Slab T, (P z).1 p = z.1.1.1.1.2.1 p) ∧
      ∀ z : Y, P z ∈ forcingGraph (E3 →L[ℝ] E6) T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  have hz (z : Y) : z.1 ∈ fullParabolicJetSet T alpha hT.le := by
    rw [← hY]
    exact z.2
  let P : Y →ₗ[ℝ] (Slab T →ᵇ (E3 →L[ℝ] E6)) := {
    toFun := fun z => z.1.1.1.1.2.1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hb (z : Y) : ‖P z‖ ≤ (3*Real.sqrt T)*‖z‖ := by
    let w : FullJet T := z.1
    have h := PoincareConjecture.ParallelImplementation.ZeroTraceLowerJetSmallness.zero_trace_lower_jet_smallness T alpha hT w (hz z)
    have ht : ‖w.1.2‖ ≤ ‖w‖ := (norm_snd_le w.1).trans (norm_fst_le w)
    have hH : ‖w.1.1.1.2.2‖ ≤ ‖w‖ :=
      (norm_snd_le w.1.1.1.2).trans ((norm_snd_le w.1.1.1).trans
        ((norm_fst_le w.1.1).trans ((norm_fst_le w.1).trans (norm_fst_le w))))
    calc
      ‖P z‖ ≤ (2*‖w.1.2‖+‖w.1.1.1.2.2‖)*Real.sqrt T := h.2
      _ ≤ (2*‖w‖+‖w‖)*Real.sqrt T :=
        mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left ht (by norm_num)) hH) (Real.sqrt_nonneg T)
      _ = (3*Real.sqrt T)*‖z‖ := by dsimp only [w]; rw [Submodule.norm_coe]; ring
  have hh (z : Y) (p q : Slab T) : ‖P z p-P z q‖ ≤
      ((16*T^((1-alpha)/2))*‖z‖)*PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q ^ alpha := by
    have h := PoincareConjecture.ParallelImplementation.ZeroTraceGradientHolderSmallness.zero_trace_gradient_holder_smallness T alpha hT ha ha1 z.1 (hz z) p q
    calc
      ‖P z p-P z q‖ ≤ 16*‖z.1‖*T^((1-alpha)/2)*PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q ^ alpha := h
      _ = ((16*T^((1-alpha)/2))*‖z‖)*PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q ^ alpha := by rw [Submodule.norm_coe]; ring
  have hLift :
      ∃ Q : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E6) T,
        ‖Q‖ ≤ 3*Real.sqrt T + 16*T^((1-alpha)/2) ∧
        (∀ z : Y, (Q z).1 = P z) ∧
        ∀ z : Y, Q z ∈ forcingGraph (E3 →L[ℝ] E6) T alpha :=
    PoincareConjecture.ParallelImplementation.BoundedHolderLinearLift.exists_bounded_holder_linear_lift
      (X := Y) (V := E3 →L[ℝ] E6) (T := T) (alpha := alpha)
      (M := 3*Real.sqrt T) (H := 16*T^((1-alpha)/2)) ha
      (by positivity) (by positivity) (P := P) (hbound := hb) (hholder := hh)
  obtain ⟨Q, hQ, hv, hg⟩ := hLift
  refine ⟨Q, hQ, ?_, hg⟩
  intro z p
  change (Q z).1 p = (P z) p
  rw [hv]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ZeroTraceGradientProjection
