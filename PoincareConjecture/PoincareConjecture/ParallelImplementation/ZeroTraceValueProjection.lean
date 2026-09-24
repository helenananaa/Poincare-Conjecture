import PoincareConjecture.ParallelImplementation.BoundedHolderLinearLift
import PoincareConjecture.ParallelImplementation.ZeroTraceValueHolderSmallness
import PoincareConjecture.ParallelImplementation.ParabolicIncrementBCF
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ZeroTraceValueProjection
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped Topology BoundedContinuousFunction
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance (T : ℝ) : NormedAddCommGroup (FullJet T) := inferInstance
local instance (T : ℝ) : NormedSpace ℝ (FullJet T) := inferInstance
/-- Actual zero-trace values define a small bounded linear map into the forcing Holder graph. -/
theorem exists_zero_trace_value_projection (T alpha : ℝ)
    (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha < 1)
    (Y : Submodule ℝ (FullJet T))
    (hY : (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le) :
    ∃ P : Y →L[ℝ] ForcingJet E6 T,
      ‖P‖ ≤ T + 8 * T^(1-alpha/2) ∧
      (∀ z : Y, ∀ p : Slab T, (P z).1 p = z.1.1.1.1.1 p) ∧
      ∀ z : Y, P z ∈ forcingGraph E6 T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  have hz (z : Y) : z.1 ∈ fullParabolicJetSet T alpha hT.le := by
    rw [← hY]
    exact z.2
  let P : Y →ₗ[ℝ] (Slab T →ᵇ E6) := {
    toFun := fun z => z.1.1.1.1.1
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  have hb (z : Y) : ‖P z‖ ≤ T*‖z‖ := by
    have h := PoincareConjecture.ParallelImplementation.ZeroTraceValueSmallness.zero_trace_value_smallness T alpha hT.le z.1 (hz z)
    have ht : ‖z.1.1.2‖ ≤ ‖z.1‖ := (norm_snd_le z.1.1).trans (norm_fst_le z.1)
    exact h.2.trans (mul_le_mul_of_nonneg_left ht hT.le)
  have hh (z : Y) (p q : Slab T) : ‖P z p-P z q‖ ≤
      ((8*T^(1-alpha/2))*‖z‖)*PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q ^ alpha := by
    have h := PoincareConjecture.ParallelImplementation.ZeroTraceValueHolderSmallness.zero_trace_value_holder_smallness T alpha hT ha ha1 z.1 (hz z) p q
    calc
      ‖P z p-P z q‖ ≤ 8*‖z.1‖*T^(1-alpha/2)*PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q ^ alpha := h
      _ = ((8*T^(1-alpha/2))*‖z‖)*PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet.parabolicRho p q ^ alpha := by rw [Submodule.norm_coe]; ring
  obtain ⟨Q, hQ, hv, hg⟩ :=
    PoincareConjecture.ParallelImplementation.BoundedHolderLinearLift.exists_bounded_holder_linear_lift T alpha T (8*T^(1-alpha/2)) ha hT.le (by positivity) P hb hh
  refine ⟨Q, hQ, ?_, hg⟩
  intro z p
  change (Q z).1 p = (P z) p
  rw [hv]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ZeroTraceValueProjection
