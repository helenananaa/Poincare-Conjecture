import PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift
import PoincareConjecture.ParallelImplementation.ZeroTraceValueProjection
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ZeroTraceOperatorValueProjection
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance (T : ℝ) : NormedAddCommGroup (FullJet T) := inferInstance
local instance (T : ℝ) : NormedSpace ℝ (FullJet T) := inferInstance
local instance (T : ℝ) : NormedAddCommGroup (ForcingJet (E3 →L[ℝ] E3) T) := inferInstance
local instance (T : ℝ) : NormedSpace ℝ (ForcingJet (E3 →L[ℝ] E3) T) := inferInstance
local instance (T : ℝ) (Y : Submodule ℝ (FullJet T)) : NormedAddCommGroup Y := inferInstance
local instance (T : ℝ) (Y : Submodule ℝ (FullJet T)) : NormedSpace ℝ Y := inferInstance
theorem exists_zero_trace_operator_value_projection
    (T alpha : ℝ) (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha < 1)
    (Y : Submodule ℝ (FullJet T))
    (hY : (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le)
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) :
    ∃ P : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E3) T,
      ‖P‖ ≤ ‖E‖*(T+8*T^(1-alpha/2)) ∧
      (∀ z : Y, ∀ p : Slab T, (P z).1 p = -E (z.1.1.1.1.1 p)) ∧
      ∀ z : Y, P z ∈ forcingGraph (E3 →L[ℝ] E3) T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨P, hP, hPv, hPg⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceValueProjection.exists_zero_trace_value_projection
      T alpha hT ha ha1 Y hY
  obtain ⟨L, hL, hLv, hLi, hLg⟩ :=
    PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift.exists_forcing_graph_linear_lift
      (-E) T alpha
  refine ⟨L.comp P, ?_, ?_, ?_⟩
  · calc
      ‖L.comp P‖ ≤ ‖L‖ * ‖P‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖E‖ * (T + 8 * T^(1-alpha/2)) := by
        have hL' : ‖L‖ ≤ ‖E‖ := hL.trans_eq (norm_neg E)
        exact mul_le_mul hL' hP (norm_nonneg P) (norm_nonneg E)
  · intro z p
    change (L (P z)).1 p = -E ((z : FullJet T).1.1.1.1 p)
    rw [hLv, hPv]
    simp
  · intro z
    exact hLg (P z) (hPg z)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ZeroTraceOperatorValueProjection
