import PoincareConjecture.ParallelImplementation.FullJetHessianProjection
import PoincareConjecture.ParallelImplementation.ZeroTraceValueProjection
import PoincareConjecture.ParallelImplementation.MixedProjectedForcingBilinear
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ZeroTraceValueHessianNonlinearity
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_zero_trace_value_hessian_nonlinearity
    (T alpha : ℝ) (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha < 1)
    (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T))
    (hX : (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha)
    (hY : (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le)
    (B : E6 →L[ℝ] (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6) :
    ∃ N : Y → X, N 0 = 0 ∧
      (∀ z : Y, ∀ p : Slab T,
        (N z).1.1 p = B (z.1.1.1.1.1 p) (z.1.1.1.1.2.2 p)) ∧
      (∀ z w : Y, ‖N z-N w‖ ≤
        (2*‖B‖*(T+8*T^(1-alpha/2)))*(‖z‖+‖w‖)*‖z-w‖) :=
/- SWARM_PROOF_BEGIN -/
by
  letI : NormedAddCommGroup Y := inferInstance
  obtain ⟨P, hPbound, hPvalue, hPgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceValueProjection.exists_zero_trace_value_projection T alpha hT ha ha1 Y hY
  obtain ⟨H, hHbound, hHvalue, _, hHgraph⟩ :=
    PoincareConjecture.ParallelImplementation.FullJetHessianProjection.exists_full_jet_hessian_projection T alpha hT.le
  let i : Y →L[ℝ] FullJet T := Y.subtypeL
  let Q : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T := H.comp i
  have hQbound : ‖Q‖ ≤ 1 := by
    have hsub : ‖i‖ ≤ 1 := Submodule.norm_subtypeL_le Y
    calc
      ‖Q‖ ≤ ‖H‖ * ‖i‖ := H.opNorm_comp_le i
      _ ≤ 1 * 1 := mul_le_mul hHbound hsub (norm_nonneg i) (by norm_num)
      _ = 1 := one_mul 1
  have hzY (z : Y) : z.1 ∈ fullParabolicJetSet T alpha hT.le := by
    rw [← hY]
    exact z.2
  have hQgraph (z : Y) : Q z ∈ forcingGraph (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha := by
    change H z.1 ∈ forcingGraph (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha
    exact hHgraph z.1 (hzY z)
  obtain ⟨N, hNzero, hNvalue, hNlip⟩ :=
    PoincareConjecture.ParallelImplementation.MixedProjectedForcingBilinear.exists_mixed_projected_forcing_bilinear
      (Y := Y) (V := E6) (W := E3 →L[ℝ] E3 →L[ℝ] E6) (Z := E6)
      T alpha B X hX P Q hPgraph hQgraph
  have hcoeff : 2*‖B‖*‖P‖*‖Q‖ ≤ 2*‖B‖*(T+8*T^(1-alpha/2)) := by
    calc
      2*‖B‖*‖P‖*‖Q‖ = (2*‖B‖*‖P‖)*‖Q‖ := by ring
      _ ≤ (2*‖B‖*‖P‖)*1 :=
        mul_le_mul_of_nonneg_left hQbound
          (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg B)) (norm_nonneg P))
      _ = (2*‖B‖)*‖P‖ := by ring
      _ ≤ (2*‖B‖)*(T+8*T^(1-alpha/2)) :=
        mul_le_mul_of_nonneg_left hPbound
          (mul_nonneg (by norm_num) (norm_nonneg B))
  refine ⟨N, hNzero, ?_, ?_⟩
  · intro z p
    exact (hNvalue z p).trans
      (congrArg₂ (fun v h => B v h) (hPvalue z p) (hHvalue z.1 p))
  · intro z w
    exact (hNlip z w).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (add_nonneg (norm_nonneg z) (norm_nonneg w)))
        (norm_nonneg (z-w)))
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ZeroTraceValueHessianNonlinearity
