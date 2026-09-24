import PoincareConjecture.ParallelImplementation.ZeroTraceValueSmallness
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SixComponentPositiveBall
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators RealInnerProductSpace BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Actual zero-trace metric corrections preserve uniform positivity for sufficiently small time. -/
theorem zero_trace_metric_positivity :
    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Fin 3),
        (E q v) i = ∑ j : Fin 3, symmetricSixMatrix q i j*v j) ∧
      ∀ (T alpha c M : ℝ) (hT : 0 ≤ T), 0 < c → 0 ≤ M →
        ∀ (q0 : E3 → E6),
        (∀ x v : E3, c*‖v‖^2 ≤ inner ℝ (E (q0 x) v) v) →
        ∀ z : FullJet T, z ∈ fullParabolicJetSet T alpha hT →
        ‖z‖ ≤ M → T*M ≤ c/6 → ∀ p : Slab T,
        (∀ v : E3, (c/2)*‖v‖^2 ≤
          inner ℝ (E (q0 p.2 + z.1.1.1.1 p) v) v) ∧
        ∃ e : E3 ≃L[ℝ] E3,
          e.toContinuousLinearMap = E (q0 p.2 + z.1.1.1.1 p) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ 2/c :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨E, hEinj, hEnorm, hEaction, hpositive⟩ :=
    six_component_positive_neighborhood
  refine ⟨E, hEinj, hEnorm, hEaction, ?_⟩
  intro T alpha c M hT hc hM q0 hq0 z hz hzM hTM p
  have htimeNorm : ‖z.1.2‖ ≤ ‖z‖ :=
    (norm_snd_le z.1).trans (norm_fst_le z)
  have hvalueBound :=
    (PoincareConjecture.ParallelImplementation.ZeroTraceValueSmallness.zero_trace_value_smallness
      T alpha hT z hz).2
  have hvalueSmall : ‖z.1.1.1.1 p‖ ≤ c / 6 := by
    calc
      ‖z.1.1.1.1 p‖ ≤ ‖z.1.1.1.1‖ :=
        BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ T * ‖z.1.2‖ := hvalueBound
      _ ≤ T * ‖z‖ := mul_le_mul_of_nonneg_left htimeNorm hT
      _ ≤ T * M := mul_le_mul_of_nonneg_left hzM hT
      _ ≤ c / 6 := hTM
  have hperturb := hpositive (q0 p.2) (q0 p.2 + z.1.1.1.1 p) c hc
    (hq0 p.2) (by
      rw [show q0 p.2 + z.1.1.1.1 p - q0 p.2 = z.1.1.1.1 p by abel]
      exact hvalueSmall)
  refine ⟨hperturb.1, ?_⟩
  obtain ⟨e, he, hebound⟩ := hperturb.2
  refine ⟨e, ?_, ?_⟩
  · exact he
  · exact hebound
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity
