import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_forcing_graph_linear_lift
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (A : V →L[ℝ] W) (T alpha : ℝ) :
    ∃ L : ForcingJet V T →L[ℝ] ForcingJet W T,
      ‖L‖ ≤ ‖A‖ ∧ (∀ f p, (L f).1 p = A (f.1 p)) ∧
      (∀ f p, (L f).2 p = A (f.2 p)) ∧
      ∀ f ∈ forcingGraph V T alpha, L f ∈ forcingGraph W T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  let value := A.compLeftContinuousBounded (Slab T)
  let increment := A.compLeftContinuousBounded (Pair T)
  have hvalue (f : Slab T →ᵇ V) :
      ‖value f‖ ≤ ‖A‖ * ‖f‖ := by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    intro p
    change ‖A (f p)‖ ≤ ‖A‖ * ‖f‖
    exact (A.le_opNorm (f p)).trans
      (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm p) (norm_nonneg _))
  have hincrement (f : Pair T →ᵇ V) :
      ‖increment f‖ ≤ ‖A‖ * ‖f‖ := by
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2
    intro p
    change ‖A (f p)‖ ≤ ‖A‖ * ‖f‖
    exact (A.le_opNorm (f p)).trans
      (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm p) (norm_nonneg _))
  let L0 : ForcingJet V T →ₗ[ℝ] ForcingJet W T := {
    toFun := fun f => (value f.1, increment f.2)
    map_add' := by
      intro f g
      apply Prod.ext <;> simp [value, increment]
    map_smul' := by
      intro c f
      apply Prod.ext <;> simp [value, increment]
  }
  have hbound (f : ForcingJet V T) : ‖L0 f‖ ≤ ‖A‖ * ‖f‖ := by
    change max ‖value f.1‖ ‖increment f.2‖ ≤ ‖A‖ * max ‖f.1‖ ‖f.2‖
    apply max_le
    · exact (hvalue f.1).trans
        (mul_le_mul_of_nonneg_left (norm_fst_le f) (norm_nonneg _))
    · exact (hincrement f.2).trans
        (mul_le_mul_of_nonneg_left (norm_snd_le f) (norm_nonneg _))
  let L : ForcingJet V T →L[ℝ] ForcingJet W T := L0.mkContinuous ‖A‖ hbound
  refine ⟨L, LinearMap.mkContinuous_norm_le _ (norm_nonneg _) hbound, ?_, ?_, ?_⟩
  · intro f p
    rfl
  · intro f p
    rfl
  · intro f hf p
    have h := hf p
    change A (f.2 p) =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (A (f.1 p.1.1) - A (f.1 p.1.2))
    rw [h, map_smul, map_sub]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingGraphLinearLift
