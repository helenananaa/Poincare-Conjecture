import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetHessianComponent
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BoundedContinuousFunction
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Each unit-coordinate Hessian component is a norm-one map into the Holder forcing graph. -/
theorem exists_full_jet_hessian_component (T alpha : ℝ) (hT : 0 ≤ T) (i j : Fin 3) :
    ∃ H : FullJet T →L[ℝ] ForcingJet E6 T, ‖H‖ ≤ 1 ∧
      (∀ z p, (H z).1 p = z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      (∀ z p, (H z).2 p = z.1.1.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ z ∈ fullParabolicJetSet T alpha hT, H z ∈ forcingGraph E6 T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  let e (k : Fin 3) : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single k 1
  let evalLeft : (EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] E6) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] E6 :=
    ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ] E6) (e i)
  let evalRight : (EuclideanSpace ℝ (Fin 3) →L[ℝ] E6) →L[ℝ] E6 :=
    ContinuousLinearMap.apply ℝ E6 (e j)
  let eval : (EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] E6) →L[ℝ] E6 := evalRight.comp evalLeft
  have heval (H : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] E6) : ‖eval H‖ ≤ ‖H‖ := by
    change ‖H (e i) (e j)‖ ≤ ‖H‖
    calc
      ‖H (e i) (e j)‖ ≤ ‖H (e i)‖ * ‖e j‖ := (H (e i)).le_opNorm _
      _ ≤ (‖H‖ * ‖e i‖) * ‖e j‖ :=
        mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
      _ = ‖H‖ := by simp [e]
  have hevalNorm : ‖eval‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro H
    simpa only [one_mul] using heval H
  let evalSlab := eval.compLeftContinuousBounded (Slab T)
  let evalPair := eval.compLeftContinuousBounded (Pair T)
  have hevalSlab (H : Slab T →ᵇ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] E6)) :
      ‖evalSlab H‖ ≤ ‖H‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    intro p
    change ‖eval (H p)‖ ≤ ‖H‖
    exact (heval (H p)).trans (H.norm_coe_le_norm p)
  have hevalPair (H : Pair T →ᵇ
      (EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] E6)) :
      ‖evalPair H‖ ≤ ‖H‖ := by
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
    intro p
    change ‖eval (H p)‖ ≤ ‖H‖
    exact (heval (H p)).trans (H.norm_coe_le_norm p)
  let L0 : FullJet T →ₗ[ℝ] ForcingJet E6 T := {
    toFun := fun z => (evalSlab z.1.1.1.2.2, evalPair z.1.1.2)
    map_add' := by
      intro z w
      apply Prod.ext <;> simp [evalSlab, evalPair]
    map_smul' := by
      intro c z
      apply Prod.ext <;> simp [evalSlab, evalPair]
  }
  have hbound (z : FullJet T) : ‖L0 z‖ ≤ 1 * ‖z‖ := by
    have hfirst : ‖z.1.1.1.2.2‖ ≤ ‖z‖ :=
      (norm_snd_le z.1.1.1.2).trans ((norm_snd_le z.1.1.1).trans
        ((norm_fst_le z.1.1).trans ((norm_fst_le z.1).trans (norm_fst_le z))))
    have hsecond : ‖z.1.1.2‖ ≤ ‖z‖ :=
      (norm_snd_le z.1.1).trans ((norm_fst_le z.1).trans (norm_fst_le z))
    change max ‖evalSlab z.1.1.1.2.2‖ ‖evalPair z.1.1.2‖ ≤ 1 * ‖z‖
    apply max_le
    · simpa only [one_mul] using (hevalSlab _).trans hfirst
    · simpa only [one_mul] using (hevalPair _).trans hsecond
  let L : FullJet T →L[ℝ] ForcingJet E6 T := L0.mkContinuous 1 hbound
  refine ⟨L, LinearMap.mkContinuous_norm_le _ (by norm_num) hbound, ?_, ?_, ?_⟩
  · intro z p
    rfl
  · intro z p
    rfl
  · intro z hz p
    have hh := hz.1.2 p
    have heq := congrArg eval hh
    rw [map_smul, map_sub] at heq
    change eval (z.1.1.2 p) =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (eval (z.1.1.1.2.2 p.1.1) - eval (z.1.1.1.2.2 p.1.2))
    exact heq
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetHessianComponent
