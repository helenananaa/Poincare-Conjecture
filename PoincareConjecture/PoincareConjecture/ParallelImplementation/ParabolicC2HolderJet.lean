import PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped Topology ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
abbrev Pair (T : ℝ) := {p : Slab T × Slab T // p.1 ≠ p.2}
def parabolicRho {T : ℝ} (p q : Slab T) : ℝ :=
  ‖p.2-q.2‖ + Real.sqrt |(p.1 : ℝ)-(q.1 : ℝ)|
abbrev HolderJet (T : ℝ) := Jet T × (Pair T →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6))
def parabolicC2HolderSet (T alpha : ℝ) : Set (HolderJet T) :=
  {z | z.1 ∈ spaceTimeC2JetSet T ∧ ∀ p : Pair T,
    z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
      (z.1.2.2 p.1.1 - z.1.2.2 p.1.2)}
/-- Actual spatial jets with bounded normalized parabolic Hessian increments form a complete set. -/
theorem parabolic_C2_holder_jet_complete (T alpha : ℝ) (ha : 0 < alpha) :
    IsComplete (parabolicC2HolderSet T alpha) ∧
      ∀ z ∈ parabolicC2HolderSet T alpha, ∀ p q : Slab T,
        ‖z.1.2.2 p-z.1.2.2 q‖ ≤ ‖z.2‖ * parabolicRho p q ^ alpha :=
/- SWARM_PROOF_BEGIN -/
by
  let hessEval (x : Slab T) : HolderJet T → (E3 →L[ℝ] E3 →L[ℝ] E6) :=
    fun z => z.1.2.2 x
  have hessEval_cont (x : Slab T) : Continuous (hessEval x) := by
    dsimp [hessEval]
    exact (ContinuousEvalConst.continuous_eval_const x).comp
      (continuous_snd.comp (continuous_snd.comp continuous_fst))
  have baseClosed : IsClosed (spaceTimeC2JetSet T) := by
    exact (spaceTime_C2_jet_complete T).1.isClosed
  have graphClosed (p : Pair T) : IsClosed {z : HolderJet T |
      z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (z.1.2.2 p.1.1 - z.1.2.2 p.1.2)} := by
    apply isClosed_eq
    · exact (ContinuousEvalConst.continuous_eval_const p).comp continuous_snd
    · exact ((hessEval_cont p.1.1).sub (hessEval_cont p.1.2)).const_smul
        ((parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹)
  have holderClosed : IsClosed (parabolicC2HolderSet T alpha) := by
    have heq : parabolicC2HolderSet T alpha =
        (fun z : HolderJet T => z.1) ⁻¹' spaceTimeC2JetSet T ∩
          ⋂ p : Pair T, {z : HolderJet T |
            z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
              (z.1.2.2 p.1.1 - z.1.2.2 p.1.2)} := by
      ext z
      simp [parabolicC2HolderSet]
    rw [heq]
    exact (baseClosed.preimage continuous_fst).inter
      (isClosed_iInter graphClosed)
  haveI : CompleteSpace (E3 →L[ℝ] E6) :=
    (SeparatingDual.completeSpace_continuousLinearMap_iff ℝ E3 E6).2 inferInstance
  haveI : CompleteSpace (E3 →L[ℝ] E3 →L[ℝ] E6) :=
    (SeparatingDual.completeSpace_continuousLinearMap_iff ℝ E3
      (E3 →L[ℝ] E6)).2 inferInstance
  haveI : CompleteSpace (HolderJet T) := by infer_instance
  refine ⟨holderClosed.isComplete, ?_⟩
  intro z hz p q
  by_cases hpq : p = q
  · subst q
    simp [parabolicRho, ha.ne']
  · let pq : Pair T := ⟨(p, q), hpq⟩
    have htimeOrSpace : (p.1 : ℝ) ≠ (q.1 : ℝ) ∨ p.2 ≠ q.2 := by
      by_contra h
      push Not at h
      apply hpq
      apply Prod.ext
      · exact Subtype.ext h.1
      · exact h.2
    have hrho : 0 < parabolicRho p q := by
      unfold parabolicRho
      rcases htimeOrSpace with ht | hx
      · exact add_pos_of_nonneg_of_pos (norm_nonneg _) <| Real.sqrt_pos.2 <|
          abs_pos.mpr (sub_ne_zero.mpr ht)
      · exact add_pos_of_pos_of_nonneg
          (norm_pos_iff.mpr (sub_ne_zero.mpr hx)) (Real.sqrt_nonneg _)
    have haRho : 0 < parabolicRho p q ^ alpha := Real.rpow_pos_of_pos hrho alpha
    have hrel := hz.2 pq
    have hdiff : z.1.2.2 p - z.1.2.2 q =
        parabolicRho p q ^ alpha • z.2 pq := by
      calc
        z.1.2.2 p - z.1.2.2 q =
            parabolicRho p q ^ alpha •
              ((parabolicRho p q ^ alpha)⁻¹ •
                (z.1.2.2 p - z.1.2.2 q)) := by
          rw [smul_smul, mul_inv_cancel₀ haRho.ne', one_smul]
        _ = parabolicRho p q ^ alpha • z.2 pq := by
          rw [← hrel]
    calc
      ‖z.1.2.2 p - z.1.2.2 q‖ =
          parabolicRho p q ^ alpha * ‖z.2 pq‖ := by
            rw [hdiff, norm_smul, Real.norm_of_nonneg haRho.le]
      _ ≤ parabolicRho p q ^ alpha * ‖z.2‖ :=
        mul_le_mul_of_nonneg_left (z.2.norm_coe_le_norm pq) haRho.le
      _ = ‖z.2‖ * parabolicRho p q ^ alpha := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
