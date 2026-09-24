import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetHeatOperator
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- The genuine heat residual, together with its normalized increments, is bounded linear. -/
theorem exists_full_jet_heat_operator (T alpha : ℝ) (hT : 0 ≤ T) :
    ∃ L : FullJet T →L[ℝ] ForcingJet E6 T, ‖L‖ ≤ 4 ∧
      (∀ z p, (L z).1 p = z.1.2 p - ∑ i : Fin 3,
        z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) ∧
      (∀ z p, (L z).2 p = z.2 p - ∑ i : Fin 3,
        z.1.1.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) ∧
      ∀ z ∈ fullParabolicJetSet T alpha hT, L z ∈ forcingGraph E6 T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  let e (i : Fin 3) : E3 := EuclideanSpace.single i 1
  let tr : (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6 :=
    ∑ i : Fin 3, (ContinuousLinearMap.apply ℝ E6 (e i)).comp
      (ContinuousLinearMap.apply ℝ (E3 →L[ℝ] E6) (e i))
  have htr (H : E3 →L[ℝ] E3 →L[ℝ] E6) : ‖tr H‖ ≤ 3 * ‖H‖ := by
    change ‖∑ i : Fin 3, H (e i) (e i)‖ ≤ _
    calc
      _ ≤ ∑ i : Fin 3, ‖H (e i) (e i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 3, ‖H‖ := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          ‖H (e i) (e i)‖ ≤ ‖H (e i)‖ * ‖e i‖ := (H (e i)).le_opNorm _
          _ ≤ (‖H‖ * ‖e i‖) * ‖e i‖ :=
            mul_le_mul_of_nonneg_right (H.le_opNorm _) (norm_nonneg _)
          _ = ‖H‖ := by simp [e]
      _ = _ := by simp
  let trS := tr.compLeftContinuousBounded (Slab T)
  let trP := tr.compLeftContinuousBounded (Pair T)
  have htrS (H : Slab T →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6)) : ‖trS H‖ ≤ 3 * ‖H‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro p
    exact (htr (H p)).trans (mul_le_mul_of_nonneg_left (H.norm_coe_le_norm p) (by norm_num))
  have htrP (H : Pair T →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6)) : ‖trP H‖ ≤ 3 * ‖H‖ := by
    apply (BoundedContinuousFunction.norm_le (by positivity)).2
    intro p
    exact (htr (H p)).trans (mul_le_mul_of_nonneg_left (H.norm_coe_le_norm p) (by norm_num))
  let L0 : FullJet T →ₗ[ℝ] ForcingJet E6 T := {
    toFun := fun z => (z.1.2 - trS z.1.1.1.2.2, z.2 - trP z.1.1.2)
    map_add' := by
      intro z w
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add] <;> abel
    map_smul' := by
      intro c z
      apply Prod.ext
      · change c • z.1.2 - trS (c • z.1.1.1.2.2) = c • (z.1.2 - trS z.1.1.1.2.2)
        rw [map_smul, smul_sub]
      · change c • z.2 - trP (c • z.1.1.2) = c • (z.2 - trP z.1.1.2)
        rw [map_smul, smul_sub]
  }
  have hbound (z : FullJet T) : ‖L0 z‖ ≤ 4 * ‖z‖ := by
    have htime : ‖z.1.2‖ ≤ ‖z‖ := (norm_snd_le z.1).trans (norm_fst_le z)
    have hinc : ‖z.2‖ ≤ ‖z‖ := norm_snd_le z
    have hhi : ‖z.1.1.2‖ ≤ ‖z‖ :=
      (norm_snd_le z.1.1).trans ((norm_fst_le z.1).trans (norm_fst_le z))
    have hh : ‖z.1.1.1.2.2‖ ≤ ‖z‖ :=
      (norm_snd_le z.1.1.1.2).trans ((norm_snd_le z.1.1.1).trans
        ((norm_fst_le z.1.1).trans ((norm_fst_le z.1).trans (norm_fst_le z))))
    change max ‖z.1.2 - trS z.1.1.1.2.2‖ ‖z.2 - trP z.1.1.2‖ ≤ _
    apply max_le
    · calc
        _ ≤ ‖z.1.2‖ + ‖trS z.1.1.1.2.2‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + 3 * ‖z‖ := add_le_add htime
          ((htrS _).trans (mul_le_mul_of_nonneg_left hh (by norm_num)))
        _ = _ := by ring
    · calc
        _ ≤ ‖z.2‖ + ‖trP z.1.1.2‖ := norm_sub_le _ _
        _ ≤ ‖z‖ + 3 * ‖z‖ := add_le_add hinc
          ((htrP _).trans (mul_le_mul_of_nonneg_left hhi (by norm_num)))
        _ = _ := by ring
  let L : FullJet T →L[ℝ] ForcingJet E6 T := L0.mkContinuous 4 hbound
  refine ⟨L, LinearMap.mkContinuous_norm_le _ (by norm_num) hbound, ?_, ?_, ?_⟩
  · intro z p
    rfl
  · intro z p
    rfl
  · intro z hz p
    have ht := hz.2.2.1 p
    have hh := hz.1.2 p
    change z.2 p - tr (z.1.1.2 p) =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((z.1.2 p.1.1 - tr (z.1.1.1.2.2 p.1.1)) -
          (z.1.2 p.1.2 - tr (z.1.1.1.2.2 p.1.2)))
    rw [ht, hh, map_smul, map_sub]
    simp only [smul_sub]
    abel
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetHeatOperator
