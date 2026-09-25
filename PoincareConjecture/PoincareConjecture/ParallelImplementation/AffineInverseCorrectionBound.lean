import PoincareConjecture.ParallelImplementation.AffineForcingGraphInverse
import PoincareConjecture.ParallelImplementation.ForcingGraphNearIdentityInverse
import PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.AffineInverseCorrectionBound
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
theorem exists_affine_inverse_correction_bound
    {Y A : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedRing A] [NormedAlgebra ℝ A] [NormOneClass A] [CompleteSpace A]
    (T alpha R : ℝ) (hR : 0 < R)
    (a : ForcingJet A T) (ha : a ∈ forcingGraph A T alpha)
    (P : Y →L[ℝ] ForcingJet A T) (hP : ∀ z, P z ∈ forcingGraph A T alpha)
    (hsmall : ‖a‖+‖P‖*R ≤ 1/2) :
    let oneJet : ForcingJet A T := ((1 : Slab T →ᵇ A), (0 : Pair T →ᵇ A))
    ∃ I : Y → ForcingJet A T,
      (∀ z, ‖z‖ ≤ R → I z ∈ forcingGraph A T alpha ∧ ‖I z‖ ≤ 2 ∧
        (∀ p : Slab T, (1-(a+P z).1 p)*(I z).1 p=1 ∧
          (I z).1 p*(1-(a+P z).1 p)=1) ∧
        ‖I z-oneJet‖ ≤ 4*‖a+P z‖) ∧
      ‖I 0-oneJet‖ ≤ 4*‖a‖ ∧
      ∀ z w, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖I z-I w‖ ≤ (12*‖P‖)*‖z-w‖ :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let oneJet : ForcingJet A T :=
    ((1 : Slab T →ᵇ A), (0 : Pair T →ᵇ A))
  obtain ⟨I, hI, hIzero, hIlip⟩ :=
    PoincareConjecture.ParallelImplementation.AffineForcingGraphInverse.exists_affine_forcing_graph_inverse
      T alpha R hR a ha P hP hsmall
  have hAffineGraph (z : Y) : a + P z ∈ forcingGraph A T alpha := by
    intro p
    change a.2 p + (P z).2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (a.1 p.1.1 + (P z).1 p.1.1 - (a.1 p.1.2 + (P z).1 p.1.2))
    rw [ha p, hP z p]
    simp [sub_eq_add_neg, smul_add]
    abel
  have hAffineNorm (z : Y) (hz : ‖z‖ ≤ R) : ‖a + P z‖ ≤ 1 / 2 := by
    calc
      ‖a + P z‖ ≤ ‖a‖ + ‖P z‖ := norm_add_le _ _
      _ ≤ ‖P‖ * ‖z‖ + ‖a‖ := by
        calc
          ‖a‖ + ‖P z‖ = ‖P z‖ + ‖a‖ := by ring
          _ ≤ ‖P‖ * ‖z‖ + ‖a‖ := add_le_add_left (P.le_opNorm z) ‖a‖
      _ = ‖a‖ + ‖P‖ * ‖z‖ := by ring
      _ ≤ ‖P‖ * R + ‖a‖ := by
        calc
          ‖a‖ + ‖P‖ * ‖z‖ = ‖P‖ * ‖z‖ + ‖a‖ := by ring
          _ ≤ ‖P‖ * R + ‖a‖ :=
            add_le_add_left (mul_le_mul_of_nonneg_left hz (norm_nonneg P)) ‖a‖
      _ = ‖a‖ + ‖P‖ * R := by ring
      _ ≤ 1 / 2 := hsmall
  have hCorrection (z : Y) (hz : ‖z‖ ≤ R) :
      ‖I z - oneJet‖ ≤ 4 * ‖a + P z‖ := by
    have hxValue : ‖(a + P z).1‖ ≤ (1 / 2 : ℝ) :=
      (norm_fst_le (a + P z)).trans (hAffineNorm z hz)
    obtain ⟨b, hbGraph, hbInv, hbIncrement, hbValueNorm, hbSecondNorm, hbNorm⟩ :=
      PoincareConjecture.ParallelImplementation.ForcingGraphNearIdentityInverse.exists_forcing_graph_near_identity_inverse
        T alpha (1 / 2) (by norm_num) (by norm_num) (a + P z)
        (hAffineGraph z) hxValue
    have hbValueNorm' : ‖b.1‖ ≤ 2 := by
      simpa only [show (1 / (1 - (1 / 2 : ℝ)) : ℝ) = 2 by norm_num] using
        hbValueNorm
    have hValues (p : Slab T) : (I z).1 p = b.1 p := by
      calc
        (I z).1 p = (I z).1 p * ((1 - (a + P z).1 p) * b.1 p) := by
          rw [(hbInv p).1, mul_one]
        _ = ((I z).1 p * (1 - (a + P z).1 p)) * b.1 p := by
          rw [mul_assoc]
        _ = b.1 p := by
          rw [((hI z hz).2.2 p).2, one_mul]
    have hEq : I z = b :=
      PoincareConjecture.ParallelImplementation.ForcingGraphValueExtensionality.forcing_jet_eq_of_value_eq
        T alpha (I z) b (hI z hz).1 hbGraph hValues
    have hfirst :
        ‖b.1 - (BoundedContinuousFunction.const (Slab T) 1)‖ ≤
          2 * ‖(a + P z).1‖ := by
      apply (BoundedContinuousFunction.norm_le
        (mul_nonneg (by norm_num) (norm_nonneg _))).2
      intro p
      rw [BoundedContinuousFunction.sub_apply,
        BoundedContinuousFunction.const_apply]
      have hvalue : b.1 p - 1 = (a + P z).1 p * b.1 p := by
        calc
          b.1 p - 1 = b.1 p - (1 - (a + P z).1 p) * b.1 p := by
            rw [(hbInv p).1]
          _ = (a + P z).1 p * b.1 p := by noncomm_ring
      rw [hvalue]
      calc
        ‖(a + P z).1 p * b.1 p‖ ≤ ‖(a + P z).1 p‖ * ‖b.1 p‖ :=
          norm_mul_le _ _
        _ ≤ ‖(a + P z).1 p‖ * 2 :=
          mul_le_mul_of_nonneg_left
            ((b.1.norm_coe_le_norm p).trans hbValueNorm') (norm_nonneg _)
        _ ≤ ‖(a + P z).1‖ * 2 :=
          mul_le_mul_of_nonneg_right ((a + P z).1.norm_coe_le_norm p) (by norm_num)
        _ = 2 * ‖(a + P z).1‖ := by ring
    have hsecond : ‖b.2‖ ≤ 4 * ‖(a + P z).2‖ := by
      apply (BoundedContinuousFunction.norm_le
        (mul_nonneg (by norm_num) (norm_nonneg _))).2
      intro p
      rw [hbIncrement p]
      calc
        ‖b.1 p.1.1 * (a + P z).2 p * b.1 p.1.2‖ ≤
            ‖b.1 p.1.1 * (a + P z).2 p‖ * ‖b.1 p.1.2‖ := norm_mul_le _ _
        _ ≤ (‖b.1 p.1.1‖ * ‖(a + P z).2 p‖) * ‖b.1 p.1.2‖ := by
          exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ (2 * ‖(a + P z).2 p‖) * 2 := by
          apply mul_le_mul
          · exact mul_le_mul
              ((b.1.norm_coe_le_norm p.1.1).trans hbValueNorm')
              le_rfl
              (norm_nonneg _)
              (by norm_num)
          · exact (b.1.norm_coe_le_norm p.1.2).trans hbValueNorm'
          · exact norm_nonneg _
          · exact mul_nonneg (by norm_num) (norm_nonneg _)
        _ = 4 * ‖(a + P z).2 p‖ := by ring
        _ ≤ 4 * ‖(a + P z).2‖ :=
          mul_le_mul_of_nonneg_left ((a + P z).2.norm_coe_le_norm p) (by norm_num)
    rw [hEq, Prod.norm_def]
    simp only [oneJet, Prod.fst_sub, Prod.snd_sub, sub_zero]
    apply max_le
    · calc
        ‖b.1 - (1 : Slab T →ᵇ A)‖ ≤ 2 * ‖(a + P z).1‖ := by
          change ‖b.1 - BoundedContinuousFunction.const (Slab T) 1‖ ≤ _
          exact hfirst
        _ ≤ 2 * ‖a + P z‖ :=
          mul_le_mul_of_nonneg_left (norm_fst_le (a + P z)) (by norm_num)
        _ ≤ 4 * ‖a + P z‖ := by nlinarith [norm_nonneg (a + P z)]
    · calc
        ‖b.2‖ ≤ 4 * ‖(a + P z).2‖ := hsecond
        _ ≤ 4 * ‖a + P z‖ :=
          mul_le_mul_of_nonneg_left (norm_snd_le (a + P z)) (by norm_num)
  refine ⟨I, ?_, ?_, hIlip⟩
  · intro z hz
    rcases hI z hz with ⟨hgraph, hnorm, hinv⟩
    exact ⟨hgraph, hnorm, hinv, hCorrection z hz⟩
  · have hzeroBall : ‖(0 : Y)‖ ≤ R := by
      simpa using hR.le
    simpa [P.map_zero] using hCorrection 0 hzeroBall
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.AffineInverseCorrectionBound
