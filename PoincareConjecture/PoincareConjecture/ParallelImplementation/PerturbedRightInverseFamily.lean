import PoincareConjecture.ParallelImplementation.UniformNearIdentityInverse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.PerturbedRightInverseFamily
theorem exists_lipschitz_perturbed_right_inverse_family
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : Y →L[ℝ] X) (D : X →L[ℝ] Y)
    (hLD : L.comp D = ContinuousLinearMap.id ℝ X)
    (q : ℝ) (hq0 : 0 ≤ q) (hq : q < 1) :
    ∃ E : (Y →L[ℝ] X) → (X →L[ℝ] Y),
      (∀ R, ‖R.comp D‖ ≤ q →
        (L-R).comp (E R) = ContinuousLinearMap.id ℝ X ∧ ‖E R‖ ≤ ‖D‖/(1-q)) ∧
      (∀ R S, ‖R.comp D‖ ≤ q → ‖S.comp D‖ ≤ q →
        ‖E R-E S‖ ≤ (‖D‖^2/(1-q)^2)*‖R-S‖) :=
/- SWARM_PROOF_BEGIN -/
by
  by_cases hX : Nontrivial X
  · letI : NontrivialTopology X :=
      nontrivialTopology_iff_exists_norm_ne_zero.mpr (by
        obtain ⟨x, hx⟩ := exists_ne (0 : X)
        exact ⟨x, ne_of_gt (norm_pos_iff.mpr hx)⟩)
    let P := {R : Y →L[ℝ] X // ‖R.comp D‖ ≤ q}
    let a : P → (X →L[ℝ] X) := fun p => p.1.comp D
    obtain ⟨b, hbInv, hbBound, hbResolvent, hbLip⟩ :=
      PoincareConjecture.ParallelImplementation.UniformNearIdentityInverse.exists_uniform_near_identity_inverse
        (A := X →L[ℝ] X) (P := P) a q hq0 hq (by
          intro p
          exact p.2)
    let E : (Y →L[ℝ] X) → (X →L[ℝ] Y) := fun R =>
      if hR : ‖R.comp D‖ ≤ q then D.comp (b ⟨R, hR⟩) else 0
    have hone : (1 : X →L[ℝ] X) = ContinuousLinearMap.id ℝ X := by
      ext x
      rfl
    have hbase (p : P) : (L - p.1).comp D =
        ContinuousLinearMap.id ℝ X - a p := by
      ext x
      simp only [ContinuousLinearMap.comp_apply, sub_apply,
        ContinuousLinearMap.id_apply, a]
      have hx : L (D x) = x := by
        simpa using congrArg (fun f : X →L[ℝ] X => f x) hLD
      rw [hx]
    have hleft (p : P) :
        (ContinuousLinearMap.id ℝ X - a p).comp (b p) =
          ContinuousLinearMap.id ℝ X := by
      have hU : (1 - a p) = ContinuousLinearMap.id ℝ X - a p := by
        rw [hone]
      rw [← hU, ← ContinuousLinearMap.mul_def]
      rw [← hone]
      exact (hbInv p).1
    refine ⟨E, ?_, ?_⟩
    · intro R hR
      let p : P := ⟨R, hR⟩
      have hER : E R = D.comp (b p) := by
        simp [E, p, hR]
      have hbaseR : (L - R).comp D =
          ContinuousLinearMap.id ℝ X - a p := by
        simpa [p] using hbase p
      refine ⟨?_, ?_⟩
      · calc
          (L - R).comp (E R) = ((L - R).comp D).comp (b p) := by
            simp only [hER, ← ContinuousLinearMap.comp_assoc]
          _ = (ContinuousLinearMap.id ℝ X - a p).comp (b p) := by
            rw [hbaseR]
          _ = ContinuousLinearMap.id ℝ X := hleft p
      · calc
          ‖E R‖ = ‖D.comp (b p)‖ := by rw [hER]
          _ ≤ ‖D‖ * ‖b p‖ := D.opNorm_comp_le _
          _ ≤ ‖D‖ * (1 / (1 - q)) :=
            mul_le_mul_of_nonneg_left (hbBound p) (norm_nonneg D)
          _ = ‖D‖ / (1 - q) := by ring
    · intro R S hR hS
      let p : P := ⟨R, hR⟩
      let s : P := ⟨S, hS⟩
      have hER : E R = D.comp (b p) := by simp [E, p, hR]
      have hES : E S = D.comp (b s) := by simp [E, s, hS]
      have haDiff : a p - a s = (R - S).comp D := by
        ext x
        simp [a, p, s, ContinuousLinearMap.comp_apply]
      have haBound : ‖a p - a s‖ ≤ ‖R - S‖ * ‖D‖ := by
        rw [haDiff]
        exact (R - S).opNorm_comp_le D
      have hbDiffNorm : ‖b p - b s‖ ≤
          (1 / (1 - q)) ^ 2 * ‖a p - a s‖ := by
        rw [hbResolvent p s]
        calc
          ‖b p * (a p - a s) * b s‖ ≤
              (‖b p‖ * ‖a p - a s‖) * ‖b s‖ := by
            calc
              ‖b p * (a p - a s) * b s‖ ≤
                  ‖b p * (a p - a s)‖ * ‖b s‖ := norm_mul_le _ _
              _ ≤ (‖b p‖ * ‖a p - a s‖) * ‖b s‖ :=
                mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
          _ ≤ (1 / (1 - q)) * ‖a p - a s‖ * (1 / (1 - q)) := by
            gcongr <;> exact hbBound _
          _ = (1 / (1 - q)) ^ 2 * ‖a p - a s‖ := by ring
      calc
        ‖E R - E S‖ = ‖D.comp (b p - b s)‖ := by
          rw [hER, hES]
          congr 1
          ext x
          simp
        _ ≤ ‖D‖ * ‖b p - b s‖ := D.opNorm_comp_le _
        _ ≤ ‖D‖ * ((1 / (1 - q)) ^ 2 * ‖a p - a s‖) :=
          mul_le_mul_of_nonneg_left hbDiffNorm (norm_nonneg D)
        _ ≤ ‖D‖ * ((1 / (1 - q)) ^ 2 * (‖R - S‖ * ‖D‖)) := by
          gcongr
        _ = (‖D‖ ^ 2 / (1 - q) ^ 2) * ‖R - S‖ := by
          have hqden : 1 - q ≠ 0 := ne_of_gt (sub_pos.mpr hq)
          field_simp [hqden]
  · have hsub : Subsingleton X := not_nontrivial_iff_subsingleton.mp hX
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro R hR
      constructor
      · ext x
        have hx : x = 0 := hsub.elim x 0
        subst x
        simp
      · simp
    · intro R S hR hS
      simp
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.PerturbedRightInverseFamily
