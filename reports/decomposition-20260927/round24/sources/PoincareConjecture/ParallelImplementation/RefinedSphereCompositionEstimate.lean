import PoincareConjecture.ProofContract.Refinement20260927.AmbientApproximationLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedSphereCompositionEstimate
open PoincareConjecture.ProofContract.Refinement20260927
theorem sphere_composition_estimate : SphereCompositionEstimateStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro n P a b p v Q C delta hda hdb hdPa hdPb hPb hQ hC hdelta hnorm hdiff hvec hCvec
  letI : NormedAddCommGroup (ApproxAmbient n) := PiLp.normedAddCommGroup 2 (fun _ : Fin n => ℝ)
  letI : NormedSpace ℝ (ApproxAmbient n) := PiLp.normedSpace 2 ℝ (fun _ : Fin n => ℝ)
  have hA : ambientDirectionalDerivative (P ∘ a) p v =
      fderiv ℝ P (a p) (ambientDirectionalDerivative a p v) := by
    change NormedSpace.fromTangentSpace ((P ∘ a) p)
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (ApproxAmbient n)) (P ∘ a) p v) =
      fderiv ℝ P (a p) (NormedSpace.fromTangentSpace (a p)
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (ApproxAmbient n)) a p v))
    have h := mfderiv_comp_apply (f := a) (x := p) (g := P)
      hdPa.mdifferentiableAt hda v
    have h' := congrArg (NormedSpace.fromTangentSpace ((P ∘ a) p)) h
    convert h' using 1 <;> simp only [mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] <;> rfl
  have hB : ambientDirectionalDerivative (P ∘ b) p v =
      fderiv ℝ P (b p) (ambientDirectionalDerivative b p v) := by
    change NormedSpace.fromTangentSpace ((P ∘ b) p)
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (ApproxAmbient n)) (P ∘ b) p v) =
      fderiv ℝ P (b p) (NormedSpace.fromTangentSpace (b p)
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (ApproxAmbient n)) b p v))
    have h := mfderiv_comp_apply (f := b) (x := p) (g := P)
      hdPb.mdifferentiableAt hdb v
    have h' := congrArg (NormedSpace.fromTangentSpace ((P ∘ b) p)) h
    convert h' using 1 <;> simp only [mfderiv_eq_fderiv, NormedSpace.fromTangentSpace] <;> rfl
  have hfixed : fderiv ℝ P (b p) (ambientDirectionalDerivative b p v) =
      ambientDirectionalDerivative b p v := by
    have h := congrArg (fun f => ambientDirectionalDerivative f p v) hPb
    rw [hB] at h
    exact h
  have hdecomp : ambientDirectionalDerivative (P ∘ a) p v -
        ambientDirectionalDerivative b p v =
      fderiv ℝ P (a p) (ambientDirectionalDerivative a p v -
        ambientDirectionalDerivative b p v) +
      (fderiv ℝ P (a p) - fderiv ℝ P (b p))
        (ambientDirectionalDerivative b p v) := by
    rw [hA, map_sub, ContinuousLinearMap.sub_apply, hfixed]
    abel
  have hfirst : ‖fderiv ℝ P (a p)
        (ambientDirectionalDerivative a p v - ambientDirectionalDerivative b p v)‖ ≤
      Q * delta := by
    calc
      _ ≤ ‖fderiv ℝ P (a p)‖ *
          ‖ambientDirectionalDerivative a p v - ambientDirectionalDerivative b p v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ Q * ‖ambientDirectionalDerivative a p v - ambientDirectionalDerivative b p v‖ :=
        mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
      _ ≤ Q * delta := mul_le_mul_of_nonneg_left hvec hQ
  have hsecond : ‖(fderiv ℝ P (a p) - fderiv ℝ P (b p))
        (ambientDirectionalDerivative b p v)‖ ≤ delta * C := by
    calc
      _ ≤ ‖fderiv ℝ P (a p) - fderiv ℝ P (b p)‖ *
          ‖ambientDirectionalDerivative b p v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ delta * ‖ambientDirectionalDerivative b p v‖ :=
        mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
      _ ≤ delta * C := mul_le_mul_of_nonneg_left hCvec hdelta
  calc
    ‖ambientDirectionalDerivative (P ∘ a) p v - ambientDirectionalDerivative b p v‖ =
        ‖fderiv ℝ P (a p) (ambientDirectionalDerivative a p v -
          ambientDirectionalDerivative b p v) +
          (fderiv ℝ P (a p) - fderiv ℝ P (b p))
            (ambientDirectionalDerivative b p v)‖ := by rw [hdecomp]
    _ ≤ Q * delta + delta * C := by
      calc
        _ ≤ ‖fderiv ℝ P (a p)
              (ambientDirectionalDerivative a p v - ambientDirectionalDerivative b p v)‖ +
            ‖(fderiv ℝ P (a p) - fderiv ℝ P (b p))
              (ambientDirectionalDerivative b p v)‖ := norm_add_le _ _
        _ ≤ Q * delta + delta * C := add_le_add hfirst hsecond
    _ = delta * (Q + C) := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedSphereCompositionEstimate
