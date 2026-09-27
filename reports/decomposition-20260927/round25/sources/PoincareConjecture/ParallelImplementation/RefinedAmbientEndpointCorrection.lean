import PoincareConjecture.ProofContract.Refinement20260927.AmbientApproximationLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedAmbientEndpointCorrection
open PoincareConjecture.ProofContract.Refinement20260927
theorem ambient_endpoint_correction : AmbientEndpointCorrectionStatement :=
/- SWARM_PROOF_BEGIN -/
by
  intro n a f base delta hdelta ha hf hval hderiv
  constructor
  · unfold correctAmbientEnds
    have ha0 : ContMDiff SweepModel (modelWithCornersSelf ℝ (ApproxAmbient n)) (↑(⊤ : ℕ∞))
        (fun q : ℝ × ProofContract.V1.Sphere2 => a (0,q.2)) :=
      ha.comp (contMDiff_const.prodMk contMDiff_snd)
    have ha1 : ContMDiff SweepModel (modelWithCornersSelf ℝ (ApproxAmbient n)) (↑(⊤ : ℕ∞))
        (fun q : ℝ × ProofContract.V1.Sphere2 => a (1,q.2)) :=
      ha.comp (contMDiff_const.prodMk contMDiff_snd)
    have hwt0 : ContMDiff SweepModel (modelWithCornersSelf ℝ ℝ) (↑(⊤ : ℕ∞))
        (fun q : ℝ × ProofContract.V1.Sphere2 => 1-q.1) :=
      contMDiff_const.sub contMDiff_fst
    exact (ha.sub (hwt0.smul (ha0.sub contMDiff_const))).sub
      (contMDiff_fst.smul (ha1.sub contMDiff_const))
  · constructor
    · intro p
      constructor
      · simp [correctAmbientEnds]
      · simp [correctAmbientEnds]
    · constructor
      · intro q
        let t : ℝ := (q.1 : ℝ)
        have ht0 : 0 ≤ t := q.1.2.1
        have ht1 : t ≤ 1 := q.1.2.2
        have hf0 : f (0,q.2) = base := by
          have he : (0,q.2) ∈ sweepoutEnds := by simp [sweepoutEnds]
          have h := hf he
          simpa using h
        have hf1 : f (1,q.2) = base := by
          have he : (1,q.2) ∈ sweepoutEnds := by simp [sweepoutEnds]
          have h := hf he
          simpa using h
        have hmain : ‖a (t,q.2) - f q‖ < delta := by
          simpa [t, dist_eq_norm] using hval q
        have hend0 : ‖a (0,q.2) - base‖ < delta := by
          have h := hval (0,q.2)
          simpa [dist_eq_norm, hf0] using h
        have hend1 : ‖a (1,q.2) - base‖ < delta := by
          have h := hval (1,q.2)
          simpa [dist_eq_norm, hf1] using h
        have hc0 : 0 ≤ 1-t := by linarith
        have hc1 : 0 ≤ t := ht0
        have hb0 : (1-t) * ‖a (0,q.2)-base‖ ≤ (1-t) * delta :=
          mul_le_mul_of_nonneg_left hend0.le hc0
        have hb1 : t * ‖a (1,q.2)-base‖ ≤ t * delta :=
          mul_le_mul_of_nonneg_left hend1.le hc1
        have hnorm :
            ‖(a (t,q.2) - f q) - (1-t) • (a (0,q.2)-base) -
              t • (a (1,q.2)-base)‖ < 2*delta := by
          calc
            _ ≤ ‖a (t,q.2) - f q‖ +
                ‖(1-t) • (a (0,q.2)-base)‖ +
                ‖t • (a (1,q.2)-base)‖ := by
              calc
                _ ≤ ‖(a (t,q.2)-f q) - (1-t) • (a (0,q.2)-base)‖ +
                    ‖t • (a (1,q.2)-base)‖ := norm_sub_le _ _
                _ ≤ _ := by
                  gcongr
                  exact norm_sub_le _ _
            _ ≤ ‖a (t,q.2)-f q‖ + (1-t) * ‖a (0,q.2)-base‖ +
                t * ‖a (1,q.2)-base‖ := by
              simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0, abs_of_nonneg hc1]
            _ ≤ ‖a (t,q.2)-f q‖ + (1-t)*delta + t*delta := by
              linarith
            _ < 2*delta := by
              have hw : (1-t)*delta + t*delta = delta := by ring
              calc
                _ = ‖a (t,q.2)-f q‖ + ((1-t)*delta + t*delta) := by ring
                _ = ‖a (t,q.2)-f q‖ + delta := by rw [hw]
                _ < delta + delta := by linarith
                _ = 2*delta := by ring
        have hdist : dist
            (correctAmbientEnds a base (t,q.2)) (f q) =
              ‖(a (t,q.2)-f q) - (1-t) • (a (0,q.2)-base) -
                t • (a (1,q.2)-base)‖ := by
          simp only [correctAmbientEnds, dist_eq_norm]
          congr 1
          abel
        rw [hdist]
        exact hnorm
      · intro s p i
        let t : ℝ := (s : ℝ)
        have ht0 : 0 ≤ t := s.2.1
        have ht1 : t ≤ 1 := s.2.2
        have hf0 : f (0,p) = base := by
          have he : (0,p) ∈ sweepoutEnds := by simp [sweepoutEnds]
          simpa using hf he
        have hf1 : f (1,p) = base := by
          have he : (1,p) ∈ sweepoutEnds := by simp [sweepoutEnds]
          simpa using hf he
        have hfconst0 : (fun z : ProofContract.V1.Sphere2 => f (0,z)) = fun _ => base :=
          funext fun z => by
            have he : (0,z) ∈ sweepoutEnds := by simp [sweepoutEnds]
            simpa using hf he
        have hfconst1 : (fun z : ProofContract.V1.Sphere2 => f (1,z)) = fun _ => base :=
          funext fun z => by
            have he : (1,z) ∈ sweepoutEnds := by simp [sweepoutEnds]
            simpa using hf he
        have hfder0 : ambientSliceVector (fun z => f (0,z)) p i = 0 := by
          rw [hfconst0]
          simp [ambientSliceVector]
        have hfder1 : ambientSliceVector (fun z => f (1,z)) p i = 0 := by
          rw [hfconst1]
          simp [ambientSliceVector]
        have hA0 : ‖ambientSliceVector (fun z => a (0,z)) p i‖ ≤ delta := by
          simpa [hfder0] using hderiv (0 : SweepParameter) p i
        have hA1 : ‖ambientSliceVector (fun z => a (1,z)) p i‖ ≤ delta := by
          simpa [hfder1] using hderiv (1 : SweepParameter) p i
        let A : ProofContract.V1.Sphere2 → ApproxAmbient n := fun z => a (t,z)
        let A0 : ProofContract.V1.Sphere2 → ApproxAmbient n := fun z => a (0,z)
        let A1 : ProofContract.V1.Sphere2 → ApproxAmbient n := fun z => a (1,z)
        let G0 : ProofContract.V1.Sphere2 → ApproxAmbient n := fun z => a (0,z)-base
        let G1 : ProofContract.V1.Sphere2 → ApproxAmbient n := fun z => a (1,z)-base
        let B : ProofContract.V1.Sphere2 → ApproxAmbient n := fun z => A z-(1-t) • G0 z
        have hA_diff : MDifferentiable
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ (ApproxAmbient n)) A := by
          simpa [A, Function.comp_def] using
            ((ha.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp))
        have hAt := hA_diff p
        have hA0_diff : MDifferentiable
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ (ApproxAmbient n)) A0 := by
          simpa [A0, Function.comp_def] using
            ((ha.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp))
        have hA0t := hA0_diff p
        have hA1_diff : MDifferentiable
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ (ApproxAmbient n)) A1 := by
          simpa [A1, Function.comp_def] using
            ((ha.comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable (by simp))
        have hA1t := hA1_diff p
        have hG0t : MDifferentiableAt
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ (ApproxAmbient n)) G0 p := by
          dsimp [G0]
          exact hA0t.sub mdifferentiableAt_const
        have hG1t : MDifferentiableAt
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ (ApproxAmbient n)) G1 p := by
          dsimp [G1]
          exact hA1t.sub mdifferentiableAt_const
        have hG0ct : MDifferentiableAt
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ (ApproxAmbient n)) (fun z => (1-t) • G0 z) p :=
          hG0t.const_smul (1-t)
        have hG1ct : MDifferentiableAt
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ (ApproxAmbient n)) (fun z => t • G1 z) p :=
          hG1t.const_smul t
        have hBt : MDifferentiableAt
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ (ApproxAmbient n)) B p := by
          dsimp [B]
          exact hAt.sub hG0ct
        have hsliceVec (g : ProofContract.V1.Sphere2 → ApproxAmbient n) :
            ambientSliceVector g p i =
              mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) g p
                (sphereEnergyFrame p i) := by
          rfl
        have hG0vec : ambientSliceVector G0 p i = ambientSliceVector A0 p i := by
          rw [hsliceVec G0, hsliceVec A0]
          change mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (A0 - fun _ => base) p (sphereEnergyFrame p i) =
            mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              A0 p (sphereEnergyFrame p i)
          rw [mvfderiv_sub hA0t mdifferentiableAt_const]
          simp [mvfderiv_const]
        have hG1vec : ambientSliceVector G1 p i = ambientSliceVector A1 p i := by
          rw [hsliceVec G1, hsliceVec A1]
          change mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (A1 - fun _ => base) p (sphereEnergyFrame p i) =
            mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              A1 p (sphereEnergyFrame p i)
          rw [mvfderiv_sub hA1t mdifferentiableAt_const]
          simp [mvfderiv_const]
        have hC : (fun z => correctAmbientEnds a base (t,z)) =
            fun z => B z-t • G1 z := by
          funext z
          simp [correctAmbientEnds, A, G0, G1, B]
        have hconst0t : MDifferentiableAt
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℝ) (fun _ : ProofContract.V1.Sphere2 => 1-t) p :=
          mdifferentiableAt_const
        have hconst1t : MDifferentiableAt
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
            (modelWithCornersSelf ℝ ℝ) (fun _ : ProofContract.V1.Sphere2 => t) p :=
          mdifferentiableAt_const
        have hsmul0 :
            mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
                (fun z => (1-t) • G0 z) p (sphereEnergyFrame p i) =
              (1-t) • mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
                G0 p (sphereEnergyFrame p i) := by
          have h := congrArg (fun L => L (sphereEnergyFrame p i))
            (mvfderiv_smul hconst0t hG0t)
          have heq : (fun z => (1-t) • G0 z) =
              (fun _ : ProofContract.V1.Sphere2 => (1-t)) • G0 := by
            funext z
            rfl
          rw [heq]
          simpa [mvfderiv_const] using h
        have hsmul1 :
            mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
                (fun z => t • G1 z) p (sphereEnergyFrame p i) =
              t • mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
                G1 p (sphereEnergyFrame p i) := by
          have h := congrArg (fun L => L (sphereEnergyFrame p i))
            (mvfderiv_smul hconst1t hG1t)
          have heq : (fun z => t • G1 z) =
              (fun _ : ProofContract.V1.Sphere2 => t) • G1 := by
            funext z
            rfl
          rw [heq]
          simpa [mvfderiv_const] using h
        have hformulaMV :
            mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
                (fun z => correctAmbientEnds a base (t,z)) p (sphereEnergyFrame p i) =
              mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
                  A p (sphereEnergyFrame p i) -
                (1-t) • mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
                  G0 p (sphereEnergyFrame p i) -
                t • mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
                  G1 p (sphereEnergyFrame p i) := by
          rw [hC]
          change mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              (B - fun z => t • G1 z) p (sphereEnergyFrame p i) = _
          rw [mvfderiv_sub hBt hG1ct]
          change (mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              (A - fun z => (1-t) • G0 z) p -
            mvfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              (fun z => t • G1 z) p) (sphereEnergyFrame p i) = _
          rw [mvfderiv_sub hAt hG0ct]
          simp [hsmul0, hsmul1]
        have hformula :
            ambientSliceVector (fun z => correctAmbientEnds a base (t,z)) p i =
              ambientSliceVector A p i - (1-t) • ambientSliceVector G0 p i -
                t • ambientSliceVector G1 p i := by
          rw [hsliceVec, hformulaMV, ← hsliceVec A, ← hsliceVec G0, ← hsliceVec G1]
        have hmain :
            ‖ambientSliceVector A p i - ambientSliceVector (fun z => f (s,z)) p i‖ ≤ delta := by
          simpa [A, t] using hderiv s p i
        have hc0 : 0 ≤ 1-t := by linarith
        have hc1 : 0 ≤ t := ht0
        have hbound :
            ‖ambientSliceVector (fun z => correctAmbientEnds a base (t,z)) p i -
              ambientSliceVector (fun z => f (s,z)) p i‖ ≤ 2*delta := by
          rw [hformula]
          have hweight0 : (1-t) * ‖ambientSliceVector G0 p i‖ ≤ (1-t)*delta :=
            mul_le_mul_of_nonneg_left (by rw [hG0vec]; exact hA0) hc0
          have hweight1 : t * ‖ambientSliceVector G1 p i‖ ≤ t*delta :=
            mul_le_mul_of_nonneg_left (by rw [hG1vec]; exact hA1) hc1
          calc
            _ = ‖(ambientSliceVector A p i - ambientSliceVector (fun z => f (s,z)) p i) -
                  (1-t) • ambientSliceVector G0 p i - t • ambientSliceVector G1 p i‖ := by
              congr 1
              abel
            _ ≤ ‖ambientSliceVector A p i - ambientSliceVector (fun z => f (s,z)) p i‖ +
                  ‖(1-t) • ambientSliceVector G0 p i‖ + ‖t • ambientSliceVector G1 p i‖ := by
              calc
                _ ≤ ‖(ambientSliceVector A p i - ambientSliceVector (fun z => f (s,z)) p i) -
                      (1-t) • ambientSliceVector G0 p i‖ + ‖t • ambientSliceVector G1 p i‖ :=
                  norm_sub_le _ _
                _ ≤ _ := by gcongr; exact norm_sub_le _ _
            _ ≤ delta + (1-t)*delta + t*delta := by
              have hn0 : ‖(1-t) • ambientSliceVector G0 p i‖ =
                  (1-t) * ‖ambientSliceVector G0 p i‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc0]
              have hn1 : ‖t • ambientSliceVector G1 p i‖ =
                  t * ‖ambientSliceVector G1 p i‖ := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc1]
              rw [hn0, hn1]
              linarith
            _ = 2*delta := by ring
        simpa [t] using hbound
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedAmbientEndpointCorrection
