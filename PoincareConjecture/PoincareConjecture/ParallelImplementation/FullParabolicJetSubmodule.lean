import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullParabolicJetSubmodule
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BoundedContinuousFunction
/-- The exact zero-initial-value derivative graph is a complete real linear subspace. -/
theorem full_parabolic_jet_submodule (T alpha : ℝ) (hT : 0 ≤ T) (ha : 0 < alpha) :
    ∃ S : Submodule ℝ (FullJet T),
      (S : Set (FullJet T)) = fullParabolicJetSet T alpha hT ∧ CompleteSpace S :=
/- SWARM_PROOF_BEGIN -/
by
  let S : Submodule ℝ (FullJet T) := {
    carrier := fullParabolicJetSet T alpha hT
    zero_mem' := by
      change ((0 : FullJet T).1.1 ∈ parabolicC2HolderSet T alpha) ∧
        (( (0 : FullJet T).1.1.1.1, (0 : FullJet T).1.2) ∈
          slabTimeDerivativeGraph T) ∧
        (∀ p : Pair T, (0 : FullJet T).2 p =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            ((0 : FullJet T).1.2 p.1.1 - (0 : FullJet T).1.2 p.1.2)) ∧
        (∀ x : EuclideanSpace ℝ (Fin 3),
          (0 : FullJet T).1.1.1.1 (⟨0, le_rfl, hT⟩, x) = 0)
      refine ⟨?_, ?_, ?_, ?_⟩
      · change ((0 : HolderJet T).1 ∈ spaceTimeC2JetSet T) ∧ _
        refine ⟨?_, ?_⟩
        · intro t
          constructor
          · intro x
            simpa using hasFDerivAt_const (𝕜 := ℝ)
              (0 : EuclideanSpace ℝ (Fin 6)) x
          · intro x
            simpa using hasFDerivAt_const (𝕜 := ℝ)
              (0 : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 6)) x
        · intro p
          simp
      · intro t ht0 htT x
        have hz : timeExtension (0 : Slab T →ᵇ EuclideanSpace ℝ (Fin 6)) x =
            fun _ => (0 : EuclideanSpace ℝ (Fin 6)) := by
          funext s
          simp [timeExtension]
        change HasDerivAt (timeExtension (0 : Slab T →ᵇ EuclideanSpace ℝ (Fin 6)) x)
          ((0 : Slab T →ᵇ EuclideanSpace ℝ (Fin 6)) (t, x)) (t : ℝ)
        rw [hz]
        simpa using hasDerivAt_const (𝕜 := ℝ) (t : ℝ)
          (0 : EuclideanSpace ℝ (Fin 6))
      · intro p
        simp
      · intro (x : EuclideanSpace ℝ (Fin 3))
        simp
    add_mem' := by
      intro z w hz hw
      change z + w ∈ fullParabolicJetSet T alpha hT
      rcases hz with ⟨hzHolder, hzTime, hzIncrement, hzTrace⟩
      rcases hw with ⟨hwHolder, hwTime, hwIncrement, hwTrace⟩
      rcases hzHolder with ⟨hzJet, hzHess⟩
      rcases hwHolder with ⟨hwJet, hwHess⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro t
          constructor
          · intro x
            change HasFDerivAt
              (fun y => z.1.1.1.1 (t, y) + w.1.1.1.1 (t, y))
              (z.1.1.1.2.1 (t, x) + w.1.1.1.2.1 (t, x)) x
            exact ((hzJet t).1 x).add ((hwJet t).1 x)
          · intro x
            change HasFDerivAt
              (fun y => z.1.1.1.2.1 (t, y) + w.1.1.1.2.1 (t, y))
              (z.1.1.1.2.2 (t, x) + w.1.1.1.2.2 (t, x)) x
            exact ((hzJet t).2 x).add ((hwJet t).2 x)
        · intro p
          change z.1.1.2 p + w.1.1.2 p =
            (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
              ((z.1.1.1.2.2 p.1.1 + w.1.1.1.2.2 p.1.1) -
                (z.1.1.1.2.2 p.1.2 + w.1.1.1.2.2 p.1.2))
          simp [hzHess p, hwHess p, sub_eq_add_neg, smul_add]
          abel
      · intro t ht0 htT x
        have hfun : timeExtension (z.1.1.1.1 + w.1.1.1.1) x =
            timeExtension z.1.1.1.1 x + timeExtension w.1.1.1.1 x := by
          funext s
          by_cases hs : s ∈ Set.Icc (0 : ℝ) T
          · simp [timeExtension, hs]
          · simp [timeExtension, hs]
        have hsum := (hzTime t ht0 htT x).add (hwTime t ht0 htT x)
        have hsum' := hsum.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s => congrFun hfun s)
        simpa [timeExtension, ht0.le, htT.le] using hsum'
      · intro p
        change z.2 p + w.2 p =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            ((z.1.2 p.1.1 + w.1.2 p.1.1) - (z.1.2 p.1.2 + w.1.2 p.1.2))
        simp [hzIncrement p, hwIncrement p, sub_eq_add_neg, smul_add]
        abel
      · intro x
        simp [hzTrace x, hwTrace x]
    smul_mem' := by
      intro c z hz
      change c • z ∈ fullParabolicJetSet T alpha hT
      rcases hz with ⟨hzHolder, hzTime, hzIncrement, hzTrace⟩
      rcases hzHolder with ⟨hzJet, hzHess⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro t
          constructor
          · intro x
            change HasFDerivAt (fun y => c • z.1.1.1.1 (t, y))
              (c • z.1.1.1.2.1 (t, x)) x
            exact ((hzJet t).1 x).const_smul c
          · intro x
            change HasFDerivAt (fun y => c • z.1.1.1.2.1 (t, y))
              (c • z.1.1.1.2.2 (t, x)) x
            exact ((hzJet t).2 x).const_smul c
        · intro p
          change c • z.1.1.2 p =
            (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
              ((c • z.1.1.1.2.2 p.1.1) - (c • z.1.1.1.2.2 p.1.2))
          simp [hzHess p, smul_sub, smul_smul, mul_comm]
      · intro t ht0 htT x
        have hfun : timeExtension (c • z.1.1.1.1) x =
            c • timeExtension z.1.1.1.1 x := by
          funext s
          by_cases hs : s ∈ Set.Icc (0 : ℝ) T
          · simp [timeExtension, hs]
          · simp [timeExtension, hs]
        have hsmul := (hzTime t ht0 htT x).const_smul c
        have hsmul' := hsmul.congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun s => congrFun hfun s)
        simpa [timeExtension, ht0.le, htT.le] using hsmul'
      · intro p
        change c • z.2 p =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            ((c • z.1.2 p.1.1) - (c • z.1.2 p.1.2))
        simp [hzIncrement p, smul_sub, smul_smul, mul_comm]
      · intro x
        simp [hzTrace x]
  }
  refine ⟨S, rfl, ?_⟩
  have hcomplete : IsComplete (fullParabolicJetSet T alpha hT) :=
    full_parabolic_jet_complete T alpha hT ha
  change CompleteSpace (fullParabolicJetSet T alpha hT)
  exact hcomplete.completeSpace_coe
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullParabolicJetSubmodule
