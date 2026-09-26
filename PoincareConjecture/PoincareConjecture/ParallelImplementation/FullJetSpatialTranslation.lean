import PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetSpatialTranslation
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
open PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
def translateFullJet {T : ℝ} (i : Fin 3) (h : ℝ) (z : FullJet T) : FullJet T :=
  ((((pullbackBCF (spatialShiftSlabMap i h) z.1.1.1.1,
      (pullbackBCF (spatialShiftSlabMap i h) z.1.1.1.2.1,
       pullbackBCF (spatialShiftSlabMap i h) z.1.1.1.2.2)),
      pullbackBCF (spatialShiftPairMap i h) z.1.1.2),
    pullbackBCF (spatialShiftSlabMap i h) z.1.2),
    pullbackBCF (spatialShiftPairMap i h) z.2)
/-- Actual spatial translation preserves the zero-trace full jet graph and norm,
and commutes with the pointwise heat residual on those same fields. -/
theorem full_jet_translation_properties (T alpha : ℝ) (hT : 0 ≤ T)
    (i : Fin 3) (h : ℝ) :
    (∀ z : FullJet T,
      translateFullJet i h z ∈ fullParabolicJetSet T alpha hT ↔
        z ∈ fullParabolicJetSet T alpha hT) ∧
    (∀ z : FullJet T, ‖translateFullJet i h z‖ = ‖z‖) ∧
    (∀ z : FullJet T, translateFullJet i (-h) (translateFullJet i h z) = z) ∧
    (∀ z w : FullJet T, translateFullJet i h (z + w) =
      translateFullJet i h z + translateFullJet i h w) ∧
    (∀ (a : ℝ) (z : FullJet T), translateFullJet i h (a • z) =
      a • translateFullJet i h z) ∧
    (∀ (z : FullJet T) (p : Slab T),
      (translateFullJet i h z).1.2 p - ∑ j : Fin 3,
        (translateFullJet i h z).1.1.1.2.2 p
          (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) =
      z.1.2 (shiftPoint p i h) - ∑ j : Fin 3,
        z.1.1.1.2.2 (shiftPoint p i h)
          (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hshiftInv (p : Slab T) : shiftPoint (shiftPoint p i h) i (-h) = p := by
    apply Prod.ext
    · rfl
    · simp [shiftPoint, add_assoc]
  have hpairShiftInv (p : Pair T) :
      spatialShiftPairMap i (-h) (spatialShiftPairMap i h p) = p := by
    apply Subtype.ext
    change (shiftPoint (shiftPoint p.1.1 i h) i (-h),
      shiftPoint (shiftPoint p.1.2 i h) i (-h)) = p.1
    exact Prod.ext (hshiftInv p.1.1) (hshiftInv p.1.2)
  have hslabNorm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (F : Slab T →ᵇ V) (k : ℝ) :
      ‖pullbackBCF (spatialShiftSlabMap i k) F‖ = ‖F‖ := by
    apply le_antisymm
    · exact BoundedContinuousFunction.norm_compContinuous_le F
        (spatialShiftSlabMap i k)
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
      intro p
      let p' : Slab T := (p.1, p.2 - k • spatialUnit i)
      have hp : spatialShiftSlabMap i k p' = p := by
        apply Prod.ext
        · rfl
        · simp [spatialShiftSlabMap, shiftPoint, p', smul_sub, add_assoc]
      rw [← hp]
      exact (pullbackBCF (spatialShiftSlabMap i k) F).norm_coe_le_norm p'
  have hpairNorm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (F : Pair T →ᵇ V) (k : ℝ) :
      ‖pullbackBCF (spatialShiftPairMap i k) F‖ = ‖F‖ := by
    apply le_antisymm
    · exact BoundedContinuousFunction.norm_compContinuous_le F
        (spatialShiftPairMap i k)
    · apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).2
      intro p
      let a : Slab T := (p.1.1.1, p.1.1.2 - k • spatialUnit i)
      let b : Slab T := (p.1.2.1, p.1.2.2 - k • spatialUnit i)
      have hab : a ≠ b := by
        intro heq
        apply p.2
        have hh := congrArg (fun x : Slab T => shiftPoint x i k) heq
        simpa [a, b, shiftPoint] using hh
      let p' : Pair T := ⟨(a, b), hab⟩
      have hp : spatialShiftPairMap i k p' = p := by
        apply Subtype.ext
        apply Prod.ext
        · simp [p', a, spatialShiftPairMap, shiftPoint]
        · simp [p', b, spatialShiftPairMap, shiftPoint]
      rw [← hp]
      exact (pullbackBCF (spatialShiftPairMap i k) F).norm_coe_le_norm p'
  have hnorm (z : FullJet T) : ‖translateFullJet i h z‖ = ‖z‖ := by
    unfold translateFullJet
    simp only [Prod.norm_def]
    simp only [hslabNorm, hpairNorm]
  have hlinearAdd (z w : FullJet T) :
      translateFullJet i h (z + w) = translateFullJet i h z + translateFullJet i h w := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext <;> ext x <;> rfl
        · ext x <;> rfl
      · ext x <;> rfl
    · ext x <;> rfl
  have hlinearSmul (a : ℝ) (z : FullJet T) :
      translateFullJet i h (a • z) = a • translateFullJet i h z := by
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext <;> ext x <;> rfl
        · ext x <;> rfl
      · ext x <;> rfl
    · ext x <;> rfl
  have hinverse (z : FullJet T) :
      translateFullJet i (-h) (translateFullJet i h z) = z := by
    unfold translateFullJet
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · apply Prod.ext <;> ext x <;>
            simp [pullbackBCF, spatialShiftSlabMap, shiftPoint, hshiftInv]
        · ext x <;>
            simp [pullbackBCF, spatialShiftPairMap, shiftPoint, hpairShiftInv]
      · ext x <;>
          simp [pullbackBCF, spatialShiftSlabMap, shiftPoint, hshiftInv]
    · ext x <;>
        simp [pullbackBCF, spatialShiftPairMap, shiftPoint, hpairShiftInv]

  have hpres (k : ℝ) (z : FullJet T)
      (hz : z ∈ fullParabolicJetSet T alpha hT) :
      translateFullJet i k z ∈ fullParabolicJetSet T alpha hT := by
    rcases hz with ⟨hzSpace, hzTime, hzTimeInc, hzTrace⟩
    have hspace : z.1.1.1 ∈ spaceTimeC2JetSet T := hzSpace.1
    have htranslatedSpace : (translateFullJet i k z).1.1.1 ∈ spaceTimeC2JetSet T := by
      change ∀ t : Set.Icc (0 : ℝ) T,
        (∀ x : E3, HasFDerivAt
          (fun y => (pullbackBCF (spatialShiftSlabMap i k) z.1.1.1.1) (t, y))
          ((pullbackBCF (spatialShiftSlabMap i k) z.1.1.1.2.1) (t, x)) x) ∧
        (∀ x : E3, HasFDerivAt
          (fun y => (pullbackBCF (spatialShiftSlabMap i k) z.1.1.1.2.1) (t, y))
          ((pullbackBCF (spatialShiftSlabMap i k) z.1.1.1.2.2) (t, x)) x)
      intro t
      have hj := hspace t
      let c : E3 := k • spatialUnit i
      constructor
      · intro x
        have hinner : HasFDerivAt (fun y : E3 => c + y)
            (ContinuousLinearMap.id ℝ E3) x := by
          simpa using (hasFDerivAt_id x).const_add c
        have hc := HasFDerivAt.comp (f := fun y : E3 => c + y) (x := x)
          (hj.1 (c + x)) hinner
        simpa [pullbackBCF, spatialShiftSlabMap, shiftPoint, c,
          Function.comp_def, add_comm, ContinuousLinearMap.comp_id] using hc
      · intro x
        have hinner : HasFDerivAt (fun y : E3 => c + y)
            (ContinuousLinearMap.id ℝ E3) x := by
          simpa using (hasFDerivAt_id x).const_add c
        have hc := HasFDerivAt.comp (f := fun y : E3 => c + y) (x := x)
          (hj.2 (c + x)) hinner
        simpa [pullbackBCF, spatialShiftSlabMap, shiftPoint, c,
          Function.comp_def, add_comm, ContinuousLinearMap.comp_id] using hc
    have htranslatedHolder : (translateFullJet i k z).1.1 ∈
        parabolicC2HolderSet T alpha := by
      change (translateFullJet i k z).1.1.1 ∈ spaceTimeC2JetSet T ∧
        ∀ p : Pair T, (translateFullJet i k z).1.1.2 p =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            ((translateFullJet i k z).1.1.1.2.2 p.1.1 -
              (translateFullJet i k z).1.1.1.2.2 p.1.2)
      refine ⟨htranslatedSpace, ?_⟩
      intro p
      have hincr := hzSpace.2 (spatialShiftPairMap i k p)
      have hincr' : z.1.1.2 (spatialShiftPairMap i k p) =
          (parabolicRho (shiftPoint p.1.1 i k)
            (shiftPoint p.1.2 i k) ^ alpha)⁻¹ •
            (z.1.1.1.2.2 (shiftPoint p.1.1 i k) -
              z.1.1.1.2.2 (shiftPoint p.1.2 i k)) := by
        simpa [spatialShiftPairMap] using hincr
      rw [spatialShiftPair_rho i k p] at hincr'
      change z.1.1.2 (spatialShiftPairMap i k p) =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          (z.1.1.1.2.2 (shiftPoint p.1.1 i k) -
            z.1.1.1.2.2 (shiftPoint p.1.2 i k))
      exact hincr'
    have htranslatedTime :
        ((translateFullJet i k z).1.1.1.1, (translateFullJet i k z).1.2) ∈
          slabTimeDerivativeGraph T := by
      change ∀ t : Set.Icc (0 : ℝ) T, 0 < (t : ℝ) → (t : ℝ) < T → ∀ x : E3,
        HasDerivAt (timeExtension
          (pullbackBCF (spatialShiftSlabMap i k) z.1.1.1.1) x)
          ((pullbackBCF (spatialShiftSlabMap i k) z.1.2) (t, x)) (t : ℝ)
      intro t ht0 htT x
      let c : E3 := k • spatialUnit i
      have hext : timeExtension
          (pullbackBCF (spatialShiftSlabMap i k) z.1.1.1.1) x =
          timeExtension z.1.1.1.1 (x + c) := by
        funext s
        by_cases hs : s ∈ Set.Icc (0 : ℝ) T
        · simp [timeExtension, pullbackBCF, spatialShiftSlabMap, shiftPoint, c, hs]
        · simp [timeExtension, hs]
      have hd := hzTime t ht0 htT (x + c)
      have hval : (pullbackBCF (spatialShiftSlabMap i k) z.1.2) (t, x) =
          z.1.2 (t, x + c) := by
        rfl
      rw [hext, hval]
      exact hd
    have htranslatedTimeInc : ∀ p : Pair T,
        (translateFullJet i k z).2 p =
          (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
            ((translateFullJet i k z).1.2 p.1.1 -
              (translateFullJet i k z).1.2 p.1.2) := by
      intro p
      have hincr := hzTimeInc (spatialShiftPairMap i k p)
      have hincr' : z.2 (spatialShiftPairMap i k p) =
          (parabolicRho (shiftPoint p.1.1 i k)
            (shiftPoint p.1.2 i k) ^ alpha)⁻¹ •
            (z.1.2 (shiftPoint p.1.1 i k) -
              z.1.2 (shiftPoint p.1.2 i k)) := by
        simpa [spatialShiftPairMap] using hincr
      rw [spatialShiftPair_rho i k p] at hincr'
      change z.2 (spatialShiftPairMap i k p) =
        (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
          (z.1.2 (shiftPoint p.1.1 i k) - z.1.2 (shiftPoint p.1.2 i k))
      exact hincr'
    have htranslatedTrace : ∀ x : E3,
        (translateFullJet i k z).1.1.1.1 (⟨0, le_rfl, hT⟩, x) = 0 := by
      intro x
      have hzero := hzTrace (x + k • spatialUnit i)
      simpa [translateFullJet, pullbackBCF, spatialShiftSlabMap,
        shiftPoint] using hzero
    exact ⟨htranslatedHolder, htranslatedTime, htranslatedTimeInc,
      htranslatedTrace⟩

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro z
    constructor
    · intro htz
      have hback := hpres (-h) (translateFullJet i h z) htz
      simpa [hinverse z] using hback
    · intro hz
      exact hpres h z hz
  · exact hnorm
  · exact hinverse
  · exact hlinearAdd
  · exact hlinearSmul
  · intro z p
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetSpatialTranslation
