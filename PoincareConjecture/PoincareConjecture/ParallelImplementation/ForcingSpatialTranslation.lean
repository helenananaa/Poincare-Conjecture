import PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
open scoped Topology BigOperators BoundedContinuousFunction
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def translateForcingJet {T : ℝ} (i : Fin 3) (h : ℝ)
    (z : ForcingJet V T) : ForcingJet V T :=
  (pullbackBCF (spatialShiftSlabMap i h) z.1,
   pullbackBCF (spatialShiftPairMap i h) z.2)
/-- The actual translation acts isometrically on the same forcing graph.
No PDE covariance or solution regularity is assumed. -/
theorem forcing_translation_properties (T alpha : ℝ) (i : Fin 3) (h : ℝ) :
    (∀ z : ForcingJet V T,
      translateForcingJet i h z ∈ forcingGraph V T alpha ↔
        z ∈ forcingGraph V T alpha) ∧
    (∀ z : ForcingJet V T, ‖translateForcingJet i h z‖ = ‖z‖) ∧
    (∀ z : ForcingJet V T,
      translateForcingJet i (-h) (translateForcingJet i h z) = z) ∧
    (∀ z w : ForcingJet V T,
      translateForcingJet i h (z + w) =
        translateForcingJet i h z + translateForcingJet i h w) ∧
    (∀ (a : ℝ) (z : ForcingJet V T),
      translateForcingJet i h (a • z) = a • translateForcingJet i h z) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hslabNorm (F : Slab T →ᵇ V) :
      ‖pullbackBCF (spatialShiftSlabMap i h) F‖ = ‖F‖ := by
    apply le_antisymm
    · exact BoundedContinuousFunction.norm_compContinuous_le F (spatialShiftSlabMap i h)
    · calc
        ‖F‖ = ‖pullbackBCF (spatialShiftSlabMap i (-h))
            (pullbackBCF (spatialShiftSlabMap i h) F)‖ := by
              congr 1
              ext p
              simp [pullbackBCF, spatialShiftSlabMap,
                PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint]
        _ ≤ ‖pullbackBCF (spatialShiftSlabMap i h) F‖ :=
          BoundedContinuousFunction.norm_compContinuous_le _ (spatialShiftSlabMap i (-h))
  have hpairNorm (F : Pair T →ᵇ V) :
      ‖pullbackBCF (spatialShiftPairMap i h) F‖ = ‖F‖ := by
    apply le_antisymm
    · exact BoundedContinuousFunction.norm_compContinuous_le F (spatialShiftPairMap i h)
    · calc
        ‖F‖ = ‖pullbackBCF (spatialShiftPairMap i (-h))
            (pullbackBCF (spatialShiftPairMap i h) F)‖ := by
              congr 1
              ext p
              apply congrArg F
              apply Subtype.ext
              apply Prod.ext <;> simp [spatialShiftPairMap,
                PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint]
        _ ≤ ‖pullbackBCF (spatialShiftPairMap i h) F‖ :=
          BoundedContinuousFunction.norm_compContinuous_le _ (spatialShiftPairMap i (-h))
  have hgraphForward (k : ℝ) (z : ForcingJet V T)
      (hz : z ∈ forcingGraph V T alpha) :
      translateForcingJet i k z ∈ forcingGraph V T alpha := by
    intro p
    have h := hz (spatialShiftPairMap i k p)
    have h' : z.2 (spatialShiftPairMap i k p) =
        (parabolicRho
          (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
            p.1.1 i k)
          (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
            p.1.2 i k) ^ alpha)⁻¹ •
          (z.1 (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
            p.1.1 i k) -
           z.1 (PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint
            p.1.2 i k)) := by
      simpa [spatialShiftPairMap] using h
    have hrho := spatialShiftPair_rho i k p
    rw [hrho] at h'
    simpa [translateForcingJet, pullbackBCF, spatialShiftPairMap,
      spatialShiftSlabMap] using h'
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z
    constructor
    · intro hz
      have hback := hgraphForward (-h) (translateForcingJet i h z) hz
      have hinv : translateForcingJet i (-h) (translateForcingJet i h z) = z := by
        ext <;> simp [translateForcingJet, pullbackBCF,
          spatialShiftSlabMap, spatialShiftPairMap,
          PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint]
      simpa [hinv] using hback
    · exact hgraphForward h z
  · intro z
    change max ‖pullbackBCF (spatialShiftSlabMap i h) z.1‖
      ‖pullbackBCF (spatialShiftPairMap i h) z.2‖ = max ‖z.1‖ ‖z.2‖
    rw [hslabNorm, hpairNorm]
  · intro z
    ext <;> simp [translateForcingJet, pullbackBCF, spatialShiftSlabMap,
      spatialShiftPairMap,
      PoincareConjecture.ParallelImplementation.RationalSpatialDifferenceQuotient.shiftPoint]
  · intro z w
    ext p <;> simp [translateForcingJet, pullbackBCF]
  · intro a z
    ext p <;> simp [translateForcingJet, pullbackBCF]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ForcingSpatialTranslation
