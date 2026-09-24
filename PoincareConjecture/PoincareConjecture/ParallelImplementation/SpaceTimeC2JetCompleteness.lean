import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.BoundedC2JetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open Set
open scoped Topology ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
abbrev Slab (T : ℝ) := Set.Icc (0:ℝ) T × E3
abbrev Jet (T : ℝ) := (Slab T →ᵇ E6) ×
  ((Slab T →ᵇ (E3 →L[ℝ] E6)) × (Slab T →ᵇ (E3 →L[ℝ] E3 →L[ℝ] E6)))
/-- **Math.** Jointly continuous bounded jets with actual spatial derivative relations. -/
def spaceTimeC2JetSet (T : ℝ) : Set (Jet T) :=
  {z | ∀ t : Set.Icc (0:ℝ) T,
    (∀ x : E3, HasFDerivAt (fun y => z.1 (t,y)) (z.2.1 (t,x)) x) ∧
    (∀ x : E3, HasFDerivAt (fun y => z.2.1 (t,y)) (z.2.2 (t,x)) x)}
/-- **Math.** Spatial jet relations are closed under uniform space-time limits. -/
theorem spaceTime_C2_jet_complete (T : ℝ) :
    IsComplete (spaceTimeC2JetSet T) ∧
      ∀ z ∈ spaceTimeC2JetSet T, ∀ t : Set.Icc (0:ℝ) T,
        ContDiff ℝ 2 (fun x : E3 => z.1 (t,x)) :=
/- SWARM_PROOF_BEGIN -/
by
  let slice (t : Set.Icc (0 : ℝ) T) : ContinuousMap E3 (Slab T) :=
    ⟨fun x => (t, x), continuous_const.prodMk continuous_id⟩
  let sliceJet (t : Set.Icc (0 : ℝ) T) (z : Jet T) :=
    (z.1.compContinuous (slice t),
      (z.2.1.compContinuous (slice t), z.2.2.compContinuous (slice t)))
  have hslice_cont (t : Set.Icc (0 : ℝ) T) : Continuous (sliceJet t) := by
    exact
      ((BoundedContinuousFunction.continuous_compContinuous (slice t)).comp
          continuous_fst).prodMk
        (((BoundedContinuousFunction.continuous_compContinuous (slice t)).comp
              (continuous_fst.comp continuous_snd)).prodMk
          ((BoundedContinuousFunction.continuous_compContinuous (slice t)).comp
              (continuous_snd.comp continuous_snd)))
  have hjet := MorganTianLib.MetricCoefficient.bounded_C2_jet_completeness E6
  have hclosed : IsClosed (MorganTianLib.MetricCoefficient.boundedC2JetSet E6) :=
    hjet.1.isClosed
  have hclosedSpace : IsClosed (spaceTimeC2JetSet T) := by
    have heq : spaceTimeC2JetSet T =
        ⋂ t : Set.Icc (0 : ℝ) T,
          (sliceJet t) ⁻¹' MorganTianLib.MetricCoefficient.boundedC2JetSet E6 := by
      ext z
      simp [spaceTimeC2JetSet, sliceJet, slice,
        MorganTianLib.MetricCoefficient.boundedC2JetSet]
    rw [heq]
    exact isClosed_iInter fun t => hclosed.preimage (hslice_cont t)
  refine ⟨hclosedSpace.isComplete, ?_⟩
  intro z hz t
  have hzSlice : sliceJet t z ∈ MorganTianLib.MetricCoefficient.boundedC2JetSet E6 := by
    simpa [spaceTimeC2JetSet, sliceJet, slice,
      MorganTianLib.MetricCoefficient.boundedC2JetSet] using hz t
  simpa [sliceJet, slice] using hjet.2 (sliceJet t z) hzSlice
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
