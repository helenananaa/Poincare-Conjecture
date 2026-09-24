import PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
import PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
abbrev FullJet (T : ℝ) := (HolderJet T × (Slab T →ᵇ E6)) × (Pair T →ᵇ E6)
def fullParabolicJetSet (T alpha : ℝ) (hT : 0 ≤ T) : Set (FullJet T) :=
  {z | z.1.1 ∈ parabolicC2HolderSet T alpha ∧
    (z.1.1.1.1, z.1.2) ∈ slabTimeDerivativeGraph T ∧
    (∀ p : Pair T, z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
      (z.1.2 p.1.1-z.1.2 p.1.2)) ∧
    ∀ x : E3, z.1.1.1.1 (⟨0, le_rfl, hT⟩,x) = 0}
/-- The parabolic graph norm controls real spatial and time derivatives with zero initial trace. -/
theorem full_parabolic_jet_complete (T alpha : ℝ) (hT : 0 ≤ T) (ha : 0 < alpha) :
    IsComplete (fullParabolicJetSet T alpha hT) :=
/- SWARM_PROOF_BEGIN -/
by
  let timeProj (z : FullJet T) :
      (Slab T →ᵇ E6) × (Slab T →ᵇ E6) :=
    (z.1.1.1.1, z.1.2)
  have htimeProj : Continuous timeProj := by
    exact
      (continuous_fst.comp (continuous_fst.comp (continuous_fst.comp continuous_fst))).prodMk
        (continuous_snd.comp continuous_fst)
  have hvalueEval (p : Slab T) : Continuous (fun z : FullJet T => z.1.1.1.1 p) := by
    exact (ContinuousEvalConst.continuous_eval_const p).comp
      (continuous_fst.comp (continuous_fst.comp (continuous_fst.comp continuous_fst)))
  have htimeEval (p : Slab T) : Continuous (fun z : FullJet T => z.1.2 p) := by
    exact (ContinuousEvalConst.continuous_eval_const p).comp
      (continuous_snd.comp continuous_fst)
  have hpairEval (p : Pair T) : Continuous (fun z : FullJet T => z.2 p) := by
    exact (ContinuousEvalConst.continuous_eval_const p).comp continuous_snd
  have hholderClosed : IsClosed (parabolicC2HolderSet T alpha) :=
    (parabolic_C2_holder_jet_complete T alpha ha).1.isClosed
  have htimeClosed : IsClosed (slabTimeDerivativeGraph T) :=
    slab_time_derivative_graph_closed T
  have hparClosed : IsClosed ((fun z : FullJet T => z.1.1) ⁻¹'
      parabolicC2HolderSet T alpha) :=
    hholderClosed.preimage (continuous_fst.comp continuous_fst)
  have hderivClosed : IsClosed ((fun z : FullJet T => timeProj z) ⁻¹'
      slabTimeDerivativeGraph T) := htimeClosed.preimage htimeProj
  have hincrementClosed (p : Pair T) : IsClosed {z : FullJet T |
      z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        (z.1.2 p.1.1-z.1.2 p.1.2)} := by
    apply isClosed_eq
    · exact hpairEval p
    · exact ((htimeEval p.1.1).sub (htimeEval p.1.2)).const_smul
        ((parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹)
  have hinitialClosed (x : E3) : IsClosed {z : FullJet T |
      z.1.1.1.1 (⟨0, le_rfl, hT⟩,x) = 0} := by
    apply isClosed_eq
    · exact hvalueEval (⟨0, le_rfl, hT⟩,x)
    · exact continuous_const
  have hfullClosed : IsClosed (fullParabolicJetSet T alpha hT) := by
    have heq : fullParabolicJetSet T alpha hT =
        ((fun z : FullJet T => z.1.1) ⁻¹' parabolicC2HolderSet T alpha) ∩
          ((fun z : FullJet T => timeProj z) ⁻¹' slabTimeDerivativeGraph T) ∩
          (⋂ p : Pair T, {z : FullJet T |
            z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
              (z.1.2 p.1.1-z.1.2 p.1.2)}) ∩
          (⋂ x : E3, {z : FullJet T |
            z.1.1.1.1 (⟨0, le_rfl, hT⟩,x) = 0}) := by
      ext z
      simp [fullParabolicJetSet, timeProj]
      tauto
    rw [heq]
    exact (((hparClosed.inter hderivClosed).inter (isClosed_iInter hincrementClosed)).inter
      (isClosed_iInter hinitialClosed))
  haveI : CompleteSpace (E3 →L[ℝ] E6) :=
    (SeparatingDual.completeSpace_continuousLinearMap_iff ℝ E3 E6).2 inferInstance
  haveI : CompleteSpace (E3 →L[ℝ] E3 →L[ℝ] E6) :=
    (SeparatingDual.completeSpace_continuousLinearMap_iff ℝ E3
      (E3 →L[ℝ] E6)).2 inferInstance
  haveI : CompleteSpace (HolderJet T) := by infer_instance
  haveI : CompleteSpace (FullJet T) := by infer_instance
  exact hfullClosed.isComplete
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
