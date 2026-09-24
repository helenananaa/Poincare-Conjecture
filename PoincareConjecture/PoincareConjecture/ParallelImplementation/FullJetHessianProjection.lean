import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetHessianProjection
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_full_jet_hessian_projection (T alpha : ℝ) (hT : 0 ≤ T) :
    ∃ H : FullJet T →L[ℝ] ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T,
      ‖H‖ ≤ 1 ∧
      (∀ z p, (H z).1 p = z.1.1.1.2.2 p) ∧
      (∀ z p, (H z).2 p = z.1.1.2 p) ∧
      ∀ z ∈ fullParabolicJetSet T alpha hT,
        H z ∈ forcingGraph (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha :=
/- SWARM_PROOF_BEGIN -/
by
  let L0 : FullJet T →ₗ[ℝ]
      ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T := {
    toFun := fun z => (z.1.1.1.2.2, z.1.1.2)
    map_add' := by
      intro z w
      apply Prod.ext <;> simp
    map_smul' := by
      intro c z
      apply Prod.ext <;> simp
  }
  have hbound (z : FullJet T) : ‖L0 z‖ ≤ 1 * ‖z‖ := by
    have hfirst : ‖z.1.1.1.2.2‖ ≤ ‖z‖ :=
      (norm_snd_le z.1.1.1.2).trans ((norm_snd_le z.1.1.1).trans
        ((norm_fst_le z.1.1).trans ((norm_fst_le z.1).trans (norm_fst_le z))))
    have hsecond : ‖z.1.1.2‖ ≤ ‖z‖ :=
      (norm_snd_le z.1.1).trans ((norm_fst_le z.1).trans (norm_fst_le z))
    change max ‖z.1.1.1.2.2‖ ‖z.1.1.2‖ ≤ 1 * ‖z‖
    apply max_le
    · simpa only [one_mul] using hfirst
    · simpa only [one_mul] using hsecond
  let L : FullJet T →L[ℝ] ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T :=
    L0.mkContinuous 1 hbound
  refine ⟨L, LinearMap.mkContinuous_norm_le _ (by norm_num) hbound, ?_, ?_, ?_⟩
  · intro z p
    rfl
  · intro z p
    rfl
  · intro z hz p
    exact hz.1.2 p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetHessianProjection
