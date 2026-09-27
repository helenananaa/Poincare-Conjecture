import PoincareConjecture.ProofContract.Refinement20260927.EmbeddedNormalFrames
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedNormalParametrizationRegularity
open PoincareConjecture.ProofContract.Refinement20260927
theorem normal_parametrization_regularity : NormalParametrizationRegularityStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro N n e p F h r
  constructor
  · rw [r.target_eq]
    let fst : NormalSplit F.linear →L[ℝ] NormalTangent :=
      ContinuousLinearMap.fst ℝ _ _
    let snd : NormalSplit F.linear →L[ℝ] NormalFiber F.linear :=
      ContinuousLinearMap.snd ℝ _ _
    let snd' : NormalSplit F.linear →L[ℝ] ApproxAmbient n :=
      (NormalFiber F.linear).subtypeL.comp snd
    have hfst : Set.MapsTo (fun z => fst z) (F.baseChart.target ×ˢ Set.univ) F.baseChart.target := by
      intro z hz
      exact hz.1
    have he : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : NormalSplit F.linear => e.map (F.baseChart.symm z.1))
        (F.baseChart.target ×ˢ Set.univ) := by
      have hcomp := F.smooth_embedding.comp fst.contDiff.contDiffOn hfst
      exact hcomp.congr (by intro z hz; simp [fst])
    have hfwd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : NormalSplit F.linear => normalFrameForward F (F.baseChart.symm z.1))
        (F.baseChart.target ×ˢ Set.univ) := by
      have hcomp := h.smooth_forward.comp fst.contDiff.contDiffOn hfst
      exact hcomp.congr (by intro z hz; simp [fst])
    have hsnd0 : ContDiffOn ℝ ⊤
        (fun z : NormalSplit F.linear => snd' z)
        (F.baseChart.target ×ˢ Set.univ) :=
      snd'.contDiff.contDiffOn (s := F.baseChart.target ×ˢ Set.univ)
    have hsnd : ContDiffOn ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : NormalSplit F.linear => (z.2 : ApproxAmbient n))
        (F.baseChart.target ×ˢ Set.univ) :=
      (hsnd0.of_le (show (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≤ ⊤ from le_top)).congr
        (by intro z hz; rfl)
    have hterm := hfwd.clm_apply hsnd
    have hadd := he.add hterm
    exact hadd.congr (by intro z hz; rfl)
  · rw [r.target_eq]
    let fst : NormalSplit F.linear →L[ℝ] NormalTangent :=
      ContinuousLinearMap.fst ℝ _ _
    have hfst : Set.MapsTo (fun z => fst z) (F.baseChart.target ×ˢ Set.univ) F.baseChart.target := by
      intro z hz
      exact hz.1
    have hcomp := F.smooth_base_inverse.comp
      (fst.contMDiff.contMDiffOn (s := F.baseChart.target ×ˢ Set.univ))
      (by
        intro z hz
        exact hz.1)
    have heq : Set.EqOn (fun z : NormalSplit F.linear => ((r.chart.symm z).val).1)
        (fun z => F.baseChart.symm (fst z))
        (F.baseChart.target ×ˢ Set.univ) := by
      intro z hz
      simpa [fst] using (r.inverse_base z (by simpa [r.target_eq] using hz))
    exact hcomp.congr heq
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedNormalParametrizationRegularity
