import Mathlib
import Shared.MetricGeometry.LengthSpace
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Quantitative.Reference
open Set Function Filter
open scoped BigOperators Topology
/-- **Math.** The real line is a genuine length space for the original metric and path variation. -/
theorem real_line_lengthSpace : Shared.LengthSpace ℝ :=
/- SWARM_PROOF_BEGIN -/
by
  refine ⟨fun x y => le_antisymm ?dist_le_iInf ?iInf_le_dist⟩
  · exact le_iInf fun γ => Shared.LengthSpace.edist_le_pathLength γ
  · -- The straight segment realises the distance, so the infimum of path lengths
    -- is at most `edist x y`.
    refine iInf_le_of_le (Path.segment x y) ?_
    dsimp only [Shared.pathLength]
    -- Reverse paths have the same variation, so it is enough to treat `x ≤ y`.
    have hrev (a b : ℝ) :
        eVariationOn (⇑(Path.segment a b)) univ =
          eVariationOn (⇑(Path.segment b a)) univ := by
      have hσ : AntitoneOn (unitInterval.symm : unitInterval → unitInterval) univ :=
        unitInterval.strictAnti_symm.antitone.antitoneOn _
      have hcoe : (⇑(Path.segment b a) : unitInterval → ℝ) =
          (⇑(Path.segment a b) : unitInterval → ℝ) ∘ unitInterval.symm := by
        ext t
        rw [← Path.segment_symm]
        rfl
      rw [hcoe, eVariationOn.comp_eq_of_antitoneOn _ _ hσ, image_univ,
        range_eq_univ.2 unitInterval.symm_bijective.surjective]
    have hmono_case {a b : ℝ} (hab : a ≤ b) :
        eVariationOn (⇑(Path.segment a b)) univ ≤ edist a b := by
      have hmono : MonotoneOn (⇑(Path.segment a b)) (univ : Set unitInterval) := by
        intro t₁ _ t₂ _ ht
        simpa [Path.segment_apply] using
          AffineMap.lineMap_mono hab (show (t₁ : ℝ) ≤ (t₂ : ℝ) from ht)
      have hI : (univ : Set unitInterval) ∩ Icc (0 : unitInterval) 1 = univ := by
        rw [unitInterval.univ_eq_Icc, inter_self]
      have hle := hmono.eVariationOn_le (mem_univ (0 : unitInterval)) (mem_univ 1)
      rw [hI] at hle
      refine hle.trans_eq ?_
      simp [edist_dist, Real.dist_eq, abs_sub_comm a b, abs_of_nonneg (sub_nonneg.2 hab)]
    rcases le_total x y with hxy | hyx
    · exact hmono_case hxy
    · rw [hrev x y, edist_comm]
      exact hmono_case hyx
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Quantitative.Reference
