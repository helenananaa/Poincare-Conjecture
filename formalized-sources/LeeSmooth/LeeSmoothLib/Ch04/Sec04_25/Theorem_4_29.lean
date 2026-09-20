import Mathlib
import LeeSmoothLib.Ch04.Sec04_25.Proposition_4_28
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; the statement below is aligned with the
-- local `Manifold.IsSmoothSubmersion` API from `Proposition_4_28`.

open scoped ContDiff Manifold

namespace Manifold

universe uE uE' uE'' uH uH' uH'' uM uN uP

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]
variable {K : ModelWithCorners ℝ E'' H''} [IsManifold K ∞ P]

variable [I.Boundaryless]

/-- Theorem 4.29 (Characteristic Property of Surjective Smooth Submersions): if
`π : M → N` is a surjective smooth submersion whose source model is boundaryless, then a map
`F : N → P` is smooth if and only if `F ∘ π` is smooth. -/
theorem contMDiff_iff_comp_of_surjective_smooth_submersion {π : M → N}
    (hπ : IsSmoothSubmersion I J π) (h_surj : Function.Surjective π) {F : N → P} :
    ContMDiff J K ∞ F ↔ ContMDiff I K ∞ (F ∘ π) := by
  constructor
  · intro hF
    exact hF.comp hπ.contMDiff
  · intro hcomp y
    obtain ⟨x, hx⟩ := h_surj y
    have hsections :
        ∀ x : M,
          ∃ U : TopologicalSpace.Opens N, ∃ hxU : π x ∈ U, ∃ σ : U → M,
            IsSmoothLocalSection I J π U σ ∧ σ ⟨π x, hxU⟩ = x :=
      (smooth_submersion_iff_exists_smooth_local_section_through_every_point
          hπ.contMDiff).mp hπ.surjective_mfderiv
    rcases hsections x with ⟨U, hxU, σ, hσ, -⟩
    have hsmooth : ContMDiff J K ∞ (fun z : U => F z) := by
      have hsmooth' := hcomp.comp hσ.1
      apply hsmooth'.congr
      intro z
      simp only [Function.comp_apply]
      rw [hσ.2 z]
    have hat : ContMDiffAt J K ∞ F (π x) :=
      contMDiffAt_subtype_iff.mp (hsmooth ⟨π x, hxU⟩)
    simpa [hx] using hat

end Manifold
