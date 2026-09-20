import Mathlib
import LeeSmoothLib.Ch04.Sec04_25.Theorem_4_29
-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; the statement below is aligned with the
-- local quotient-map API for surjective smooth submersions from `Proposition_4_28` and
-- `Theorem_4_29`.

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

/-- Theorem 4.30 (Passing Smoothly to the Quotient): if `π : M → N` is a surjective smooth
submersion with boundaryless source model and `F : M → P` is a smooth map that is constant on
the fibers of `π`, then there exists a unique smooth map `F̃ : N → P` such that
`F̃ ∘ π = F`. -/
theorem existsUnique_contMDiff_lift_of_surjective_smooth_submersion {π : M → N}
    (hπ : IsSmoothSubmersion I J π) (h_surj : Function.Surjective π) {F : M → P}
    (hF : ContMDiff I K ∞ F)
    (hFib : ∀ ⦃x y : M⦄, π x = π y → F x = F y) :
    ∃! F_tilde : N → P, ContMDiff J K ∞ F_tilde ∧ F_tilde ∘ π = F := by
  let proj : C(M, N) := ⟨π, hπ.continuous⟩
  have hq : Topology.IsQuotientMap proj := by
    simpa [proj] using hπ.isQuotientMap h_surj
  let raw : C(M, P) := ⟨F, hF.continuous⟩
  have hfactor : Function.FactorsThrough raw proj := by
    intro x y hxy
    exact hFib hxy
  let F_tilde : N → P := hq.lift raw hfactor
  have hcomp : F_tilde ∘ π = F := by
    funext x
    change ((hq.lift raw hfactor).comp proj) x = raw x
    exact congrArg (fun g : C(M, P) => g x)
      (Topology.IsQuotientMap.lift_comp hq raw hfactor)
  have hsmooth : ContMDiff J K ∞ F_tilde :=
    (contMDiff_iff_comp_of_surjective_smooth_submersion hπ h_surj).mpr (by
      rw [hcomp]
      exact hF)
  refine ⟨F_tilde, ⟨hsmooth, hcomp⟩, ?_⟩
  intro G hG
  funext y
  obtain ⟨x, rfl⟩ := h_surj y
  calc
    G (π x) = F x := congrFun hG.2 x
    _ = F_tilde (π x) := (congrFun hcomp x).symm

end Manifold
