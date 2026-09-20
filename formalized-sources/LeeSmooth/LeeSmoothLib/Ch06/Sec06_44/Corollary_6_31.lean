import LeeSmoothLib.Ch06.Sec06_44.Theorem_6_30

/-!
# Corollary 6.31, genuine C∞ submersion preimage

The original statement returned `IsEmbeddedSubmanifold`, whose inclusion field is outer-top
(`ω`, analytic).  A smooth submersion need only cut out a C∞ embedded preimage of an analytic
embedded target: the graph of the standard flat function
`x ↦ if x ≤ 0 then 0 else exp (-1 / x)` is a smooth embedded curve, not an analytic submanifold.
The corrected theorem therefore returns the C∞ bundle
`ChartedSpace` + `IsManifold ∞` + `IsSmoothEmbedding ∞`.

Codimension arithmetic on an empty source is `Nat` subtraction.  A nonempty source supplies the
bound `codimension ≤ source dimension` from surjectivity of the submersion derivative; an empty
source needs that numerical inequality explicitly.
-/

open scoped ContDiff Manifold

section SubmersionPreimages

universe uEN uEM uES uHN uHM uHS uN uM

open Manifold

variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace ℝ EN] [FiniteDimensional ℝ EN]
variable {EM : Type uEM} [NormedAddCommGroup EM] [NormedSpace ℝ EM] [FiniteDimensional ℝ EM]
variable {ES : Type uES} [NormedAddCommGroup ES] [NormedSpace ℝ ES] [FiniteDimensional ℝ ES]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HM : Type uHM} [TopologicalSpace HM]
variable {HS : Type uHS} [TopologicalSpace HS]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace HN N]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace HM M]
variable {IN : ModelWithCorners ℝ EN HN} [IsManifold IN ∞ N]
variable {IM : ModelWithCorners ℝ EM HM} [IsManifold IM ∞ M]
variable {S : Set M}
variable {K : ModelWithCorners ℝ ES HS}
variable [ChartedSpace HS S] [IsManifold K ∞ S]

omit [IsManifold IN ∞ N] [IsManifold IM ∞ M] [IsManifold K ∞ S] in
/-- If the source is nonempty, a smooth submersion forces the target's embedded-submanifold
codimension to fit in the source dimension.  This does not require a nonempty preimage. -/
lemma submersion_codimension_le_source_finrank
    {F : N → M} (hF : IsSmoothSubmersion IN IM F)
    (hS : IsEmbeddedSubmanifold IM K S)
    (hN : Nonempty N) :
    hS.codimension ≤ Module.finrank ℝ EN := by
  obtain ⟨p⟩ := hN
  letI : FiniteDimensional ℝ (TangentSpace IN p) :=
    inferInstanceAs (FiniteDimensional ℝ EN)
  letI : FiniteDimensional ℝ (TangentSpace IM (F p)) :=
    inferInstanceAs (FiniteDimensional ℝ EM)
  have hsurj := hF.surjective_mfderiv p
  have hdim := LinearMap.finrank_le_finrank_of_surjective hsurj
  change Module.finrank ℝ EM ≤ Module.finrank ℝ EN at hdim
  have hcodim : hS.codimension ≤ Module.finrank ℝ EM := by
    simp only [IsEmbeddedSubmanifold.codimension]
    exact Nat.sub_le _ _
  exact hcodim.trans hdim

/-- Corollary 6.31, C∞ form: if `S ⊆ M` is an embedded submanifold and `F : N → M` is a smooth
submersion, then `F ⁻¹' S` carries a C∞ embedded submanifold structure in `N` whose model
dimension is `dim N - codim S`.

The disjunction records the empty-source edge case: a nonempty source derives the rank bound
from the submersion derivative, while an empty source must supply
`codimension ≤ source dimension` so that `Nat` subtraction does not silently collapse. -/
theorem smooth_submersion_preimage_has_embedded_submanifold_structure
    [IN.Boundaryless] [T2Space N] [SecondCountableTopology N]
    {F : N → M} (hF : IsSmoothSubmersion IN IM F)
    (hS : IsEmbeddedSubmanifold IM K S)
    (hcod : hS.codimension ≤ Module.finrank ℝ EN ∨ Nonempty N) :
    let T : Set N := F ⁻¹' S
    let L :=
      modelWithCornersSelf ℝ
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ EN - hS.codimension)))
    ∃ cs : ChartedSpace
        (EuclideanSpace ℝ (Fin (Module.finrank ℝ EN - hS.codimension))) T,
      ∃ hs : IsManifold L ∞ T,
        let _ : ChartedSpace
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ EN - hS.codimension))) T := cs
        let _ : IsManifold L ∞ T := hs
        IsSmoothEmbedding L IN ∞ (Subtype.val : T → N) := by
  let _ : IsEmbeddedSubmanifold IM K S := hS
  have hbound : hS.codimension ≤ Module.finrank ℝ EN :=
    hcod.elim id (submersion_codimension_le_source_finrank hF hS)
  exact
    transverse_preimage_has_embedded_submanifold_structure
      (Manifold.IsSmoothSubmersion.isTransverseToSubmanifold hF) hbound

end SubmersionPreimages
