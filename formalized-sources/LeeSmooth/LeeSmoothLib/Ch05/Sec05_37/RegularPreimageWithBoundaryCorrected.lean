/-
Verified ordinary-halfspace, positive-dimensional version of Problem 5.23.
The broader legacy statement is retained separately in Problem_5_23.lean.
This companion does not assert the arbitrary-corners or zero-dimensional cases.
-/
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothEmbedding
import LeeSmoothLib.Ch01.Sec01_05.Definition_1_5_extra_1
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_2
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_4
import LeeSmoothLib.Ch05.Sec05_37.InteriorRegularPreimageChart
-- Declarations for this item will be appended below by the statement pipeline.

/-
open Set
open scoped ContDiff Manifold

noncomputable section

namespace Manifold

universe uE uE' uH uH' uM uN

section RegularValue

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}

/-- A point `c` is a regular value of the boundary restriction `F|_{∂M}` when the derivative of
`F` along the boundary subset is surjective at every boundary point of the fiber `F⁻¹({c})`. This
is the intrinsic boundary-restriction form of Lee's boundary regular-value hypothesis. -/
def IsBoundaryRegularValue (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ E' H')
    (F : M → N) (c : N) : Prop :=
  ∀ x : I.boundary M, F x = c →
    Function.Surjective (mfderivWithin I J F (I.boundary M) x)

/-- A boundary regular value is characterized by surjectivity of the derivative of `F` within the
boundary along the boundary fiber. -/
theorem isBoundaryRegularValue_iff (F : M → N) (c : N) :
    IsBoundaryRegularValue I J F c ↔
      ∀ x : M, x ∈ I.boundary M → F x = c →
        Function.Surjective (mfderivWithin I J F (I.boundary M) x) := by
  constructor
  · intro h x hx hFx
    exact h ⟨x, hx⟩ hFx
  · intro h x hFx
    exact h x x.2 hFx

end RegularValue

section RegularPreimageWithBoundary

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J (⊤ : WithTop ℕ∞) N]
variable [BoundarylessManifold J N]

local notation "ambientDim" => Module.finrank ℝ E
local notation "levelDim" =>
  Module.finrank ℝ E - Module.finrank ℝ E'

/-- Helper for Problem 5-23: the intrinsic boundary-regular-value hypothesis can be used directly
at ordinary ambient points of the boundary fiber. -/
lemma boundary_regular_value_pointwise
    {F : M → N} {c : N}
    (hBoundary : IsBoundaryRegularValue I J F c) :
    ∀ x : M, x ∈ I.boundary M → F x = c →
      Function.Surjective (mfderivWithin I J F (I.boundary M) x) := by
  -- Rewrite the boundary-restriction hypothesis into the pointwise ambient form needed later.
  exact (isBoundaryRegularValue_iff (I := I) (J := J) F c).1 hBoundary

/-- Helper for Problem 5-23: once interior fiber points admit slice charts and boundary fiber
points admit half-slice charts, the whole regular fiber satisfies the chapter's local
slice-with-boundary condition. -/
lemma regular_fiber_satisfies_local_slice_condition_with_boundary
    {F : M → N} {c : N}
    [ChartedSpace (EuclideanSpace ℝ (Fin ambientDim)) M]
    [IsManifold (𝓡 ambientDim) (⊤ : WithTop ℕ∞) M]
    (hInterior :
      ∀ x : M, x ∈ F ⁻¹' {c} → x ∉ I.boundary M →
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin ambientDim)),
          x ∈ e.source ∧ e.IsSliceChart (F ⁻¹' {c}) levelDim)
    (hBoundary :
      ∀ x : M, x ∈ F ⁻¹' {c} → x ∈ I.boundary M →
        ∃ e : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin ambientDim)),
          x ∈ e.source ∧ e.IsBoundarySliceChart (F ⁻¹' {c}) levelDim) :
    Set.SatisfiesLocalSliceConditionWithBoundary ambientDim (F ⁻¹' {c}) levelDim := by
  refine ⟨?_⟩
  intro x hx
  -- Split exactly as in Lee's proof: ambient interior points use ordinary slices,
  -- ambient boundary points use half-slices.
  by_cases hxBoundary : x ∈ I.boundary M
  · rcases hBoundary x hx hxBoundary with ⟨e, hxsource, he⟩
    exact ⟨e, hxsource, Or.inr he⟩
  · rcases hInterior x hx hxBoundary with ⟨e, hxsource, he⟩
    exact ⟨e, hxsource, Or.inl he⟩

/-- Helper for Problem 5-23: the empty fiber carries the canonical smooth manifold-with-boundary
structure, and its inclusion into the ambient manifold is a smooth embedding. -/
theorem empty_subtype_smooth_manifold_with_boundary_structure_into
    (k : ℕ) :
    ∃ _ : SmoothManifoldWithBoundary k (∅ : Set M),
      IsSmoothEmbedding
        (leeBoundaryModelWithCorners k)
        I
        ∞
        ((↑) : (∅ : Set M) → M) := by
  letI : IsEmpty (∅ : Set M) := inferInstance
  letI : ChartedSpace (ℍ^{k}) (∅ : Set M) := ChartedSpace.empty _ _
  have hTopological : IsManifold (leeBoundaryModelWithCorners k) (0 : WithTop ℕ∞) (∅ : Set M) := by
    -- The empty atlas has no chart overlaps, so the `C^0` compatibility condition is vacuous.
    refine isManifold_of_contDiffOn (leeBoundaryModelWithCorners k) (0 : WithTop ℕ∞)
      (∅ : Set M) ?_
    intro e e' he he'
    have hFalse : False := by
      change e ∈ (∅ : Set (OpenPartialHomeomorph (∅ : Set M) (ℍ^{k}))) at he
      simp at he
    exact False.elim hFalse
  have hSmooth :
      IsManifold (leeBoundaryModelWithCorners k) (⊤ : WithTop ℕ∞) (∅ : Set M) := by
    -- The same empty-atlas argument upgrades immediately to smooth compatibility.
    refine isManifold_of_contDiffOn (leeBoundaryModelWithCorners k) (⊤ : WithTop ℕ∞)
      (∅ : Set M) ?_
    intro e e' he he'
    have hFalse : False := by
      change e ∈ (∅ : Set (OpenPartialHomeomorph (∅ : Set M) (ℍ^{k}))) at he
      simp at he
    exact False.elim hFalse
  let hBoundary : SmoothManifoldWithBoundary k (∅ : Set M) :=
    { toTopologicalManifoldWithBoundary :=
        { toT2Space := inferInstance
          toSecondCountableTopology := inferInstance
          toChartedSpace := inferInstance
          toIsManifold := hTopological }
      smooth := hSmooth }
  refine ⟨hBoundary, ?_⟩
  let _ : SmoothManifoldWithBoundary k (∅ : Set M) := hBoundary
  refine ⟨?_, ⟨Topology.IsInducing.subtypeVal, Subtype.val_injective⟩⟩
  -- Every chart-level condition for the empty inclusion is vacuous.
  exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ False.elim x.2⟩

/-- Problem 5-23: if `M` is a smooth manifold with boundary, `N` is a smooth boundaryless
manifold, `F` is smooth, `c` is a regular value of `F`, and the boundary restriction `F | ∂M`
has `c` as a regular value in the intrinsic boundary sense, then the level set `F⁻¹({c})` carries
the canonical owner
`SmoothManifoldWithBoundary levelDim (F ⁻¹' {c})`, its subtype inclusion into `M` is a smooth
embedding, and its boundary maps onto `F⁻¹({c}) ∩ ∂M`. -/
theorem regular_preimage_has_embedded_submanifold_with_boundary_structure
    {F : M → N} {c : N} (hF : ContMDiff I J ∞ F) (hc : IsRegularValue I J F c)
    (hBoundary : IsBoundaryRegularValue I J F c) :
    ∃ _ : SmoothManifoldWithBoundary levelDim (F ⁻¹' {c}),
        IsSmoothEmbedding
            (leeBoundaryModelWithCorners levelDim)
            I
            ∞
            ((↑) : (F ⁻¹' {c}) → M) ∧
          ((↑) : (F ⁻¹' {c}) → M) '' (leeBoundaryModelWithCorners levelDim).boundary (F ⁻¹' {c}) =
            (F ⁻¹' {c}) ∩ I.boundary M := by
  let S : Set M := F ⁻¹' {c}
  have hBoundary' :
      ∀ x : M, x ∈ I.boundary M → F x = c →
        Function.Surjective (mfderivWithin I J F (I.boundary M) x) :=
    boundary_regular_value_pointwise (I := I) (J := J) hBoundary
  by_cases hEmpty : S = ∅
  · have hSEmpty : F ⁻¹' {c} = ∅ := by
      simpa [S] using hEmpty
    rw [hSEmpty]
    rcases
        empty_subtype_smooth_manifold_with_boundary_structure_into
          (M := M) (I := I) levelDim with
      ⟨hEmptyBoundary, hEmptyEmb⟩
    refine ⟨hEmptyBoundary, hEmptyEmb, ?_⟩
    -- Both sides are empty once the fiber itself is empty.
    ext x
    simp
  · have hNonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    -- Route correction: the source proof still splits into ambient interior points and ambient
    -- boundary points, but the available local-slice-with-boundary API is formulated only for a
    -- boundaryless Euclidean ambient model.
    -- TODO: construct a boundary-aware replacement for the missing ambient API: from `hc` and
    -- `hBoundary'`, build local interior slice charts and boundary half-slice charts for points of
    -- `S`, then package them directly into the subtype `SmoothManifoldWithBoundary` structure and
    -- prove that its boundary maps to `S ∩ I.boundary M`.
    let _hUnusedF := hF
    let _hUnusedRegular := hc
    let _hUnusedBoundary := hBoundary'
    let _hUnusedNonempty := hNonempty
    let _S := S
    sorry

end RegularPreimageWithBoundary

end Manifold

-/

open Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Manifold

universe uM uN

open InteriorRegularPreimageChart BoundaryRegularPreimageChart

/-!
## Corrected explicit half-space theorem

The theorem below is intentionally stated for ordinary finite-dimensional real manifolds modeled on
the standard half-space and Euclidean space, with explicit separation and countability instances.
Its boundary hypothesis is the intrinsic tangential surjectivity predicate from
`BoundaryRegularValueCore`; no family of target charts is assumed.
-/

theorem regular_preimage_has_cInfinity_halfspace_structure_with_boundary
    {n m : ℕ} (hmn : m ≤ n)
    {M : Type uM} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
      [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
      [IsManifold (𝓡∂ (n + 1)) ∞ M]
    {N : Type uN} [TopologicalSpace N] [T2Space N] [SecondCountableTopology N]
      [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
      [IsManifold (𝓡 m) ∞ N]
    {F : M → N} {c : N}
    (hF : ContMDiff (𝓡∂ (n + 1)) (𝓡 m) ∞ F)
    (hc : IsRegularValue (𝓡∂ (n + 1)) (𝓡 m) F c)
    (hBoundary : IsBoundaryRegularValue n m F c) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace ((n - m) + 1)) (F ⁻¹' {c}),
      ∃ hs : IsManifold (𝓡∂ ((n - m) + 1)) ∞ (F ⁻¹' {c}),
        let _ : ChartedSpace (EuclideanHalfSpace ((n - m) + 1)) (F ⁻¹' {c}) := cs
        let _ : IsManifold (𝓡∂ ((n - m) + 1)) ∞ (F ⁻¹' {c}) := hs
        IsSmoothEmbedding (𝓡∂ ((n - m) + 1)) (𝓡∂ (n + 1)) ∞
            ((↑) : (F ⁻¹' {c}) → M) ∧
          ((↑) : (F ⁻¹' {c}) → M) ''
              (𝓡∂ ((n - m) + 1)).boundary (F ⁻¹' {c}) =
            (F ⁻¹' {c}) ∩ (𝓡∂ (n + 1)).boundary M := by
  classical
  let S : Set M := F ⁻¹' {c}
  let localChart : S →
      CInfinityNeatSliceChart (d := n) (k := n - m) (q := m) S := fun x ↦
    dite (x.1 ∈ (𝓡∂ (n + 1)).boundary M)
      (fun hxBoundary ↦
        Classical.choose
          (BoundaryRegularPreimageChart.exists_boundary_cInfinityNeatSliceChart
            (hmn := hmn) (hF := hF) (hpBoundary := hxBoundary)
            (hFp := x.2) (hA := hBoundary x.1 hxBoundary x.2)))
      (fun hxInterior ↦
        interiorRegularPreimageChart hmn hF
          (((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint x.1).2
            (by change ¬(𝓡∂ (n + 1)).IsBoundaryPoint x.1; exact hxInterior))
          x.2 (hc x.1 x.2))
  let D : CInfinityNeatSliceFamily (d := n) (k := n - m) (q := m) S :=
    { localChart := localChart
      mem_ambient_source := by
        intro x
        by_cases hxBoundary : x.1 ∈ (𝓡∂ (n + 1)).boundary M
        · simp [localChart, hxBoundary]
          exact Classical.choose_spec
            (BoundaryRegularPreimageChart.exists_boundary_cInfinityNeatSliceChart
              (hmn := hmn) (hF := hF) (hpBoundary := hxBoundary)
              (hFp := x.2) (hA := hBoundary x.1 hxBoundary x.2))
        · simp [localChart, hxBoundary]
          exact interiorRegularPreimageChart_mem_source hmn hF
            (((𝓡∂ (n + 1)).isInteriorPoint_iff_not_isBoundaryPoint x.1).2
              (by change ¬(𝓡∂ (n + 1)).IsBoundaryPoint x.1; exact hxBoundary))
            x.2 (hc x.1 x.2) }
  simpa [S] using
    (CInfinityNeatSliceFamily.exists_structure_of_neatSliceFamily D)

end Manifold
