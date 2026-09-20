import LeeSmoothLib.Ch04.Sec04_26.Proposition_4_41
import LeeSmoothLib.Ch04.Sec04_26.Corollary_4_43
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff unitInterval
open Topology

universe uM uMtilde uM'

section

variable {n : ℕ}
variable {M : Type uM} [TopologicalSpace M] [SmoothManifoldWithBoundary n M]
variable [ConnectedSpace M]

local notation "I" => leeBoundaryModelWithCorners n

/-- Fixed-endpoint path-homotopy classes are countable: the compact-open path space is second
countable, its homotopy quotient is separable, and semilocal simple connectivity makes that
quotient discrete. -/
private theorem exercise_4_45_countable_pathHomotopyQuotient
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [TauCeti.SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X] (x y : X) :
    Countable (Path.Homotopic.Quotient x y) := by
  letI : SecondCountableTopology C(unitInterval, X) := inferInstance
  letI : SecondCountableTopology (Path x y) :=
    TopologicalSpace.secondCountableTopology_induced
      (Path x y) C(unitInterval, X) ((↑) : Path x y → C(unitInterval, X))
  letI : TopologicalSpace.SeparableSpace (Path.Homotopic.Quotient x y) :=
    (show IsQuotientMap
      (Path.Homotopic.Quotient.mk : Path x y → Path.Homotopic.Quotient x y) from
      isQuotientMap_quotient_mk').separableSpace
  exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance

/-- Every standard sheet in the based-path cover is second countable because the endpoint
projection restricts to a homeomorphism from that sheet to its open base neighborhood. -/
private theorem exercise_4_45_secondCountableTopology_sheet
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [TauCeti.SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {x₀ x : X} (U : Set X) (hUopen : IsOpen U) (hxU : x ∈ U)
    (hUpath : IsPathConnected U) (hUtrivial : IsPathHomotopyTrivial U)
    (q : Path.Homotopic.Quotient x₀ x) :
    SecondCountableTopology (TauCeti.UniversalCover.sheet U hxU q) := by
  let S := TauCeti.UniversalCover.sheet (x₀ := x₀) U hxU q
  let f : S → U := fun z ↦
    ⟨TauCeti.UniversalCover.proj z.1,
      TauCeti.UniversalCover.sheet_subset_proj_preimage U hxU q z.2⟩
  have hfbij : Function.Bijective f := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply TauCeti.UniversalCover.proj_injOn_sheet hUtrivial hxU q a.2 b.2
      exact congrArg Subtype.val hab
    · intro y
      obtain ⟨z, hzS, hz⟩ :=
        TauCeti.UniversalCover.proj_surjOn_sheet hUpath hxU q y.2
      exact ⟨⟨z, hzS⟩, Subtype.ext hz⟩
  have hfcont : Continuous f := by
    exact ((TauCeti.UniversalCover.continuous_proj x₀).comp continuous_subtype_val).subtype_mk _
  have hfopen : IsOpenMap f := by
    exact ((TauCeti.UniversalCover.isOpenMap_proj x₀).restrict
      (TauCeti.UniversalCover.isOpen_sheet U hUopen hxU q)).subtype_mk _
  let e : S ≃ₜ U := (Equiv.ofBijective f hfbij).toHomeomorphOfContinuousOpen hfcont hfopen
  exact e.secondCountableTopology

/-- The based-path universal cover of a second-countable, locally path-connected, semilocally
simply connected space is second countable.  A countable family of good base neighborhoods is
chosen first; over each one the cover is a countable union of second-countable sheets. -/
private theorem exercise_4_45_universalCover_secondCountableTopology
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [TauCeti.SemilocallySimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (x₀ : X) : SecondCountableTopology (TauCeti.UniversalCover x₀) := by
  choose U hUopen hxU hUpath hUtrivial using
    fun x : X ↦ exists_isOpen_mem_isPathConnected_isPathHomotopyTrivial x
  obtain ⟨s, hscount, hscover⟩ :=
    TopologicalSpace.countable_cover_nhds
      (fun x ↦ (hUopen x).mem_nhds (hxU x))
  let ι := Σ x : s, Path.Homotopic.Quotient x₀ x.1
  let W : ι → Set (TauCeti.UniversalCover x₀) := fun i ↦
    TauCeti.UniversalCover.sheet (U i.1.1) (hxU i.1.1) i.2
  letI : Countable s := hscount.to_subtype
  letI (x : s) : Countable (Path.Homotopic.Quotient x₀ x.1) :=
    exercise_4_45_countable_pathHomotopyQuotient x₀ x.1
  letI : Countable ι := inferInstance
  letI : ∀ i : ι, SecondCountableTopology (W i) := fun i ↦
    exercise_4_45_secondCountableTopology_sheet
      (U i.1.1) (hUopen i.1.1) (hxU i.1.1)
      (hUpath i.1.1) (hUtrivial i.1.1) i.2
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (U := W)
  · intro i
    exact TauCeti.UniversalCover.isOpen_sheet
      (U i.1.1) (hUopen i.1.1) (hxU i.1.1) i.2
  · apply Set.eq_univ_of_forall
    intro z
    have hzbase : TauCeti.UniversalCover.proj z ∈ ⋃ x ∈ s, U x := by
      rw [hscover]
      exact Set.mem_univ _
    simp only [Set.mem_iUnion] at hzbase
    obtain ⟨x, hxs, hzxU⟩ := hzbase
    have hzsheets := TauCeti.UniversalCover.sheet_exhaustive
      (x₀ := x₀) (x := x) (hUpath x) (hxU x) hzxU
    simp only [Set.mem_iUnion] at hzsheets
    obtain ⟨q, hzq⟩ := hzsheets
    exact Set.mem_iUnion.2 ⟨⟨⟨x, hxs⟩, q⟩, hzq⟩

-- Semantic Lean search tool unavailable in this environment (`lean_leansearch` not present in
-- tool discovery); verified directly against `Corollary_4_43.lean` and `Proposition_4_41.lean`.
/-- Exercise 4.45: every connected smooth manifold with boundary admits a universal smooth
covering map from a simply connected smooth manifold with boundary, and any other simply
connected smooth covering of the same base is diffeomorphic to it over the base. -/
theorem exists_universal_smooth_covering_manifold_with_boundary
    : ∃ (Mtilde : Type uM) (_ : TopologicalSpace Mtilde)
      (_ : SmoothManifoldWithBoundary n Mtilde) (π : Mtilde → M),
      Manifold.IsUniversalSmoothCoveringMap I I π ∧
        ∀ {M' : Type uM'} [TopologicalSpace M'] [SmoothManifoldWithBoundary n M']
          (π' : M' → M),
          Manifold.IsUniversalSmoothCoveringMap I I π' →
            ∃ Φ : Diffeomorph I I Mtilde M' (∞ : WithTop ℕ∞), π' ∘ Φ = π := by
  letI : StronglyLocallyContractibleSpace M :=
    corollary_4_43_stronglyLocallyContractibleSpace (leeBoundaryModelWithCorners n)
  letI : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let x₀ : M := Classical.arbitrary M
  let Mtilde : Type uM := TauCeti.UniversalCover x₀
  let π : Mtilde → M := TauCeti.UniversalCover.proj
  have hcover : IsCoveringMap π := TauCeti.UniversalCover.isCoveringMap x₀
  have hsurj : Function.Surjective π := by
    intro x
    let p : Path x₀ x := PathConnectedSpace.somePath x₀ x
    refine ⟨TauCeti.UniversalCover.ofBasedPath x₀ (BasedPath.ofPath p), ?_⟩
    simpa [π] using
      (TauCeti.UniversalCover.proj_ofBasedPath x₀ (BasedPath.ofPath p))
  letI : SecondCountableTopology Mtilde :=
    exercise_4_45_universalCover_secondCountableTopology x₀
  letI : SimplyConnectedSpace Mtilde :=
    TauCeti.UniversalCover.simplyConnectedSpace x₀
  obtain ⟨s, hsmooth⟩ :=
    exists_smooth_boundary_covering_structure (n := n) (π := π) hcover hsurj
  letI : SmoothManifoldWithBoundary n Mtilde := s
  have huniversal : Manifold.IsUniversalSmoothCoveringMap I I π :=
    ⟨hsmooth, inferInstance⟩
  refine ⟨Mtilde, inferInstance, s, π, huniversal, ?_⟩
  intro M' _ _ π' hπ'
  exact exists_diffeomorph_of_universal_smooth_covering_maps π huniversal π' hπ'

end


#print axioms exists_universal_smooth_covering_manifold_with_boundary
