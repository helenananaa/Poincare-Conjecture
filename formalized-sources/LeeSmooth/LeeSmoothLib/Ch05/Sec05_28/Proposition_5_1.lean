import Mathlib.Geometry.Manifold.Instances.Real
import LeeSmoothLib.Ch01.Sec01_04.Example_1_26
import LeeSmoothLib.Ch04.Sec04_22.Proposition_4_8
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

-- `lean_leansearch` was unavailable in this session; local precedent here uses the chapter owner
-- `IsEmbeddedSubmanifold` together with `IsEmbeddedSubmanifold.codimension`.

open TopologicalSpace
open scoped ContDiff Manifold
open Manifold

universe u

noncomputable section

variable {n k : ℕ} {M : Type u} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) M]

/-- The underlying subtype of an open subset carries the canonical restricted charted-space
structure. -/
instance instChartedSpaceUnderlyingOpenSet (U : Opens M) :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) ((U : Set M)) :=
  (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin n)) U)

/-- The underlying subtype of an open subset of a smooth manifold carries the canonical inherited
smooth structure. -/
instance instIsManifoldUnderlyingOpenSet (U : Opens M) :
    IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) ((U : Set M)) :=
  (inferInstance : IsManifold (𝓡 n) (⊤ : WithTop ℕ∞) U)

/-- Proposition 5.1 (1): an open submanifold of a smooth manifold is an embedded submanifold via
the canonical subtype inclusion. -/
theorem open_submanifold_isEmbeddedSubmanifold (U : Opens M) :
    IsEmbeddedSubmanifold (𝓡 n) (𝓡 n) (U : Set M) where
  toBoundarylessManifold :=
    (inferInstance : BoundarylessManifold (𝓡 n) U)
  isSmoothEmbedding_subtype_val :=
    IsSmoothEmbedding.of_opens (I := 𝓡 n) (n := (⊤ : WithTop ℕ∞)) U

/-- The canonical `Opens`-typed open submanifold inherits the embedded-submanifold structure from
`open_submanifold_isEmbeddedSubmanifold`. -/
instance instIsEmbeddedSubmanifoldOpens (U : Opens M) :
    IsEmbeddedSubmanifold (𝓡 n) (𝓡 n) (U : Set M) :=
  open_submanifold_isEmbeddedSubmanifold U

/-- Helper: an open submanifold has codimension `0` in its ambient smooth manifold. -/
theorem open_submanifold_codimension_zero (U : Opens M) :
    ((show IsEmbeddedSubmanifold (𝓡 n) (𝓡 n) (U : Set M) from
        open_submanifold_isEmbeddedSubmanifold U)).codimension = 0 := by
  simp

/-- Lowering the differentiability index preserves immersions: the same chart normal form remains
valid in the coarser maximal atlas. -/
lemma isImmersion_of_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    {I : ModelWithCorners ℝ E H} [IsManifold I (⊤ : WithTop ℕ∞) N]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {P : Type*} [TopologicalSpace P] [ChartedSpace H' P]
    {J : ModelWithCorners ℝ E' H'} [IsManifold J (⊤ : WithTop ℕ∞) P]
    {a b : WithTop ℕ∞} {f : N → P} (hba : b ≤ a) (hf : IsImmersion I J a f) :
    IsImmersion I J b f := by
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := N) hba)
      hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := J) (M := P) hba)
      hx.codChart_mem_maximalAtlas

/-- Proposition 5.1 (2): a codimension-`0` embedded submanifold of a smooth manifold is an open
subset of the ambient manifold. -/
theorem isOpen_of_codimension_zero_embedded_submanifold {S : Set M}
    [ChartedSpace (EuclideanSpace ℝ (Fin k)) S]
    [IsManifold (𝓡 k) (⊤ : WithTop ℕ∞) S]
    (hS : IsEmbeddedSubmanifold (𝓡 n) (𝓡 k) S)
    (hcodim : hS.codimension = 0) :
    IsOpen S := by
  cases Set.eq_empty_or_nonempty S with
  | inl hSemp =>
    rw [hSemp]
    exact isOpen_empty
  | inr hNE =>
    obtain ⟨p, hpS⟩ := hNE
    let hp := hS.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt ⟨p, hpS⟩
    have hle : k ≤ n := by
      have hinj :
          Function.Injective
            (hp.equiv.toLinearEquiv.toLinearMap.comp
              (LinearMap.inl ℝ (EuclideanSpace ℝ (Fin k)) hp.complement)) :=
        hp.equiv.injective.comp LinearMap.inl_injective
      have := LinearMap.finrank_le_finrank_of_injective hinj
      simpa [finrank_euclideanSpace_fin] using this
    have hnle : n ≤ k := by
      have hnk : n - k = 0 := by
        simpa [finrank_euclideanSpace_fin] using hcodim
      exact Nat.le_of_sub_eq_zero hnk
    have hkn : k = n := le_antisymm hle hnle
    letI : IsManifold (𝓡 k) ∞ S := IsManifold.of_le le_top
    letI : IsManifold (𝓡 n) ∞ M := IsManifold.of_le le_top
    have himm : IsImmersion (𝓡 k) (𝓡 n) ∞ (Subtype.val : S → M) :=
      isImmersion_of_le (by simp) hS.isSmoothEmbedding_subtype_val.isImmersion
    have hld : IsLocalDiffeomorph (𝓡 k) (𝓡 n) ∞ (Subtype.val : S → M) :=
      is_local_diffeomorph_of_is_immersion_of_eq_dim hkn himm
    simpa [Subtype.range_coe] using hld.isOpen_range

end
