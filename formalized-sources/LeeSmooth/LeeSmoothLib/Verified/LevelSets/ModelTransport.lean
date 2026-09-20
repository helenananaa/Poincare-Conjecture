import Mathlib
import LeeSmoothLib.Verified.LevelSets.DiffeomorphTransport
import LeeSmoothLib.Ch04.Sec04_21.Exercise_4_4
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3

/-!
Generic `C∞` atlas transport from a finite-dimensional real boundaryless model to the
standard Euclidean model `𝓡 (finrank E)`.

A wrapper type `EuclideanRechart M` carries the transported Euclidean atlas, so the original
`ChartedSpace H M` instance is never overwritten (this matters when `H` is already a Euclidean
space).  Linear identifications are `C∞`, so the construction does not promote smoothness to
analyticity.

Downstream h06 / h07 may reuse the same source and codomain transport.  Helpers live in this
distinct namespace and do not modify `IsEmbeddedSubmanifold` or the verified Euclidean owners.
-/

open scoped ContDiff Manifold
open Manifold Set ChartedSpace

noncomputable section

namespace LeeVerifiedLevelSets
namespace ModelTransport

universe uE uH uM uE' uH' uN

/-- Copy of a manifold used only to host a Euclidean atlas, avoiding a `ChartedSpace` diamond
when the original model space is already Euclidean. -/
@[ext]
structure EuclideanRechart (M : Type*) where
  /-- The underlying point of the original manifold. -/
  val : M

namespace EuclideanRechart

variable {M : Type*} [TopologicalSpace M]

instance : TopologicalSpace (EuclideanRechart M) :=
  TopologicalSpace.induced val ‹TopologicalSpace M›

/-- The wrapper is topologically identical to the original space. -/
def homeomorph : EuclideanRechart M ≃ₜ M where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact continuous_id

instance [T2Space M] : T2Space (EuclideanRechart M) :=
  homeomorph.symm.t2Space

instance [SecondCountableTopology M] : SecondCountableTopology (EuclideanRechart M) :=
  homeomorph.secondCountableTopology

end EuclideanRechart

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]

/-- Preferred linear identification of a finite-dimensional real space with Euclidean space. -/
abbrev toEuclideanCLM (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
  toEuclidean

/-- The model-space homeomorphism `H ≃ₜ EuclideanSpace` from a boundaryless model. -/
def toEuclideanModelHomeomorph :
    H ≃ₜ EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
  I.toHomeomorph.trans (toEuclideanCLM E).toHomeomorph

/-- Pull a `ChartedSpace` structure back along a homeomorphism of the underlying space. -/
@[implicit_reducible]
def chartedSpaceCongr {H' M' N' : Type*} [TopologicalSpace H'] [TopologicalSpace M']
    [TopologicalSpace N'] [ChartedSpace H' M'] (e : N' ≃ₜ M') :
    ChartedSpace H' N' where
  atlas := (atlas H' M').image fun χ => e.toOpenPartialHomeomorph.trans χ
  chartAt x := e.toOpenPartialHomeomorph.trans (chartAt H' (e x))
  mem_chart_source x := by
    simp [Homeomorph.toOpenPartialHomeomorph_source]
  chart_mem_atlas x := ⟨chartAt H' (e x), chart_mem_atlas H' (e x), rfl⟩

/-- Postcompose every chart by a homeomorphism of the model space. -/
@[implicit_reducible]
def chartedSpaceTransHomeomorph {H' : Type*} [TopologicalSpace H'] (e : H ≃ₜ H') :
    ChartedSpace H' M where
  atlas := (atlas H M).image fun χ => χ.transHomeomorph e
  chartAt x := (chartAt H x).transHomeomorph e
  mem_chart_source x := by
    simp [OpenPartialHomeomorph.transHomeomorph_eq_trans,
      Homeomorph.toOpenPartialHomeomorph_source]
  chart_mem_atlas x := ⟨chartAt H x, chart_mem_atlas H x, rfl⟩

/-- Euclidean charts on the original space `M`.  Prefer `euclideanRechartChartedSpace` when
both the original and Euclidean `ChartedSpace` instances must coexist. -/
@[implicit_reducible]
def euclideanChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) M :=
  chartedSpaceTransHomeomorph (toEuclideanModelHomeomorph (I := I))

/-- Self-model specialisation used by matrix groups. -/
@[implicit_reducible]
def euclideanChartedSpaceSelf
    {F P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace P] [ChartedSpace F P] :
    ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) P :=
  chartedSpaceTransHomeomorph (H := F) (M := P) (toEuclideanCLM F).toHomeomorph

/-- Euclidean charts on the wrapper type. -/
@[implicit_reducible]
def euclideanRechartChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) (EuclideanRechart M) :=
  haveI : ChartedSpace H (EuclideanRechart M) :=
    chartedSpaceCongr (EuclideanRechart.homeomorph (M := M))
  euclideanChartedSpace (I := I) (M := EuclideanRechart M)

/-- `C∞` manifold structure after pulling charts back along a homeomorphism of the space. -/
theorem chartedSpaceCongr_isManifold {H' M' N' : Type*}
    [TopologicalSpace H'] [TopologicalSpace M'] [TopologicalSpace N']
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {I' : ModelWithCorners ℝ E' H'} [ChartedSpace H' M'] [IsManifold I' ∞ M']
    (e : N' ≃ₜ M') :
    letI : ChartedSpace H' N' :=
      chartedSpaceCongr (H' := H') (M' := M') (N' := N') e
    IsManifold I' ∞ N' := by
  letI : ChartedSpace H' N' :=
    chartedSpaceCongr (H' := H') (M' := M') (N' := N') e
  refine isManifold_of_contDiffOn I' ∞ N' ?_
  intro f f' hf hf'
  rcases hf with ⟨χ, hχ, rfl⟩
  rcases hf' with ⟨χ', hχ', rfl⟩
  have horigMem :
      χ.symm.trans χ' ∈ contDiffGroupoid (∞ : WithTop ℕ∞) I' :=
    HasGroupoid.compatible hχ hχ'
  have horig :
      ContDiffOn ℝ ∞ (I' ∘ (↑(χ.symm.trans χ')) ∘ I'.symm)
        (I'.symm ⁻¹' (χ.symm.trans χ').source ∩ range I') :=
    (mem_groupoid_of_pregroupoid.mp horigMem).1
  convert horig using 2
  · ext z
    simp [OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      Homeomorph.symm_toOpenPartialHomeomorph, OpenPartialHomeomorph.trans_assoc]
  · ext z
    simp [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      Homeomorph.symm_toOpenPartialHomeomorph, Homeomorph.toOpenPartialHomeomorph_source]

/-- The transported Euclidean atlas on `M` is a `C∞` manifold structure. -/
theorem euclideanChartedSpace_isManifold :
    letI := euclideanChartedSpace (E := E) (H := H) (M := M) (I := I)
    IsManifold (𝓡 (Module.finrank ℝ E)) ∞ M := by
  letI := euclideanChartedSpace (E := E) (H := H) (M := M) (I := I)
  refine isManifold_of_contDiffOn (𝓡 (Module.finrank ℝ E)) ∞ M ?_
  intro e e' he he'
  rcases he with ⟨χ, hχ, rfl⟩
  rcases he' with ⟨χ', hχ', rfl⟩
  let eE := toEuclideanCLM E
  let φ := toEuclideanModelHomeomorph (I := I)
  have horigMem :
      χ.symm.trans χ' ∈ contDiffGroupoid (∞ : WithTop ℕ∞) I :=
    HasGroupoid.compatible hχ hχ'
  have horig :
      ContDiffOn ℝ ∞ (I ∘ (↑(χ.symm.trans χ')) ∘ I.symm)
        (I.symm ⁻¹' (χ.symm.trans χ').source ∩ range I) :=
    (mem_groupoid_of_pregroupoid.mp horigMem).1
  have hlin :
      ContDiffOn ℝ ∞ (eE ∘ (I ∘ (↑(χ.symm.trans χ')) ∘ I.symm) ∘ eE.symm)
        (eE '' (I.symm ⁻¹' (χ.symm.trans χ').source ∩ range I)) :=
    eE.contDiff.comp_contDiffOn <|
      horig.comp eE.symm.contDiff.contDiffOn fun z hz => by
        rcases hz with ⟨w, hw, rfl⟩
        simpa using hw
  have hrange : (range I : Set E) = univ := I.range_eq_univ
  refine (hlin.mono ?_).congr ?_
  · intro z hz
    -- `𝓡 m` is the identity model, so the groupoid domain is the transition source.
    have hzSrc :
        z ∈ ((χ.transHomeomorph φ).symm.trans (χ'.transHomeomorph φ)).source := by
      simpa [modelWithCornersSelf_coe, φ] using hz
    refine ⟨eE.symm z, ?_, ContinuousLinearEquiv.apply_symm_apply _ _⟩
    have hφ : φ.symm z ∈ (χ.symm.trans χ').source := by
      simp only [OpenPartialHomeomorph.transHomeomorph_eq_trans,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc,
        OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source] at hzSrc
      -- `φ.symm z ∈ χ.target ∧ χ.symm (φ.symm z) ∈ χ'.source`
      simpa [OpenPartialHomeomorph.trans_source] using hzSrc.2
    constructor
    · simpa [φ, toEuclideanModelHomeomorph] using hφ
    · simp [hrange]
  · intro z _hz
    simp [eE, φ, toEuclideanModelHomeomorph, Function.comp, modelWithCornersSelf_coe]

/-- The wrapper type is a `C∞` Euclidean manifold. -/
theorem euclideanRechart_isManifold :
    letI := euclideanRechartChartedSpace (E := E) (H := H) (M := M) (I := I)
    IsManifold (𝓡 (Module.finrank ℝ E)) ∞ (EuclideanRechart M) := by
  letI : ChartedSpace H (EuclideanRechart M) :=
    chartedSpaceCongr (H' := H) (M' := M) (N' := EuclideanRechart M)
      (EuclideanRechart.homeomorph (M := M))
  letI : IsManifold I ∞ (EuclideanRechart M) :=
    chartedSpaceCongr_isManifold (H' := H) (M' := M) (N' := EuclideanRechart M)
      (E' := E) (I' := I) (EuclideanRechart.homeomorph (M := M))
  exact euclideanChartedSpace_isManifold (E := E) (H := H) (M := EuclideanRechart M) (I := I)

/-- The wrapper constructor is `C∞` from the original atlas to the Euclidean recharting. -/
theorem contMDiff_euclideanRechart_mk :
    letI rechartCS := euclideanRechartChartedSpace (E := E) (H := H) (M := M) (I := I)
    ContMDiff I (𝓡 (Module.finrank ℝ E)) ∞ (EuclideanRechart.mk : M → EuclideanRechart M) := by
  letI rechartCS := euclideanRechartChartedSpace (E := E) (H := H) (M := M) (I := I)
  letI := euclideanRechart_isManifold (E := E) (H := H) (M := M) (I := I)
  rw [contMDiff_iff_target]
  refine ⟨EuclideanRechart.homeomorph.symm.continuous, ?_⟩
  intro y
  have hchart := (toEuclideanCLM E).toContinuousLinearMap.contMDiff.comp_contMDiffOn
    (contMDiffOn_extChartAt (I := I) (x := y.val) (n := ∞))
  convert hchart using 1
  · funext z
    rfl
  · ext z
    change ((True ∧ z ∈ (chartAt H y.val).source) ∧ True) ↔ z ∈ (chartAt H y.val).source
    simp

/-- The wrapper destructor is `C∞` from the Euclidean recharting to the original atlas. -/
theorem contMDiff_euclideanRechart_val :
    letI rechartCS := euclideanRechartChartedSpace (E := E) (H := H) (M := M) (I := I)
    ContMDiff (𝓡 (Module.finrank ℝ E)) I ∞ (EuclideanRechart.val : EuclideanRechart M → M) := by
  letI rechartCS := euclideanRechartChartedSpace (E := E) (H := H) (M := M) (I := I)
  letI := euclideanRechart_isManifold (E := E) (H := H) (M := M) (I := I)
  rw [contMDiff_iff_target]
  refine ⟨EuclideanRechart.homeomorph.continuous, ?_⟩
  intro y
  have hchart := (toEuclideanCLM E).symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn
    (contMDiffOn_extChartAt (I := 𝓡 (Module.finrank ℝ E)) (x := EuclideanRechart.mk y) (n := ∞))
  convert hchart using 1
  · funext z
    change I (chartAt H y z.val) = (toEuclideanCLM E).symm (toEuclideanCLM E _)
    exact ((toEuclideanCLM E).symm_apply_apply _).symm
  · ext z
    simp only [extChartAt_source, Set.mem_preimage]
    change z.val ∈ (chartAt H y).source ↔ (True ∧ z.val ∈ (chartAt H y).source)
    simp

/-- The original manifold and its Euclidean copy are genuinely diffeomorphic. -/
def euclideanRechartDiffeomorph :
    letI := euclideanRechartChartedSpace (I := I) (M := M)
    EuclideanRechart M ≃ₘ⟮𝓡 (Module.finrank ℝ E), I⟯ M := by
  letI := euclideanRechartChartedSpace (I := I) (M := M)
  exact { toEquiv := (EuclideanRechart.homeomorph (M := M)).toEquiv
          contMDiff_toFun := contMDiff_euclideanRechart_val (I := I) (M := M)
          contMDiff_invFun := contMDiff_euclideanRechart_mk (I := I) (M := M) }

variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {J : ModelWithCorners ℝ E' H'} [J.Boundaryless] [IsManifold J ∞ N]

/-- Rechart a map `M → N` as a map of Euclidean wrapper manifolds. -/
def rechartMap (Φ : M → N) : EuclideanRechart M → EuclideanRechart N :=
  fun x => ⟨Φ x.val⟩

theorem rechartMap_val (Φ : M → N) (x : EuclideanRechart M) :
    (rechartMap Φ x).val = Φ x.val :=
  rfl

/-- A `C∞` map remains `C∞` after Euclidean recharting of source and target. -/
theorem contMDiff_rechartMap {Φ : M → N} (hΦ : ContMDiff I J ∞ Φ) :
    letI := euclideanRechartChartedSpace (E := E) (H := H) (M := M) (I := I)
    letI := euclideanRechartChartedSpace (E := E') (H := H') (M := N) (I := J)
    ContMDiff (𝓡 (Module.finrank ℝ E)) (𝓡 (Module.finrank ℝ E')) ∞
      (rechartMap Φ) := by
  letI := euclideanRechartChartedSpace (E := E) (H := H) (M := M) (I := I)
  letI := euclideanRechartChartedSpace (E := E') (H := H') (M := N) (I := J)
  letI := euclideanRechart_isManifold (E := E) (H := H) (M := M) (I := I)
  letI := euclideanRechart_isManifold (E := E') (H := H') (M := N) (I := J)
  have hmk := contMDiff_euclideanRechart_mk (I := J) (M := N)
  have hval := contMDiff_euclideanRechart_val (I := I) (M := M)
  exact hmk.comp (hΦ.comp hval)

/-- Constant rank is preserved by Euclidean recharting on both sides. -/
theorem hasConstantRank_rechartMap {r : ℕ} {Φ : M → N}
    (hΦ : ContMDiff I J ∞ Φ) (hr : HasConstantRank I J Φ r) :
    letI := euclideanRechartChartedSpace (I := I) (M := M)
    letI := euclideanRechartChartedSpace (I := J) (M := N)
    HasConstantRank (𝓡 (Module.finrank ℝ E)) (𝓡 (Module.finrank ℝ E'))
      (rechartMap Φ) r := by
  letI := euclideanRechartChartedSpace (I := I) (M := M)
  letI := euclideanRechartChartedSpace (I := J) (M := N)
  exact (DiffeomorphTransport.hasConstantRank_comp_diffeomorphs_iff
    (euclideanRechartDiffeomorph (I := I) (M := M))
    (euclideanRechartDiffeomorph (I := J) (M := N)).symm hΦ r).mpr hr

/-- A regular value stays regular in the Euclidean copied manifolds. -/
theorem isRegularValue_rechartMap {Φ : M → N} {c : N}
    (hΦ : ContMDiff I J ∞ Φ) (hc : IsRegularValue I J Φ c) :
    letI := euclideanRechartChartedSpace (I := I) (M := M)
    letI := euclideanRechartChartedSpace (I := J) (M := N)
    IsRegularValue (𝓡 (Module.finrank ℝ E)) (𝓡 (Module.finrank ℝ E'))
      (rechartMap Φ) (EuclideanRechart.mk c) := by
  letI := euclideanRechartChartedSpace (I := I) (M := M)
  letI := euclideanRechartChartedSpace (I := J) (M := N)
  exact (DiffeomorphTransport.isRegularValue_comp_diffeomorphs_iff
    (euclideanRechartDiffeomorph (I := I) (M := M))
    (euclideanRechartDiffeomorph (I := J) (M := N)).symm hΦ c).mpr hc

end ModelTransport
end LeeVerifiedLevelSets
end
