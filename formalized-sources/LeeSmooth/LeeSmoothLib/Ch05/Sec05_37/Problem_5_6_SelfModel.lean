import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3

/-!
C∞ self-model transport used by Problem 5-6.

A finite-dimensional real self-model `𝓘(ℝ, F)` is linearly equivalent to a Euclidean space.
Postcomposing the atlas by that equivalence yields a `C∞` Euclidean atlas, because linear maps
are smooth.  This is the C∞ counterpart of the analytic transport in
`LeeVerifiedAnalyticLevelSets`, specialized to Problem 5-6's tangent-bundle self-model.
-/

open scoped ContDiff Manifold
open Manifold Set Function Topology

noncomputable section

namespace Problem56SelfModel

/-- Preferred linear identification of a finite-dimensional real space with Euclidean space. -/
noncomputable def toEuclideanCLM (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    F ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) :=
  ContinuousLinearEquiv.ofFinrankEq (by simp [finrank_euclideanSpace_fin])

/-- Linear identification of a product of Euclidean spaces with a single Euclidean space. -/
noncomputable def prodToEuclidean (k : ℕ) :
    (EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 * k)) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [Module.finrank_prod, finrank_euclideanSpace_fin]
    omega)

/-- The model-product tag is the ordinary product, as a homeomorphism. -/
def modelProdToProd (k : ℕ) :
    ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) ≃ₜ
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- Homeomorphism from the tangent-bundle model space to a Euclidean space of dimension `2k`. -/
noncomputable def modelProdToEuclidean (k : ℕ) :
    ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) ≃ₜ
      EuclideanSpace ℝ (Fin (2 * k)) :=
  (modelProdToProd k).trans (prodToEuclidean k).toHomeomorph

/-- Euclidean charts on a space modelled on a Euclidean product, typically a tangent bundle. -/
@[implicit_reducible]
noncomputable def euclideanChartedSpaceModelProd
    (k : ℕ) (P : Type*) [TopologicalSpace P]
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) P] :
    ChartedSpace (EuclideanSpace ℝ (Fin (2 * k))) P where
  atlas := (atlas (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) P).image
    fun e => e.transHomeomorph (modelProdToEuclidean k)
  chartAt x := (chartAt (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) x).transHomeomorph
    (modelProdToEuclidean k)
  mem_chart_source x := by
    simpa [OpenPartialHomeomorph.transHomeomorph_eq_trans, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source] using
      mem_chart_source (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) x
  chart_mem_atlas x :=
    ⟨chartAt (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) x,
      chart_mem_atlas _ x, rfl⟩

theorem euclideanChartedSpaceModelProd_isManifold
    (k : ℕ) (P : Type*) [TopologicalSpace P]
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) P]
    [IsManifold (𝓡 k).tangent ∞ P] :
    letI := euclideanChartedSpaceModelProd k P
    IsManifold (𝓡 (2 * k)) ∞ P := by
  letI := euclideanChartedSpaceModelProd k P
  refine isManifold_of_contDiffOn (𝓡 (2 * k)) ∞ P ?_
  intro e e' he he'
  rcases he with ⟨χ, hχ, rfl⟩
  rcases he' with ⟨χ', hχ', rfl⟩
  let L := modelProdToEuclidean k
  let eE := prodToEuclidean k
  have horigMem :
      χ.symm.trans χ' ∈ contDiffGroupoid ∞ (𝓡 k).tangent :=
    HasGroupoid.compatible hχ hχ'
  have horig :
      ContDiffOn ℝ ∞
        ((𝓡 k).tangent ∘ ↑(χ.symm.trans χ') ∘ (𝓡 k).tangent.symm)
        ((𝓡 k).tangent.symm ⁻¹' (χ.symm.trans χ').source ∩ range (𝓡 k).tangent) :=
    (mem_groupoid_of_pregroupoid.mp horigMem).1
  have hlin :
      ContDiffOn ℝ ∞
        (eE ∘ ((𝓡 k).tangent ∘ ↑(χ.symm.trans χ') ∘ (𝓡 k).tangent.symm) ∘ eE.symm)
        (eE '' ((𝓡 k).tangent.symm ⁻¹' (χ.symm.trans χ').source ∩ range (𝓡 k).tangent)) :=
    eE.contDiff.comp_contDiffOn <|
      horig.comp eE.symm.contDiff.contDiffOn fun z hz => by
        rcases hz with ⟨w, hw, rfl⟩
        simpa [ContinuousLinearEquiv.symm_apply_apply] using hw
  refine (hlin.mono ?_).congr ?_
  · intro z hz
    have hrange : range (𝓡 k).tangent = univ := (𝓡 k).tangent.range_eq_univ
    have hz' : L.symm z ∈ (χ.symm.trans χ').source := by
      simpa [OpenPartialHomeomorph.transHomeomorph_eq_trans, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
        Homeomorph.toOpenPartialHomeomorph_source] using hz
    refine ⟨(L.symm z : EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)), ?_, ?_⟩
    · simpa [ModelWithCorners.tangent, modelWithCorners_prod_coe_symm, modelWithCornersSelf_coe,
        hrange] using hz'
    · simp [L, modelProdToEuclidean, modelProdToProd, eE]
  · intro z hz
    have hrange : range (𝓡 k).tangent = univ := (𝓡 k).tangent.range_eq_univ
    simp [eE, L, modelProdToEuclidean, modelProdToProd, ModelWithCorners.tangent,
      modelWithCorners_prod_coe, modelWithCorners_prod_coe_symm, modelWithCornersSelf_coe,
      hrange]

/-- Euclidean charts obtained by postcomposing the self-model atlas with the linear identification. -/
@[implicit_reducible]
noncomputable def euclideanChartedSpaceSelf
    {F P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace P] [ChartedSpace F P] :
    ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) P where
  atlas := (atlas F P).image fun e => e.transHomeomorph (toEuclideanCLM F).toHomeomorph
  chartAt x := (chartAt F x).transHomeomorph (toEuclideanCLM F).toHomeomorph
  mem_chart_source x := by
    simpa [OpenPartialHomeomorph.transHomeomorph_eq_trans, OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source] using mem_chart_source F x
  chart_mem_atlas x := ⟨chartAt F x, chart_mem_atlas F x, rfl⟩

theorem euclideanChartedSpaceSelf_isManifold
    {F P : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace P] [ChartedSpace F P]
    [IsManifold 𝓘(ℝ, F) ∞ P] :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    IsManifold (𝓡 (Module.finrank ℝ F)) ∞ P := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  refine isManifold_of_contDiffOn (𝓡 (Module.finrank ℝ F)) ∞ P ?_
  intro e e' he he'
  rcases he with ⟨χ, hχ, rfl⟩
  rcases he' with ⟨χ', hχ', rfl⟩
  let eE := toEuclideanCLM F
  have horigMem :
      χ.symm.trans χ' ∈ contDiffGroupoid ∞ 𝓘(ℝ, F) :=
    HasGroupoid.compatible hχ hχ'
  have horig :
      ContDiffOn ℝ ∞
        (𝓘(ℝ, F) ∘ ↑(χ.symm.trans χ') ∘ 𝓘(ℝ, F).symm)
        (𝓘(ℝ, F).symm ⁻¹' (χ.symm.trans χ').source ∩ range 𝓘(ℝ, F)) :=
    (mem_groupoid_of_pregroupoid.mp horigMem).1
  have horig' :
      ContDiffOn ℝ ∞ (↑(χ.symm.trans χ'))
        (χ.symm.trans χ').source := by
    convert horig using 2 <;> simp [modelWithCornersSelf_coe]
  have hlin :
      ContDiffOn ℝ ∞
        (eE ∘ (↑(χ.symm.trans χ')) ∘ eE.symm)
        (eE '' (χ.symm.trans χ').source) :=
    eE.contDiff.comp_contDiffOn <|
      horig'.comp eE.symm.contDiff.contDiffOn fun z hz => by
        rcases hz with ⟨w, hw, rfl⟩
        simpa using hw
  refine (hlin.mono ?_).congr ?_
  · intro z hz
    refine ⟨eE.symm z, ?_, ContinuousLinearEquiv.apply_symm_apply _ _⟩
    simpa [OpenPartialHomeomorph.transHomeomorph_eq_trans, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      Homeomorph.toOpenPartialHomeomorph_source, modelWithCornersSelf_coe] using hz
  · intro z hz
    simp [eE]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
variable {P : Type*} [TopologicalSpace P] [ChartedSpace F P] [IsManifold 𝓘(ℝ, F) ∞ P]
variable {P' : Type*} [TopologicalSpace P'] [ChartedSpace F' P'] [IsManifold 𝓘(ℝ, F') ∞ P']

lemma chartAt_euclidean (x : P) :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    chartAt (EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) x =
      (chartAt F x).transHomeomorph (toEuclideanCLM F).toHomeomorph :=
  rfl

lemma extChartAt_euclidean_coe (x : P) :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    ⇑(extChartAt (𝓡 (Module.finrank ℝ F)) x) =
      toEuclideanCLM F ∘ extChartAt 𝓘(ℝ, F) x := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  funext z
  simp [extChartAt_coe, chartAt_euclidean, OpenPartialHomeomorph.transHomeomorph_eq_trans,
    modelWithCornersSelf_coe]

lemma extChartAt_euclidean_symm_coe (x : P) :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    ⇑(extChartAt (𝓡 (Module.finrank ℝ F)) x).symm =
      (extChartAt 𝓘(ℝ, F) x).symm ∘ (toEuclideanCLM F).symm := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  funext z
  simp [extChartAt_coe_symm, chartAt_euclidean, OpenPartialHomeomorph.transHomeomorph_eq_trans,
    modelWithCornersSelf_coe]

lemma extChartAt_euclidean_source (x : P) :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    (extChartAt (𝓡 (Module.finrank ℝ F)) x).source = (extChartAt 𝓘(ℝ, F) x).source := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  simp [extChartAt_source, chartAt_euclidean, OpenPartialHomeomorph.transHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_source, Homeomorph.toOpenPartialHomeomorph_source]

lemma extChartAt_euclidean_target (x : P) :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    (extChartAt (𝓡 (Module.finrank ℝ F)) x).target =
      toEuclideanCLM F '' (extChartAt 𝓘(ℝ, F) x).target := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  have hI : range (𝓡 (Module.finrank ℝ F)) = univ := ModelWithCorners.range_eq_univ _
  have hI' : range 𝓘(ℝ, F) = univ := ModelWithCorners.range_eq_univ _
  simp [extChartAt_target, chartAt_euclidean, OpenPartialHomeomorph.transHomeomorph_eq_trans,
    OpenPartialHomeomorph.trans_target, Homeomorph.toOpenPartialHomeomorph_target,
    modelWithCornersSelf_coe, hI, hI']
  exact ((toEuclideanCLM F).toHomeomorph.image_eq_preimage_symm _).symm

lemma extChartAt_comp_euclidean (f : P → P') (x : P) (y : P') :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    letI := euclideanChartedSpaceSelf (P := P') (F := F')
    extChartAt (𝓡 (Module.finrank ℝ F')) y ∘ f ∘
        (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm =
      toEuclideanCLM F' ∘
        (extChartAt 𝓘(ℝ, F') y ∘ f ∘ (extChartAt 𝓘(ℝ, F) x).symm) ∘
          (toEuclideanCLM F).symm := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  letI := euclideanChartedSpaceSelf (P := P') (F := F')
  funext z
  rw [extChartAt_euclidean_coe, extChartAt_euclidean_symm_coe]
  rfl

lemma extChartAt_comp_euclidean_domain (f : P → P') (x : P) (y : P') :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    letI := euclideanChartedSpaceSelf (P := P') (F := F')
    (extChartAt (𝓡 (Module.finrank ℝ F)) x).target ∩
        (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm ⁻¹'
          (f ⁻¹' (extChartAt (𝓡 (Module.finrank ℝ F')) y).source) =
      toEuclideanCLM F ''
        ((extChartAt 𝓘(ℝ, F) x).target ∩
          (extChartAt 𝓘(ℝ, F) x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℝ, F') y).source)) := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  letI := euclideanChartedSpaceSelf (P := P') (F := F')
  let eE := toEuclideanCLM F
  have htgt := extChartAt_euclidean_target (F := F) (P := P) x
  have hsym := extChartAt_euclidean_symm_coe (F := F) (P := P) x
  have hsrcy := extChartAt_euclidean_source (F := F') (P := P') y
  ext z
  constructor
  · intro hz
    have hzT : z ∈ (extChartAt (𝓡 (Module.finrank ℝ F)) x).target := hz.1
    rw [htgt] at hzT
    rcases hzT with ⟨w, hw, rfl⟩
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    have hzw : (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm (eE w) =
        (extChartAt 𝓘(ℝ, F) x).symm w := by
      rw [hsym]; simp [eE]
    have hmem : f ((extChartAt (𝓡 (Module.finrank ℝ F)) x).symm (eE w)) ∈
        (extChartAt (𝓡 (Module.finrank ℝ F')) y).source := hz.2
    rw [hzw, hsrcy] at hmem
    exact hmem
  · intro hz
    rcases hz with ⟨w, hw, rfl⟩
    constructor
    · rw [htgt]
      exact ⟨w, hw.1, rfl⟩
    · have hzw : (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm (eE w) =
          (extChartAt 𝓘(ℝ, F) x).symm w := by
        rw [hsym]; simp [eE]
      have hmem : f ((extChartAt 𝓘(ℝ, F) x).symm w) ∈ (extChartAt 𝓘(ℝ, F') y).source := hw.2
      rw [← hzw, ← hsrcy] at hmem
      exact hmem

/-- Smooth maps between self-models remain smooth after Euclidean atlas transport. -/
theorem contMDiff_after_euclidean {f : P → P'}
    (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F') ∞ f) :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    letI := euclideanChartedSpaceSelf (P := P') (F := F')
    letI := euclideanChartedSpaceSelf_isManifold (P := P) (F := F)
    letI := euclideanChartedSpaceSelf_isManifold (P := P') (F := F')
    ContMDiff (𝓡 (Module.finrank ℝ F)) (𝓡 (Module.finrank ℝ F')) ∞ f := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  letI := euclideanChartedSpaceSelf (P := P') (F := F')
  letI := euclideanChartedSpaceSelf_isManifold (P := P) (F := F)
  letI := euclideanChartedSpaceSelf_isManifold (P := P') (F := F')
  rw [contMDiff_iff]
  refine ⟨hf.continuous, ?_⟩
  intro x y
  have hfold := (contMDiff_iff.mp hf).2 x y
  have hfun := extChartAt_comp_euclidean (F := F) (F' := F') (P := P) (P' := P') f x y
  have hdom := extChartAt_comp_euclidean_domain (F := F) (F' := F') (P := P) (P' := P') f x y
  let eE := toEuclideanCLM F
  let eE' := toEuclideanCLM F'
  have hlin :
      ContDiffOn ℝ ∞
        (eE' ∘ (extChartAt 𝓘(ℝ, F') y ∘ f ∘ (extChartAt 𝓘(ℝ, F) x).symm) ∘ eE.symm)
        (eE '' ((extChartAt 𝓘(ℝ, F) x).target ∩
          (extChartAt 𝓘(ℝ, F) x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℝ, F') y).source))) :=
    eE'.contDiff.comp_contDiffOn <|
      hfold.comp eE.symm.contDiff.contDiffOn fun z hz => by
        rcases hz with ⟨w, hw, rfl⟩
        simpa [eE] using hw
  rw [hfun, hdom]
  exact hlin

/-- Regularity of a value is preserved by Euclidean atlas transport of a self-model. -/
theorem isRegularValue_after_euclidean {f : P → P'} {c : P'}
    (hf : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F') ∞ f)
    (hc : IsRegularValue 𝓘(ℝ, F) 𝓘(ℝ, F') f c) :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    letI := euclideanChartedSpaceSelf (P := P') (F := F')
    letI := euclideanChartedSpaceSelf_isManifold (P := P) (F := F)
    letI := euclideanChartedSpaceSelf_isManifold (P := P') (F := F')
    IsRegularValue (𝓡 (Module.finrank ℝ F)) (𝓡 (Module.finrank ℝ F')) f c := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  letI := euclideanChartedSpaceSelf (P := P') (F := F')
  letI := euclideanChartedSpaceSelf_isManifold (P := P) (F := F)
  letI := euclideanChartedSpaceSelf_isManifold (P := P') (F := F')
  intro x hx
  have hfold := hc x hx
  have hfnew := contMDiff_after_euclidean (F := F) (F' := F') (P := P) (P' := P') hf
  have hdiffOld : MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F') f x :=
    hf.mdifferentiableAt (by simp)
  have hdiffNew : MDifferentiableAt (𝓡 (Module.finrank ℝ F)) (𝓡 (Module.finrank ℝ F')) f x :=
    hfnew.mdifferentiableAt (by simp)
  have hpI : 𝓘(ℝ, F).IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  have hpE : (𝓡 (Module.finrank ℝ F)).IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  have holdFDeriv :
      HasFDerivAt (writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, F') x f : F → F')
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F') f x) (extChartAt 𝓘(ℝ, F) x x) :=
    writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint hpI hdiffOld.hasMFDerivAt
  let eE := toEuclideanCLM F
  let eE' := toEuclideanCLM F'
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) →L[ℝ] F := eE.symm
  let L' : F' →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ F')) := eE'
  have hcenter :
      extChartAt (𝓡 (Module.finrank ℝ F)) x x = eE (extChartAt 𝓘(ℝ, F) x x) := by
    rw [extChartAt_euclidean_coe]
    rfl
  have hwritten :
      writtenInExtChartAt (𝓡 (Module.finrank ℝ F)) (𝓡 (Module.finrank ℝ F')) x f =
        eE' ∘ writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, F') x f ∘ eE.symm :=
    extChartAt_comp_euclidean (F := F) (F' := F') (P := P) (P' := P') f x (f x)
  have hR : HasFDerivAt (⇑eE.symm) L (eE (extChartAt 𝓘(ℝ, F) x x)) := L.hasFDerivAt
  have hL : HasFDerivAt (⇑eE') L'
      (writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, F') x f (extChartAt 𝓘(ℝ, F) x x)) := L'.hasFDerivAt
  have hold' :
      HasFDerivAt (writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, F') x f : F → F')
        (mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F') f x) (eE.symm (eE (extChartAt 𝓘(ℝ, F) x x))) := by
    simpa using holdFDeriv
  have hmid :
      HasFDerivAt (writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, F') x f ∘ ⇑eE.symm)
        ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F') f x).comp L)
        (eE (extChartAt 𝓘(ℝ, F) x x)) :=
    HasFDerivAt.comp (eE (extChartAt 𝓘(ℝ, F) x x)) hold' hR
  have hL' : HasFDerivAt (⇑eE') L'
      ((writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, F') x f ∘ ⇑eE.symm)
        (eE (extChartAt 𝓘(ℝ, F) x x))) := by
    simpa using hL
  have hcomp :
      HasFDerivAt
        (eE' ∘ writtenInExtChartAt 𝓘(ℝ, F) 𝓘(ℝ, F') x f ∘ eE.symm)
        (L'.comp ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F') f x).comp L))
        (eE (extChartAt 𝓘(ℝ, F) x x)) :=
    HasFDerivAt.comp (eE (extChartAt 𝓘(ℝ, F) x x)) hL' hmid
  have hnewFDeriv :
      HasFDerivAt
        (writtenInExtChartAt (𝓡 (Module.finrank ℝ F)) (𝓡 (Module.finrank ℝ F')) x f)
        (L'.comp ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F') f x).comp L))
        (extChartAt (𝓡 (Module.finrank ℝ F)) x x) := by
    rw [hwritten, hcenter]
    exact hcomp
  have hmf :
      mfderiv (𝓡 (Module.finrank ℝ F)) (𝓡 (Module.finrank ℝ F')) f x =
        L'.comp ((mfderiv 𝓘(ℝ, F) 𝓘(ℝ, F') f x).comp L) := by
    have hHas :=
      writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint (I := 𝓡 (Module.finrank ℝ F))
        (J := 𝓡 (Module.finrank ℝ F')) (f := f) (p := x) hpE hdiffNew.hasMFDerivAt
    exact HasFDerivAt.unique hHas hnewFDeriv
  rw [hmf]
  exact (eE'.surjective.comp hfold).comp eE.symm.surjective

/-- On the Euclidean chart target, the identity's chart representative is the linear inverse. -/
lemma writtenInExtChartAt_id_euclidean (x : P) :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    EqOn (writtenInExtChartAt (𝓡 (Module.finrank ℝ F)) 𝓘(ℝ, F) x (id : P → P))
      (toEuclideanCLM F).symm
      (extChartAt (𝓡 (Module.finrank ℝ F)) x).target := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  intro z hz
  have htgt := extChartAt_euclidean_target (F := F) (P := P) x
  have hsym := extChartAt_euclidean_symm_coe (F := F) (P := P) x
  have hzT : z ∈ (extChartAt (𝓡 (Module.finrank ℝ F)) x).target := hz
  have hz' : z ∈ toEuclideanCLM F '' (extChartAt 𝓘(ℝ, F) x).target := by
    rwa [← htgt]
  rcases hz' with ⟨w, hw, rfl⟩
  have hwSrc : (extChartAt 𝓘(ℝ, F) x).symm w ∈ (extChartAt 𝓘(ℝ, F) x).source :=
    (extChartAt 𝓘(ℝ, F) x).map_target hw
  have hzw : (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm (toEuclideanCLM F w) =
      (extChartAt 𝓘(ℝ, F) x).symm w := by
    rw [hsym]; simp
  have hright := (extChartAt 𝓘(ℝ, F) x).right_inv hw
  calc
    writtenInExtChartAt (𝓡 (Module.finrank ℝ F)) 𝓘(ℝ, F) x (id : P → P)
        (toEuclideanCLM F w) =
        (extChartAt 𝓘(ℝ, F) x)
          ((extChartAt (𝓡 (Module.finrank ℝ F)) x).symm (toEuclideanCLM F w)) :=
      rfl
    _ = (extChartAt 𝓘(ℝ, F) x) ((extChartAt 𝓘(ℝ, F) x).symm w) := by rw [hzw]
    _ = w := hright
    _ = (toEuclideanCLM F).symm (toEuclideanCLM F w) := by simp

/-- The identity, read from the Euclidean atlas to the original self-model, is a smooth embedding. -/
theorem id_isSmoothEmbedding_euclidean_to_self :
    letI := euclideanChartedSpaceSelf (P := P) (F := F)
    letI := euclideanChartedSpaceSelf_isManifold (P := P) (F := F)
    IsSmoothEmbedding (𝓡 (Module.finrank ℝ F)) 𝓘(ℝ, F) ∞ (id : P → P) := by
  letI := euclideanChartedSpaceSelf (P := P) (F := F)
  letI := euclideanChartedSpaceSelf_isManifold (P := P) (F := F)
  have hid : ContMDiff (𝓡 (Module.finrank ℝ F)) 𝓘(ℝ, F) ∞ (id : P → P) := by
    rw [contMDiff_iff]
    refine ⟨continuous_id, ?_⟩
    intro x y
    let eE := toEuclideanCLM F
    have hidOld := (contMDiff_iff.mp (contMDiff_id (I := 𝓘(ℝ, F)) (n := ∞))).2 x y
    have hsym := extChartAt_euclidean_symm_coe (F := F) (P := P) x
    have htgt := extChartAt_euclidean_target (F := F) (P := P) x
    have hfun :
        extChartAt 𝓘(ℝ, F) y ∘ id ∘ (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm =
          (extChartAt 𝓘(ℝ, F) y ∘ id ∘ (extChartAt 𝓘(ℝ, F) x).symm) ∘ eE.symm := by
      funext z
      rw [hsym]
      rfl
    have hdom :
        (extChartAt (𝓡 (Module.finrank ℝ F)) x).target ∩
            (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm ⁻¹'
              (id ⁻¹' (extChartAt 𝓘(ℝ, F) y).source) =
          eE '' ((extChartAt 𝓘(ℝ, F) x).target ∩
            (extChartAt 𝓘(ℝ, F) x).symm ⁻¹' (id ⁻¹' (extChartAt 𝓘(ℝ, F) y).source)) := by
      ext z
      constructor
      · intro hz
        have hzT : z ∈ (extChartAt (𝓡 (Module.finrank ℝ F)) x).target := hz.1
        rw [htgt] at hzT
        rcases hzT with ⟨w, hw, rfl⟩
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        have hzw : (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm (eE w) =
            (extChartAt 𝓘(ℝ, F) x).symm w := by
          rw [hsym]; simp [eE]
        have hmem : (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm (eE w) ∈
            (extChartAt 𝓘(ℝ, F) y).source := hz.2
        rw [hzw] at hmem
        exact hmem
      · intro hz
        rcases hz with ⟨w, hw, rfl⟩
        constructor
        · rw [htgt]; exact ⟨w, hw.1, rfl⟩
        · have hzw : (extChartAt (𝓡 (Module.finrank ℝ F)) x).symm (eE w) =
              (extChartAt 𝓘(ℝ, F) x).symm w := by
            rw [hsym]; simp [eE]
          have hmem : (extChartAt 𝓘(ℝ, F) x).symm w ∈
              (extChartAt 𝓘(ℝ, F) y).source := hw.2
          rw [← hzw] at hmem
          exact hmem
    have hlin :
        ContDiffOn ℝ ∞
          ((extChartAt 𝓘(ℝ, F) y ∘ id ∘ (extChartAt 𝓘(ℝ, F) x).symm) ∘ eE.symm)
          (eE '' ((extChartAt 𝓘(ℝ, F) x).target ∩
            (extChartAt 𝓘(ℝ, F) x).symm ⁻¹' (id ⁻¹' (extChartAt 𝓘(ℝ, F) y).source))) :=
      hidOld.comp eE.symm.contDiff.contDiffOn fun z hz => by
        rcases hz with ⟨w, hw, rfl⟩
        simpa [eE] using hw
    rw [hfun, hdom]
    exact hlin
  refine ⟨?_, IsEmbedding.id⟩
  rw [is_immersion_iff_forall_injective_mfderiv hid]
  intro x
  have hdiff : MDifferentiableAt (𝓡 (Module.finrank ℝ F)) 𝓘(ℝ, F) (id : P → P) x :=
    hid.mdifferentiableAt (by simp)
  have hpE : (𝓡 (Module.finrank ℝ F)).IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  let eE := toEuclideanCLM F
  let L : EuclideanSpace ℝ (Fin (Module.finrank ℝ F)) →L[ℝ] F := eE.symm
  have hHas :=
    writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint (I := 𝓡 (Module.finrank ℝ F))
      (J := 𝓘(ℝ, F)) (f := (id : P → P)) (p := x) hpE hdiff.hasMFDerivAt
  have hlin : HasFDerivAt (⇑eE.symm) L
      (extChartAt (𝓡 (Module.finrank ℝ F)) x x) := L.hasFDerivAt
  have heq := writtenInExtChartAt_id_euclidean (F := F) (P := P) x
  have hnhds : (extChartAt (𝓡 (Module.finrank ℝ F)) x).target ∈
      𝓝 (extChartAt (𝓡 (Module.finrank ℝ F)) x x) :=
    extChartAt_target_mem_nhds (I := 𝓡 (Module.finrank ℝ F)) x
  have hHas' : HasFDerivAt
      (writtenInExtChartAt (𝓡 (Module.finrank ℝ F)) 𝓘(ℝ, F) x (id : P → P)) L
      (extChartAt (𝓡 (Module.finrank ℝ F)) x x) :=
    hlin.congr_of_eventuallyEq (Filter.eventually_of_mem hnhds fun z hz => heq hz)
  have hmf :
      mfderiv (𝓡 (Module.finrank ℝ F)) 𝓘(ℝ, F) (id : P → P) x = L :=
    HasFDerivAt.unique hHas hHas'
  rw [hmf]
  exact eE.symm.injective

/-! ### Tangent-bundle model-product to Euclidean transport -/

variable (k : ℕ)
variable {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) Q]
  [IsManifold (𝓡 k).tangent ∞ Q]

lemma extChartAt_modelProd_coe (x : Q) :
    letI := euclideanChartedSpaceModelProd k Q
    ⇑(extChartAt (𝓡 (2 * k)) x) =
      prodToEuclidean k ∘ extChartAt (𝓡 k).tangent x := by
  letI := euclideanChartedSpaceModelProd k Q
  funext z
  have hchart :
      chartAt (EuclideanSpace ℝ (Fin (2 * k))) x z =
        modelProdToEuclidean k
          (chartAt (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) x z) :=
    rfl
  calc
    extChartAt (𝓡 (2 * k)) x z = chartAt (EuclideanSpace ℝ (Fin (2 * k))) x z := by
      simp [extChartAt_coe, modelWithCornersSelf_coe]
    _ = modelProdToEuclidean k
          (chartAt (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) x z) :=
      hchart
    _ = prodToEuclidean k
          (chartAt (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) x z) := by
      simp [modelProdToEuclidean, modelProdToProd]
    _ = prodToEuclidean k (extChartAt (𝓡 k).tangent x z) := by
      simp [extChartAt_coe, ModelWithCorners.tangent, modelWithCorners_prod_coe,
        modelWithCornersSelf_coe]

lemma extChartAt_modelProd_symm_coe (x : Q) :
    letI := euclideanChartedSpaceModelProd k Q
    ⇑(extChartAt (𝓡 (2 * k)) x).symm =
      (extChartAt (𝓡 k).tangent x).symm ∘ (prodToEuclidean k).symm := by
  letI := euclideanChartedSpaceModelProd k Q
  funext z
  have hchart :
      (chartAt (EuclideanSpace ℝ (Fin (2 * k))) x).symm z =
        (chartAt (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) x).symm
          ((modelProdToEuclidean k).symm z) :=
    rfl
  calc
    (extChartAt (𝓡 (2 * k)) x).symm z =
        (chartAt (EuclideanSpace ℝ (Fin (2 * k))) x).symm z := by
      simp [extChartAt_coe_symm, modelWithCornersSelf_coe]
    _ = (chartAt (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) x).symm
          ((modelProdToEuclidean k).symm z) := hchart
    _ = (chartAt (ModelProd (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k))) x).symm
          ((prodToEuclidean k).symm z) := by
      simp [modelProdToEuclidean, modelProdToProd]
    _ = (extChartAt (𝓡 k).tangent x).symm ((prodToEuclidean k).symm z) := by
      simp [extChartAt_coe_symm, ModelWithCorners.tangent, modelWithCorners_prod_coe_symm,
        modelWithCornersSelf_coe]
      rfl

lemma extChartAt_modelProd_source (x : Q) :
    letI := euclideanChartedSpaceModelProd k Q
    (extChartAt (𝓡 (2 * k)) x).source = (extChartAt (𝓡 k).tangent x).source := by
  letI := euclideanChartedSpaceModelProd k Q
  simp [extChartAt_source]
  rfl

lemma extChartAt_modelProd_target (x : Q) :
    letI := euclideanChartedSpaceModelProd k Q
    (extChartAt (𝓡 (2 * k)) x).target =
      prodToEuclidean k '' (extChartAt (𝓡 k).tangent x).target := by
  letI := euclideanChartedSpaceModelProd k Q
  have hI : range (𝓡 (2 * k)) = univ := ModelWithCorners.range_eq_univ _
  have hI' : range (𝓡 k).tangent = univ := (𝓡 k).tangent.range_eq_univ
  simp [extChartAt_target, euclideanChartedSpaceModelProd, hI, hI',
    ModelWithCorners.tangent, modelWithCorners_prod_coe_symm, modelWithCornersSelf_coe]
  exact ((prodToEuclidean k).toHomeomorph.image_eq_preimage_symm _).symm

lemma extChartAt_comp_modelProd (f : Q → ℝ) (x : Q) (y : ℝ) :
    letI := euclideanChartedSpaceModelProd k Q
    letI := euclideanChartedSpaceSelf (P := ℝ) (F := ℝ)
    extChartAt (𝓡 (Module.finrank ℝ ℝ)) y ∘ f ∘ (extChartAt (𝓡 (2 * k)) x).symm =
      toEuclideanCLM ℝ ∘
        (extChartAt 𝓘(ℝ) y ∘ f ∘ (extChartAt (𝓡 k).tangent x).symm) ∘
          (prodToEuclidean k).symm := by
  letI := euclideanChartedSpaceModelProd k Q
  letI := euclideanChartedSpaceSelf (P := ℝ) (F := ℝ)
  funext z
  rw [extChartAt_euclidean_coe (F := ℝ) (P := ℝ), extChartAt_modelProd_symm_coe k x]
  rfl

lemma extChartAt_comp_modelProd_domain (f : Q → ℝ) (x : Q) (y : ℝ) :
    letI := euclideanChartedSpaceModelProd k Q
    letI := euclideanChartedSpaceSelf (P := ℝ) (F := ℝ)
    (extChartAt (𝓡 (2 * k)) x).target ∩
        (extChartAt (𝓡 (2 * k)) x).symm ⁻¹'
          (f ⁻¹' (extChartAt (𝓡 (Module.finrank ℝ ℝ)) y).source) =
      prodToEuclidean k ''
        ((extChartAt (𝓡 k).tangent x).target ∩
          (extChartAt (𝓡 k).tangent x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℝ) y).source)) := by
  letI := euclideanChartedSpaceModelProd k Q
  letI := euclideanChartedSpaceSelf (P := ℝ) (F := ℝ)
  let eE := prodToEuclidean k
  have hsym := extChartAt_modelProd_symm_coe k x
  have hsrcy := extChartAt_euclidean_source (F := ℝ) (P := ℝ) y
  have htgt := extChartAt_modelProd_target k x
  ext z
  constructor
  · intro hz
    have hzT : z ∈ (extChartAt (𝓡 (2 * k)) x).target := hz.1
    rw [htgt] at hzT
    rcases hzT with ⟨w, hw, rfl⟩
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    have hzw : (extChartAt (𝓡 (2 * k)) x).symm (eE w) =
        (extChartAt (𝓡 k).tangent x).symm w := by
      rw [hsym]; simp [eE]
    have hmem : f ((extChartAt (𝓡 (2 * k)) x).symm (eE w)) ∈
        (extChartAt (𝓡 (Module.finrank ℝ ℝ)) y).source := hz.2
    rw [hzw, hsrcy] at hmem
    exact hmem
  · intro hz
    rcases hz with ⟨w, hw, rfl⟩
    constructor
    · rw [htgt]
      exact ⟨w, hw.1, rfl⟩
    · have hzw : (extChartAt (𝓡 (2 * k)) x).symm (eE w) =
          (extChartAt (𝓡 k).tangent x).symm w := by
        rw [hsym]; simp [eE]
      have hmem : f ((extChartAt (𝓡 k).tangent x).symm w) ∈ (extChartAt 𝓘(ℝ) y).source := hw.2
      rw [← hzw, ← hsrcy] at hmem
      exact hmem

theorem contMDiff_after_modelProd {f : Q → ℝ}
    (hf : ContMDiff (𝓡 k).tangent 𝓘(ℝ) ∞ f) :
    letI := euclideanChartedSpaceModelProd k Q
    letI := euclideanChartedSpaceModelProd_isManifold k Q
    letI := euclideanChartedSpaceSelf (P := ℝ) (F := ℝ)
    letI := euclideanChartedSpaceSelf_isManifold (P := ℝ) (F := ℝ)
    ContMDiff (𝓡 (2 * k)) (𝓡 (Module.finrank ℝ ℝ)) ∞ f := by
  letI := euclideanChartedSpaceModelProd k Q
  letI := euclideanChartedSpaceModelProd_isManifold k Q
  letI := euclideanChartedSpaceSelf (P := ℝ) (F := ℝ)
  letI := euclideanChartedSpaceSelf_isManifold (P := ℝ) (F := ℝ)
  rw [contMDiff_iff]
  refine ⟨hf.continuous, ?_⟩
  intro x y
  have hfold := (contMDiff_iff.mp hf).2 x y
  have hfun := extChartAt_comp_modelProd k f x y
  have hdom := extChartAt_comp_modelProd_domain k f x y
  let eE := prodToEuclidean k
  let eE' := toEuclideanCLM ℝ
  have hlin :
      ContDiffOn ℝ ∞
        (eE' ∘ (extChartAt 𝓘(ℝ) y ∘ f ∘ (extChartAt (𝓡 k).tangent x).symm) ∘ eE.symm)
        (eE '' ((extChartAt (𝓡 k).tangent x).target ∩
          (extChartAt (𝓡 k).tangent x).symm ⁻¹' (f ⁻¹' (extChartAt 𝓘(ℝ) y).source))) :=
    eE'.contDiff.comp_contDiffOn <|
      hfold.comp eE.symm.contDiff.contDiffOn fun z hz => by
        rcases hz with ⟨w, hw, rfl⟩
        simpa [eE] using hw
  rw [hfun, hdom]
  exact hlin

theorem isRegularValue_after_modelProd {f : Q → ℝ} {c : ℝ}
    (hf : ContMDiff (𝓡 k).tangent 𝓘(ℝ) ∞ f)
    (hc : IsRegularValue (𝓡 k).tangent 𝓘(ℝ) f c) :
    letI := euclideanChartedSpaceModelProd k Q
    letI := euclideanChartedSpaceModelProd_isManifold k Q
    letI := euclideanChartedSpaceSelf (P := ℝ) (F := ℝ)
    letI := euclideanChartedSpaceSelf_isManifold (P := ℝ) (F := ℝ)
    IsRegularValue (𝓡 (2 * k)) (𝓡 (Module.finrank ℝ ℝ)) f c := by
  letI := euclideanChartedSpaceModelProd k Q
  letI := euclideanChartedSpaceModelProd_isManifold k Q
  letI := euclideanChartedSpaceSelf (P := ℝ) (F := ℝ)
  letI := euclideanChartedSpaceSelf_isManifold (P := ℝ) (F := ℝ)
  intro x hx
  have hfold := hc x hx
  have hfnew := contMDiff_after_modelProd k hf
  have hdiffOld : MDifferentiableAt (𝓡 k).tangent 𝓘(ℝ) f x :=
    hf.mdifferentiableAt (by simp)
  have hdiffNew : MDifferentiableAt (𝓡 (2 * k)) (𝓡 (Module.finrank ℝ ℝ)) f x :=
    hfnew.mdifferentiableAt (by simp)
  have hpI : (𝓡 k).tangent.IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  have hpE : (𝓡 (2 * k)).IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  have holdFDeriv :
      HasFDerivAt (writtenInExtChartAt (𝓡 k).tangent 𝓘(ℝ) x f)
        (mfderiv (𝓡 k).tangent 𝓘(ℝ) f x) (extChartAt (𝓡 k).tangent x x) :=
    writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint hpI hdiffOld.hasMFDerivAt
  let eE := prodToEuclidean k
  let eE' := toEuclideanCLM ℝ
  let L : EuclideanSpace ℝ (Fin (2 * k)) →L[ℝ]
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) := eE.symm
  let L' : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ ℝ)) := eE'
  have hwritten :
      writtenInExtChartAt (𝓡 (2 * k)) (𝓡 (Module.finrank ℝ ℝ)) x f =
        eE' ∘ writtenInExtChartAt (𝓡 k).tangent 𝓘(ℝ) x f ∘ eE.symm :=
    extChartAt_comp_modelProd k f x (f x)
  have hcenter :
      extChartAt (𝓡 (2 * k)) x x = eE (extChartAt (𝓡 k).tangent x x) := by
    rw [extChartAt_modelProd_coe]; rfl
  have hR : HasFDerivAt (⇑eE.symm) L (eE (extChartAt (𝓡 k).tangent x x)) := L.hasFDerivAt
  have hLpt : HasFDerivAt (⇑eE') L'
      (writtenInExtChartAt (𝓡 k).tangent 𝓘(ℝ) x f (extChartAt (𝓡 k).tangent x x)) :=
    L'.hasFDerivAt
  have hold' :
      HasFDerivAt (writtenInExtChartAt (𝓡 k).tangent 𝓘(ℝ) x f)
        (mfderiv (𝓡 k).tangent 𝓘(ℝ) f x) (eE.symm (eE (extChartAt (𝓡 k).tangent x x))) := by
    simpa using holdFDeriv
  have hmid :
      HasFDerivAt (writtenInExtChartAt (𝓡 k).tangent 𝓘(ℝ) x f ∘ ⇑eE.symm)
        ((mfderiv (𝓡 k).tangent 𝓘(ℝ) f x).comp L)
        (eE (extChartAt (𝓡 k).tangent x x)) :=
    HasFDerivAt.comp (eE (extChartAt (𝓡 k).tangent x x)) hold' hR
  have hL' : HasFDerivAt (⇑eE') L'
      ((writtenInExtChartAt (𝓡 k).tangent 𝓘(ℝ) x f ∘ ⇑eE.symm)
        (eE (extChartAt (𝓡 k).tangent x x))) := by
    simpa using hLpt
  have hcomp :
      HasFDerivAt
        (eE' ∘ writtenInExtChartAt (𝓡 k).tangent 𝓘(ℝ) x f ∘ eE.symm)
        (L'.comp ((mfderiv (𝓡 k).tangent 𝓘(ℝ) f x).comp L))
        (eE (extChartAt (𝓡 k).tangent x x)) :=
    HasFDerivAt.comp (eE (extChartAt (𝓡 k).tangent x x)) hL' hmid
  have hnewFDeriv :
      HasFDerivAt
        (writtenInExtChartAt (𝓡 (2 * k)) (𝓡 (Module.finrank ℝ ℝ)) x f)
        (L'.comp ((mfderiv (𝓡 k).tangent 𝓘(ℝ) f x).comp L))
        (extChartAt (𝓡 (2 * k)) x x) := by
    rw [hwritten, hcenter]
    exact hcomp
  have hmf :
      mfderiv (𝓡 (2 * k)) (𝓡 (Module.finrank ℝ ℝ)) f x =
        L'.comp ((mfderiv (𝓡 k).tangent 𝓘(ℝ) f x).comp L) := by
    have hHas :=
      writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint (I := 𝓡 (2 * k))
        (J := 𝓡 (Module.finrank ℝ ℝ)) (f := f) (p := x) hpE hdiffNew.hasMFDerivAt
    exact HasFDerivAt.unique hHas hnewFDeriv
  rw [hmf]
  exact (eE'.surjective.comp hfold).comp eE.symm.surjective

theorem id_isSmoothEmbedding_modelProd_to_tangent :
    letI := euclideanChartedSpaceModelProd k Q
    letI := euclideanChartedSpaceModelProd_isManifold k Q
    IsSmoothEmbedding (𝓡 (2 * k)) (𝓡 k).tangent ∞ (id : Q → Q) := by
  letI := euclideanChartedSpaceModelProd k Q
  letI := euclideanChartedSpaceModelProd_isManifold k Q
  have hid : ContMDiff (𝓡 (2 * k)) (𝓡 k).tangent ∞ (id : Q → Q) := by
    rw [contMDiff_iff]
    refine ⟨continuous_id, ?_⟩
    intro x y
    let eE := prodToEuclidean k
    have hidOld := (contMDiff_iff.mp (contMDiff_id (I := (𝓡 k).tangent) (n := ∞))).2 x y
    have hsym := extChartAt_modelProd_symm_coe k x
    have htgt := extChartAt_modelProd_target k x
    have hfun :
        extChartAt (𝓡 k).tangent y ∘ id ∘ (extChartAt (𝓡 (2 * k)) x).symm =
          (extChartAt (𝓡 k).tangent y ∘ id ∘ (extChartAt (𝓡 k).tangent x).symm) ∘ eE.symm := by
      funext z
      rw [hsym]
      rfl
    have hdom :
        (extChartAt (𝓡 (2 * k)) x).target ∩
            (extChartAt (𝓡 (2 * k)) x).symm ⁻¹'
              (id ⁻¹' (extChartAt (𝓡 k).tangent y).source) =
          eE '' ((extChartAt (𝓡 k).tangent x).target ∩
            (extChartAt (𝓡 k).tangent x).symm ⁻¹'
              (id ⁻¹' (extChartAt (𝓡 k).tangent y).source)) := by
      ext z
      constructor
      · intro hz
        have hzT : z ∈ (extChartAt (𝓡 (2 * k)) x).target := hz.1
        rw [htgt] at hzT
        rcases hzT with ⟨w, hw, rfl⟩
        refine ⟨w, ⟨hw, ?_⟩, rfl⟩
        have hzw : (extChartAt (𝓡 (2 * k)) x).symm (eE w) =
            (extChartAt (𝓡 k).tangent x).symm w := by
          rw [hsym]; simp [eE]
        have hmem : (extChartAt (𝓡 (2 * k)) x).symm (eE w) ∈
            (extChartAt (𝓡 k).tangent y).source := hz.2
        rw [hzw] at hmem
        exact hmem
      · intro hz
        rcases hz with ⟨w, hw, rfl⟩
        constructor
        · rw [htgt]
          exact ⟨w, hw.1, rfl⟩
        · have hzw : (extChartAt (𝓡 (2 * k)) x).symm (eE w) =
              (extChartAt (𝓡 k).tangent x).symm w := by
            rw [hsym]; simp [eE]
          have hmem : (extChartAt (𝓡 k).tangent x).symm w ∈
              (extChartAt (𝓡 k).tangent y).source := hw.2
          rw [← hzw] at hmem
          exact hmem
    have hlin :
        ContDiffOn ℝ ∞
          ((extChartAt (𝓡 k).tangent y ∘ id ∘ (extChartAt (𝓡 k).tangent x).symm) ∘ eE.symm)
          (eE '' ((extChartAt (𝓡 k).tangent x).target ∩
            (extChartAt (𝓡 k).tangent x).symm ⁻¹'
              (id ⁻¹' (extChartAt (𝓡 k).tangent y).source))) :=
      hidOld.comp eE.symm.contDiff.contDiffOn fun z hz => by
        rcases hz with ⟨w, hw, rfl⟩
        simpa [eE] using hw
    rw [hfun, hdom]
    exact hlin
  refine ⟨?_, IsEmbedding.id⟩
  rw [is_immersion_iff_forall_injective_mfderiv hid]
  intro x
  have hdiff : MDifferentiableAt (𝓡 (2 * k)) (𝓡 k).tangent (id : Q → Q) x :=
    hid.mdifferentiableAt (by simp)
  have hpE : (𝓡 (2 * k)).IsInteriorPoint x := BoundarylessManifold.isInteriorPoint
  let eE := prodToEuclidean k
  let Lmap : EuclideanSpace ℝ (Fin (2 * k)) →L[ℝ]
      EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k) := eE.symm
  have hHas :=
    writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint (I := 𝓡 (2 * k))
      (J := (𝓡 k).tangent) (f := (id : Q → Q)) (p := x) hpE hdiff.hasMFDerivAt
  have heq : EqOn (writtenInExtChartAt (𝓡 (2 * k)) (𝓡 k).tangent x (id : Q → Q))
      eE.symm (extChartAt (𝓡 (2 * k)) x).target := by
    intro z hz
    have hsym := extChartAt_modelProd_symm_coe k x
    have htgt := extChartAt_modelProd_target k x
    have : z ∈ eE '' (extChartAt (𝓡 k).tangent x).target := by
      rwa [← htgt]
    rcases this with ⟨w, hw, rfl⟩
    have hzw : (extChartAt (𝓡 (2 * k)) x).symm (eE w) =
        (extChartAt (𝓡 k).tangent x).symm w := by
      rw [hsym]; simp [eE]
    have hright := (extChartAt (𝓡 k).tangent x).right_inv hw
    calc
      writtenInExtChartAt (𝓡 (2 * k)) (𝓡 k).tangent x (id : Q → Q) (eE w) =
          (extChartAt (𝓡 k).tangent x)
            ((extChartAt (𝓡 (2 * k)) x).symm (eE w)) := rfl
      _ = (extChartAt (𝓡 k).tangent x) ((extChartAt (𝓡 k).tangent x).symm w) := by
        rw [hzw]
      _ = w := hright
      _ = eE.symm (eE w) := by simp
  have hlin : HasFDerivAt (⇑eE.symm) Lmap (extChartAt (𝓡 (2 * k)) x x) := Lmap.hasFDerivAt
  have hnhds : (extChartAt (𝓡 (2 * k)) x).target ∈ 𝓝 (extChartAt (𝓡 (2 * k)) x x) :=
    extChartAt_target_mem_nhds (I := 𝓡 (2 * k)) x
  have hHas' : HasFDerivAt
      (writtenInExtChartAt (𝓡 (2 * k)) (𝓡 k).tangent x (id : Q → Q)) Lmap
      (extChartAt (𝓡 (2 * k)) x x) :=
    hlin.congr_of_eventuallyEq (Filter.eventually_of_mem hnhds fun z hz => heq hz)
  have hmf : mfderiv (𝓡 (2 * k)) (𝓡 k).tangent (id : Q → Q) x = Lmap :=
    HasFDerivAt.unique hHas hHas'
  rw [hmf]
  exact eE.symm.injective

end Problem56SelfModel
