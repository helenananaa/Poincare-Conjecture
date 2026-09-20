import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16

/-!
C∞ Euclidean model transport for a boundaryless finite-dimensional real source.

Theorem 5.48's atlas bridges are stated at outer-top (`⊤`/`ω`) regularity.  This file repeats the
same constructions at `∞`, which is the regularity of a genuine smooth source.  Helpers live in a
private namespace so they cannot be mistaken for the analytic Theorem 5.48 owners.
-/

open scoped ContDiff Manifold
open Manifold Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Theorem630
namespace SmoothModelTransport

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M] [I.Boundaryless]
  [BoundarylessManifold I M]

/-- Interior-shrunk extended chart, copied from Theorem 5.48 at C∞ regularity. -/
def boundarylessLocalChart (x : M) : OpenPartialHomeomorph M E where
  toPartialEquiv :=
    { toFun := extChartAt I x
      invFun := (extChartAt I x).symm
      source := (extChartAt I x) ⁻¹' interior (extChartAt I x).target ∩ (extChartAt I x).source
      target := interior (extChartAt I x).target
      map_source' := fun _ hy ↦ hy.1
      map_target' := by
        intro y hy
        have hyTarget : y ∈ (extChartAt I x).target := interior_subset hy
        have hySource : (extChartAt I x).symm y ∈ (extChartAt I x).source :=
          (extChartAt I x).map_target hyTarget
        have hyEq : extChartAt I x ((extChartAt I x).symm y) = y :=
          PartialEquiv.right_inv (extChartAt I x) hyTarget
        refine ⟨?_, hySource⟩
        show extChartAt I x ((extChartAt I x).symm y) ∈ interior (extChartAt I x).target
        exact hyEq.symm ▸ hy
      left_inv' := fun _ hy ↦ PartialEquiv.left_inv (extChartAt I x) hy.2
      right_inv' := fun _ hy ↦
        PartialEquiv.right_inv (extChartAt I x) (interior_subset hy) }
  open_source := by
    let s : Set E := interior (extChartAt I x).target
    have hOpen :
        IsOpen ((chartAt H x).source ∩ (chartAt H x).extend I ⁻¹' s) :=
      (chartAt H x).isOpen_extend_preimage isOpen_interior
    simpa [s, extChartAt, Set.inter_comm] using hOpen
  open_target := isOpen_interior
  continuousOn_toFun := by
    intro y hy
    exact ((continuousOn_extChartAt x) y hy.2).mono fun _ hz ↦ hz.2
  continuousOn_invFun := by
    intro y hy
    exact ((continuousOn_extChartAt_symm x) y (interior_subset hy)).mono fun _ hz ↦
      interior_subset hz

/-- Self-model atlas on a C∞ boundaryless source. -/
noncomputable abbrev boundarylessModelChartedSpace : ChartedSpace E M where
  atlas := Set.range fun x : M ↦ boundarylessLocalChart (I := I) x
  chartAt := fun x : M ↦ boundarylessLocalChart (I := I) x
  mem_chart_source := by
    intro x
    refine ⟨?_, ?_⟩
    · exact (I.isInteriorPoint_iff).mp BoundarylessManifold.isInteriorPoint
    · rw [extChartAt_source I]
      exact mem_chart_source H x
  chart_mem_atlas := fun x ↦ ⟨x, rfl⟩

lemma boundarylessModelIsManifold :
    let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
    IsManifold (modelWithCornersSelf ℝ E) ∞ M := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
  exact isManifold_of_contDiffOn (modelWithCornersSelf ℝ E) ∞ M <| by
    intro e e' he he'
    rcases he with ⟨x, rfl⟩
    rcases he' with ⟨y, rfl⟩
    refine (I.contDiffOn_extendCoordChange
        (IsManifold.chart_mem_maximalAtlas x)
        (IsManifold.chart_mem_maximalAtlas y)).mono ?_
    intro z hz
    simp [boundarylessLocalChart, extChartAt, ModelWithCorners.extendCoordChange,
      Set.preimage_comp] at hz ⊢
    rcases hz with ⟨hzx, hrest⟩
    rcases hrest with ⟨_, hzSource⟩
    refine ⟨?_, hzSource⟩
    refine ⟨⟨I.symm z, I.right_inv (interior_subset hzx.1)⟩, ?_⟩
    simpa [(chartAt H x).open_target.interior_eq] using interior_subset hzx.2

lemma mem_boundarylessLocalChart_source (x : M) :
    x ∈ (boundarylessLocalChart (I := I) x).source := by
  refine ⟨?_, ?_⟩
  · exact (I.isInteriorPoint_iff).mp BoundarylessManifold.isInteriorPoint
  · rw [extChartAt_source I]
    exact mem_chart_source H x

lemma boundarylessAmbientId_isSmoothEmbedding :
    let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
    let _ : IsManifold (modelWithCornersSelf ℝ E) ∞ M :=
      boundarylessModelIsManifold (I := I)
    IsSmoothEmbedding (modelWithCornersSelf ℝ E) I ∞ (id : M → M) := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
  let _ : IsManifold (modelWithCornersSelf ℝ E) ∞ M :=
    boundarylessModelIsManifold (I := I)
  refine ⟨?_, Topology.IsEmbedding.id⟩
  refine ⟨PUnit.{uE + 1}, inferInstance, inferInstance, ?_⟩
  intro x
  let domChart : OpenPartialHomeomorph M E := boundarylessLocalChart (I := I) x
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    continuousAt_id
    (ContinuousLinearEquiv.prodUnique ℝ E PUnit.{uE + 1})
    domChart
    (chartAt H x)
    (mem_boundarylessLocalChart_source (I := I) x)
    (mem_chart_source H x)
    ?_
    (IsManifold.chart_mem_maximalAtlas x)
    ?_
  · simpa [domChart, boundarylessModelChartedSpace] using!
      (IsManifold.chart_mem_maximalAtlas x :
        chartAt E x ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
  · intro u hu
    have hu_target : u ∈ domChart.target := by
      simpa [domChart, OpenPartialHomeomorph.extend_target', modelWithCornersSelf_coe] using hu
    simpa [domChart, boundarylessLocalChart, extChartAt, Function.comp,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm] using
      domChart.right_inv hu_target

variable {m : ℕ}

/-- Ordered-basis identification `ℝ^m ≃L E`. -/
def euclideanContinuousLinearEquiv (hm : Module.finrank ℝ E = m)
    (b : Module.Basis (Fin m) ℝ E) :
    EuclideanSpace ℝ (Fin m) ≃L[ℝ] E :=
  let e : E ≃ₗ[ℝ] Fin m → ℝ := b.equivFun
  (EuclideanSpace.equiv (Fin m) ℝ).trans e.symm.toContinuousLinearEquiv

def euclideanModelChart (hm : Module.finrank ℝ E = m)
    (b : Module.Basis (Fin m) ℝ E) :
    OpenPartialHomeomorph E (EuclideanSpace ℝ (Fin m)) :=
  (euclideanContinuousLinearEquiv hm b).symm.toHomeomorph.toOpenPartialHomeomorph

lemma euclideanModelChart_source (hm : Module.finrank ℝ E = m)
    (b : Module.Basis (Fin m) ℝ E) :
    (euclideanModelChart hm b).source = univ := by
  simp [euclideanModelChart]

lemma euclideanModelChart_target (hm : Module.finrank ℝ E = m)
    (b : Module.Basis (Fin m) ℝ E) :
    (euclideanModelChart hm b).target = univ := by
  simp [euclideanModelChart]

lemma euclideanTransition_mem_contDiffGroupoid
    (hm : Module.finrank ℝ E = m) (b : Module.Basis (Fin m) ℝ E)
    {e : OpenPartialHomeomorph E E}
    (he : e ∈ contDiffGroupoid ∞ (modelWithCornersSelf ℝ E)) :
    let eModel := euclideanModelChart hm b
    (eModel.symm.trans e).trans eModel ∈ contDiffGroupoid ∞ (𝓡 m) := by
  let eModel := euclideanModelChart hm b
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid] at he ⊢
  have he_left : ContDiffOn ℝ ∞ (e : E → E) e.source := by simpa using he.1
  have he_right : ContDiffOn ℝ ∞ (e.symm : E → E) e.target := by simpa using he.2
  have heModel_contDiff :
      ContDiff ℝ ∞ (eModel : E → EuclideanSpace ℝ (Fin m)) := by
    simpa [eModel, euclideanModelChart, euclideanContinuousLinearEquiv] using
      (euclideanContinuousLinearEquiv hm b).symm.toContinuousLinearMap.contDiff
  have heModel_symm_contDiff :
      ContDiff ℝ ∞ (eModel.symm : EuclideanSpace ℝ (Fin m) → E) := by
    simpa [eModel, euclideanModelChart, euclideanContinuousLinearEquiv] using
      (euclideanContinuousLinearEquiv hm b).toContinuousLinearMap.contDiff
  have hsource :
      eModel.symm ⁻¹' e.source = ((eModel.symm.trans e).trans eModel).source := by
    ext x
    simp [eModel, euclideanModelChart_source, euclideanModelChart_target]
  have htarget :
      eModel.symm ⁻¹' e.target = ((eModel.symm.trans e).trans eModel).target := by
    ext x
    simp [eModel, euclideanModelChart_source, euclideanModelChart_target]
  constructor
  · have hmid :
        ContDiffOn ℝ ∞
          (fun x : EuclideanSpace ℝ (Fin m) ↦ e (eModel.symm x))
          (eModel.symm ⁻¹' e.source) :=
      he_left.comp heModel_symm_contDiff.contDiffOn fun _ hx ↦ hx
    have hfinal :
        ContDiffOn ℝ ∞ (↑eModel ∘ ↑e ∘ ↑eModel.symm)
          (eModel.symm ⁻¹' e.source) :=
      (heModel_contDiff.contDiffOn : ContDiffOn ℝ ∞ eModel univ).comp hmid fun _ _ ↦
        mem_univ _
    have hTsource :
        ContDiffOn ℝ ∞ (↑eModel ∘ ↑e ∘ ↑eModel.symm)
          ((eModel.symm.trans e).trans eModel).source := by
      rw [← hsource]
      exact hfinal
    simpa [eModel, Function.comp, modelWithCornersSelf_coe] using hTsource
  · have hmid :
        ContDiffOn ℝ ∞
          (fun x : EuclideanSpace ℝ (Fin m) ↦ e.symm (eModel.symm x))
          (eModel.symm ⁻¹' e.target) :=
      he_right.comp heModel_symm_contDiff.contDiffOn fun _ hx ↦ hx
    have hfinal :
        ContDiffOn ℝ ∞ ((↑eModel ∘ ↑e.symm) ∘ ↑eModel.symm)
          (eModel.symm ⁻¹' e.target) :=
      (heModel_contDiff.contDiffOn : ContDiffOn ℝ ∞ eModel univ).comp hmid fun _ _ ↦
        mem_univ _
    have hTtarget :
        ContDiffOn ℝ ∞ ((↑eModel ∘ ↑e.symm) ∘ ↑eModel.symm)
          ((eModel.symm.trans e).trans eModel).target := by
      rw [← htarget]
      exact hfinal
    simpa [eModel, Function.comp, modelWithCornersSelf_coe,
      OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc] using hTtarget

noncomputable abbrev euclideanChartedSpace (hm : Module.finrank ℝ E = m)
    (b : Module.Basis (Fin m) ℝ E) :
    ChartedSpace (EuclideanSpace ℝ (Fin m)) M := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
  let eModel := euclideanModelChart hm b
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) E :=
    eModel.singletonChartedSpace (euclideanModelChart_source hm b)
  exact ChartedSpace.comp (EuclideanSpace ℝ (Fin m)) E M

lemma euclideanIsManifold (hm : Module.finrank ℝ E = m)
    (b : Module.Basis (Fin m) ℝ E) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) M :=
      euclideanChartedSpace (I := I) hm b
    IsManifold (𝓡 m) ∞ M := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
  let _ : IsManifold (modelWithCornersSelf ℝ E) ∞ M :=
    boundarylessModelIsManifold (I := I)
  let eModel := euclideanModelChart hm b
  have heModel_source : eModel.source = univ := euclideanModelChart_source hm b
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) E :=
    eModel.singletonChartedSpace heModel_source
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) M :=
    euclideanChartedSpace (I := I) hm b
  have hGroupoid : HasGroupoid M (contDiffGroupoid ∞ (𝓡 m)) := by
    refine ⟨?_⟩
    rintro _ _ ⟨f, hf, c, hc, rfl⟩ ⟨f', hf', c', hc', rfl⟩
    have hcEq : c = eModel := by
      simpa [eModel] using
        eModel.singletonChartedSpace_mem_atlas_eq heModel_source c hc
    have hc'Eq : c' = eModel := by
      simpa [eModel] using
        eModel.singletonChartedSpace_mem_atlas_eq heModel_source c' hc'
    subst c
    subst c'
    have hcompat_old :
        f.symm.trans f' ∈ contDiffGroupoid ∞ (modelWithCornersSelf ℝ E) :=
      HasGroupoid.compatible hf hf'
    simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      euclideanTransition_mem_contDiffGroupoid hm b hcompat_old
  let _ : HasGroupoid M (contDiffGroupoid ∞ (𝓡 m)) := hGroupoid
  exact IsManifold.mk' (𝓡 m) ∞ M

lemma euclideanChart_mem_maximalAtlas (hm : Module.finrank ℝ E = m)
    (b : Module.Basis (Fin m) ℝ E)
    {chart : OpenPartialHomeomorph M E}
    (hchart :
      let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
      chart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M) :
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) M :=
      euclideanChartedSpace (I := I) hm b
    let _ : IsManifold (𝓡 m) ∞ M := euclideanIsManifold (I := I) hm b
    let eModel := euclideanModelChart hm b
    chart.trans eModel ∈ IsManifold.maximalAtlas (𝓡 m) ∞ M := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
  let _ : IsManifold (modelWithCornersSelf ℝ E) ∞ M :=
    boundarylessModelIsManifold (I := I)
  let eModel := euclideanModelChart hm b
  have heModel_source : eModel.source = univ := euclideanModelChart_source hm b
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) E :=
    eModel.singletonChartedSpace heModel_source
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) M :=
    euclideanChartedSpace (I := I) hm b
  let _ : IsManifold (𝓡 m) ∞ M := euclideanIsManifold (I := I) hm b
  rw [IsManifold.mem_maximalAtlas_iff]
  intro c hc
  rcases hc with ⟨f, hf, c', hc', rfl⟩
  have hc'Eq : c' = eModel := by
    simpa [eModel] using
      eModel.singletonChartedSpace_mem_atlas_eq heModel_source c' hc'
  subst c'
  have hleft_old : chart.symm.trans f ∈
      contDiffGroupoid ∞ (modelWithCornersSelf ℝ E) :=
    (IsManifold.mem_maximalAtlas_iff.mp hchart) f hf |>.1
  have hright_old : f.symm.trans chart ∈
      contDiffGroupoid ∞ (modelWithCornersSelf ℝ E) :=
    (IsManifold.mem_maximalAtlas_iff.mp hchart) f hf |>.2
  constructor
  · simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      euclideanTransition_mem_contDiffGroupoid hm b hleft_old
  · simpa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.trans_assoc, eModel] using
      euclideanTransition_mem_contDiffGroupoid hm b hright_old

lemma euclideanBoundarylessId_isSmoothEmbedding (hm : Module.finrank ℝ E = m)
    (b : Module.Basis (Fin m) ℝ E) :
    let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
    let _ : IsManifold (modelWithCornersSelf ℝ E) ∞ M :=
      boundarylessModelIsManifold (I := I)
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) M :=
      euclideanChartedSpace (I := I) hm b
    let _ : IsManifold (𝓡 m) ∞ M := euclideanIsManifold (I := I) hm b
    IsSmoothEmbedding (𝓡 m) (modelWithCornersSelf ℝ E) ∞ (id : M → M) := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
  let _ : IsManifold (modelWithCornersSelf ℝ E) ∞ M :=
    boundarylessModelIsManifold (I := I)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) M :=
    euclideanChartedSpace (I := I) hm b
  let _ : IsManifold (𝓡 m) ∞ M := euclideanIsManifold (I := I) hm b
  let eModel := euclideanModelChart hm b
  refine ⟨?_, Topology.IsEmbedding.id⟩
  refine ⟨PUnit, inferInstance, inferInstance, ?_⟩
  intro x
  let codChart : OpenPartialHomeomorph M E := boundarylessLocalChart (I := I) x
  let domChart : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m)) :=
    codChart.trans eModel
  let equiv : (EuclideanSpace ℝ (Fin m) × PUnit.{uE + 1}) ≃L[ℝ] E :=
    (ContinuousLinearEquiv.prodUnique ℝ (EuclideanSpace ℝ (Fin m)) PUnit.{uE + 1}).trans
      (euclideanContinuousLinearEquiv hm b)
  have hcodChart :
      codChart ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M := by
    simpa [codChart, boundarylessModelChartedSpace] using!
      (IsManifold.chart_mem_maximalAtlas x :
        chartAt E x ∈ IsManifold.maximalAtlas (modelWithCornersSelf ℝ E) ∞ M)
  have hdomChart : domChart ∈ IsManifold.maximalAtlas (𝓡 m) ∞ M := by
    simpa [domChart, codChart, eModel] using
      euclideanChart_mem_maximalAtlas (I := I) hm b hcodChart
  refine IsImmersionAtOfComplement.mk_of_continuousAt
    continuousAt_id equiv domChart codChart ?_ ?_ hdomChart hcodChart ?_
  · have hx_cod := mem_boundarylessLocalChart_source (I := I) x
    refine ⟨hx_cod, ?_⟩
    simp [eModel, euclideanModelChart_source]
  · exact mem_boundarylessLocalChart_source (I := I) x
  · intro u hu
    have hu_target :
        euclideanContinuousLinearEquiv hm b u ∈ codChart.target := by
      simpa [domChart, codChart, eModel, OpenPartialHomeomorph.extend_target,
        OpenPartialHomeomorph.trans_target, euclideanModelChart,
        euclideanContinuousLinearEquiv] using hu
    simpa [equiv, domChart, codChart, eModel, Function.comp,
      euclideanModelChart, euclideanContinuousLinearEquiv,
      OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm] using
      codChart.right_inv hu_target

lemma euclideanAmbientId_isSmoothEmbedding (hm : Module.finrank ℝ E = m)
    (b : Module.Basis (Fin m) ℝ E) :
    let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
    let _ : IsManifold (modelWithCornersSelf ℝ E) ∞ M :=
      boundarylessModelIsManifold (I := I)
    let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) M :=
      euclideanChartedSpace (I := I) hm b
    let _ : IsManifold (𝓡 m) ∞ M := euclideanIsManifold (I := I) hm b
    IsSmoothEmbedding (𝓡 m) I ∞ (id : M → M) := by
  let _ : ChartedSpace E M := boundarylessModelChartedSpace (I := I)
  let _ : IsManifold (modelWithCornersSelf ℝ E) ∞ M :=
    boundarylessModelIsManifold (I := I)
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin m)) M :=
    euclideanChartedSpace (I := I) hm b
  let _ : IsManifold (𝓡 m) ∞ M := euclideanIsManifold (I := I) hm b
  exact IsSmoothEmbedding.comp
    (boundarylessAmbientId_isSmoothEmbedding (I := I))
    (euclideanBoundarylessId_isSmoothEmbedding (I := I) hm b)

end SmoothModelTransport
end Theorem630
