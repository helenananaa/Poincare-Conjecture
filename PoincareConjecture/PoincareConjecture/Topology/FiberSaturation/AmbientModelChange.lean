import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.AmbientModelChange
open Set Function Manifold ChartedSpace
open scoped Manifold ContDiff Topology

private def modelDiffeomorph
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    H ≃ₘ⟮I, 𝓘(ℝ,E)⟯ E :=
  { toEquiv := I.toHomeomorph.toEquiv
    contMDiff_toFun := I.contMDiff
    contMDiff_invFun := by
      rw [← contMDiffOn_univ]
      convert I.contMDiffOn_symm using 1
      · funext x
        rfl
      · simp [I.range_eq_univ] }

private theorem modelDiffeomorph_coe
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    (modelDiffeomorph I : H → E) = I := by
  funext x
  rfl

private theorem modelDiffeomorph_symm_coe
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    ((modelDiffeomorph I).symm : E → H) = I.symm := by
  funext x
  rfl

/-- Rechart the original model space by its boundaryless model homeomorphism. -/
@[implicit_reducible] def modelChartedSpace
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    ChartedSpace E H := by
  let e := (modelDiffeomorph I).toHomeomorph.toOpenPartialHomeomorph
  have he : e.source = (univ : Set H) := by simp [e]
  exact e.singletonChartedSpace he

private theorem modelSpace_isManifold
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    letI : ChartedSpace E H := modelChartedSpace I
    IsManifold (𝓘(ℝ,E)) ∞ H := by
  letI : ChartedSpace E H := modelChartedSpace I
  apply isManifold_of_contDiffOn
  intro e e' he he'
  rcases he with ⟨rfl, rfl⟩
  rcases he' with ⟨rfl, rfl⟩
  simp [contDiffGroupoid, contDiffPregroupoid]
  have hcomp :
      (modelDiffeomorph I : H → E) ∘ (modelDiffeomorph I).symm = id := by
    funext x
    simp
  rw [hcomp]
  exact contDiff_id.contDiffOn

private theorem model_groupoid_lift
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    letI : ChartedSpace E H := modelChartedSpace I
    ∀ e : OpenPartialHomeomorph H H, e ∈ contDiffGroupoid ∞ I →
      LiftPropOn (StructureGroupoid.IsLocalStructomorphWithinAt
        (contDiffGroupoid ∞ (𝓘(ℝ,E))))
        (e : H → H) e.source := by
  letI : ChartedSpace E H := modelChartedSpace I
  letI : IsManifold (𝓘(ℝ,E)) ∞ H := modelSpace_isManifold I
  intro e he
  rw [isLocalStructomorphOn_contDiffGroupoid_iff]
  rcases he with ⟨he, he'⟩
  constructor
  · rw [contMDiffOn_iff]
    simp [extChartAt, modelChartedSpace, modelDiffeomorph]
    constructor
    · have hg :
          ContinuousOn (I ∘ e ∘ I.symm)
            (I.symm ⁻¹' e.source ∩ range I) := he.continuousOn
      have h1 : ContinuousOn (I ∘ e) e.source := by
        have hmap : MapsTo I e.source (I.symm ⁻¹' e.source ∩ range I) := by
          intro x hx
          refine ⟨?_, ?_⟩
          · simp [hx]
          · exact ⟨x, rfl⟩
        have htemp := hg.comp I.continuous.continuousOn hmap
        convert htemp using 1 <;> simp [Function.comp_assoc]
      have h2 : ContinuousOn (I.symm ∘ (I ∘ e)) e.source :=
        I.continuous_symm.continuousOn.comp h1 (by intro x hx; exact mem_univ _)
      have hcomp : I.symm ∘ I ∘ e = e := by
        funext x
        simp [Function.comp_apply]
      rw [hcomp] at h2
      exact h2
    · intro x y
      have hmono : I.symm ⁻¹' e.source ⊆ I.symm ⁻¹' e.source ∩ range I := by
        intro z hz
        exact ⟨hz, by rw [I.range_eq_univ]; trivial⟩
      convert he.mono hmono using 1
      funext z
      change I (e (I.symm z)) = I (e (I.symm z))
      rfl
      · ext z
        change I.symm z ∈ e.source ↔ I.symm z ∈ e.source
        rfl

  · rw [contMDiffOn_iff]
    simp [extChartAt, modelChartedSpace, modelDiffeomorph]
    constructor
    · have hg :
          ContinuousOn (I ∘ e.symm ∘ I.symm)
            (I.symm ⁻¹' e.target ∩ range I) := he'.continuousOn
      have h1 : ContinuousOn (I ∘ e.symm) e.target := by
        have hmap : MapsTo I e.target (I.symm ⁻¹' e.target ∩ range I) := by
          intro x hx
          refine ⟨?_, ?_⟩
          · simp [hx]
          · exact ⟨x, rfl⟩
        have htemp := hg.comp I.continuous.continuousOn hmap
        convert htemp using 1 <;> simp [Function.comp_assoc]
      have h2 : ContinuousOn (I.symm ∘ (I ∘ e.symm)) e.target :=
        I.continuous_symm.continuousOn.comp h1 (by intro x hx; exact mem_univ _)
      have hcomp : I.symm ∘ I ∘ e.symm = e.symm := by
        funext x
        simp [Function.comp_apply]
      rw [hcomp] at h2
      exact h2
    · intro x y
      have hmono : I.symm ⁻¹' e.target ⊆ I.symm ⁻¹' e.target ∩ range I := by
        intro z hz
        exact ⟨hz, by rw [I.range_eq_univ]; trivial⟩
      convert he'.mono hmono using 1
      funext z
      change I (e.symm (I.symm z)) = I (e.symm (I.symm z))
      rfl
      · ext z
        change I.symm z ∈ e.target ↔ I.symm z ∈ e.target
        rfl

/-- The composed atlas is smooth over the corresponding real normed self-model. -/
theorem standard_manifold_of_boundaryless_model
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [ChartedSpace H N] [IsManifold I ∞ N] :
    letI : ChartedSpace E H := modelChartedSpace I
    letI : ChartedSpace E N := ChartedSpace.comp E H N
    IsManifold (𝓘(ℝ,E)) ∞ N := by
  letI : ChartedSpace E H := modelChartedSpace I
  letI : IsManifold (𝓘(ℝ,E)) ∞ H := modelSpace_isManifold I
  letI : ChartedSpace E N := ChartedSpace.comp E H N
  letI : HasGroupoid N (contDiffGroupoid ∞ I) := inferInstance
  letI : HasGroupoid N (contDiffGroupoid ∞ (𝓘(ℝ,E))) :=
    StructureGroupoid.HasGroupoid.comp (contDiffGroupoid ∞ I) (model_groupoid_lift I)
  exact IsManifold.mk' (𝓘(ℝ,E)) ∞ N

/-- Recharting preserves the actual extended coordinate maps, including their domains. -/
theorem extChartAt_recharted_eq
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [ChartedSpace H N] [IsManifold I ∞ N] :
    letI : ChartedSpace E H := modelChartedSpace I
    letI : ChartedSpace E N := ChartedSpace.comp E H N
    ∀ x : N, extChartAt (𝓘(ℝ, E)) x = extChartAt I x := by
  letI : ChartedSpace E H := modelChartedSpace I
  letI : ChartedSpace E N := ChartedSpace.comp E H N
  intro x
  rw [extChartAt_comp]
  ext z <;> simp [extChartAt, modelChartedSpace, modelDiffeomorph] <;> rfl

/-- Change the ambient model by a diffeomorphism that is the identity on the underlying
points. The original topology is unchanged; neither smoothness direction is assumed. -/
def changeModel
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [ChartedSpace H N] [IsManifold I ∞ N] :
    letI : ChartedSpace E H := modelChartedSpace I
    letI : ChartedSpace E N := ChartedSpace.comp E H N
    N ≃ₘ⟮I, 𝓘(ℝ,E)⟯ N := by
  letI : ChartedSpace E H := modelChartedSpace I
  letI : ChartedSpace E N := ChartedSpace.comp E H N
  letI : IsManifold (𝓘(ℝ,E)) ∞ N := standard_manifold_of_boundaryless_model I
  have hid : ContMDiff I I ∞ (Equiv.refl N : N → N) := contMDiff_id
  refine { toEquiv := Equiv.refl N, contMDiff_toFun := ?_, contMDiff_invFun := ?_ }
  · rw [contMDiff_iff]
    simpa only [show (Equiv.refl N).symm = Equiv.refl N from rfl,
      extChartAt_recharted_eq I] using (contMDiff_iff.mp hid)
  · rw [contMDiff_iff]
    simpa only [show (Equiv.refl N).symm = Equiv.refl N from rfl,
      extChartAt_recharted_eq I] using (contMDiff_iff.mp hid)


end PoincareConjecture.Topology.FiberSaturation.AmbientModelChange
