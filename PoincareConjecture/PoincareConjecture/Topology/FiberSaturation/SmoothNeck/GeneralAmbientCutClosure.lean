import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.NativeCutClosure
import PoincareConjecture.Topology.FiberSaturation.AmbientModelChange
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
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

private abbrev modelChartedSpace := @PoincareConjecture.Topology.FiberSaturation.AmbientModelChange.modelChartedSpace
private abbrev standard_manifold_of_boundaryless_model := @PoincareConjecture.Topology.FiberSaturation.AmbientModelChange.standard_manifold_of_boundaryless_model
private abbrev ambientModelChange := @PoincareConjecture.Topology.FiberSaturation.AmbientModelChange.changeModel

private theorem transBoundaryless
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless] (e : E ≃L[ℝ] F) :
    (I.transContinuousLinearEquiv e).Boundaryless := by
  constructor
  rw [ModelWithCorners.transContinuousLinearEquiv_range, I.range_eq_univ,
    Set.image_univ]
  exact e.surjective.range_eq

private def ambientModelChangeTo
    {E F H N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [ChartedSpace H N] [IsManifold I ∞ N]
    (e : E ≃L[ℝ] F) :
    let K := I.transContinuousLinearEquiv e
    letI : K.Boundaryless := transBoundaryless I e
    letI : ChartedSpace F H := modelChartedSpace K
    letI : ChartedSpace F N := ChartedSpace.comp F H N
    N ≃ₘ⟮I, 𝓘(ℝ,F)⟯ N := by
  let K := I.transContinuousLinearEquiv e
  letI : K.Boundaryless := transBoundaryless I e
  letI : ChartedSpace F H := modelChartedSpace K
  letI : ChartedSpace F N := ChartedSpace.comp F H N
  exact (ContinuousLinearEquiv.toTransContinuousLinearEquiv I N e).trans
    (ambientModelChange K)

/-- A native neck cut cover constructs a smooth complementary closure in the original
three-dimensional boundaryless ambient model. The model change is constructed, not assumed.
The cut equations and frontier cover remain explicit geometric inputs. -/
theorem exists_smoothClosure_of_native_neck_cut_cover_of_finite_dimensional_model
    {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace N]
    (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [ChartedSpace H N] [IsManifold I ∞ N] [LocallyConnectedSpace N]
    (hdim : Module.finrank ℝ E = 3)
    {C : Set N} (hC : IsClosed C) {p : N} (hp : p ∉ C)
    (hcover : ∀ y ∈ frontier C, ∃ epsilon : ℝ, 0 < epsilon ∧
      ∃ Q : TopologicalSpace.Opens N,
      ∃ φ : Diffeomorph NativeCylinderModel I (nativeNeckDomain epsilon) Q ∞,
      ∃ c s : ℝ, c ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ ∧ (s = 1 ∨ s = -1) ∧
        (∀ z : nativeNeckDomain epsilon, (φ z : N) ∈ C ↔ s*(z.1.2 0-c) ≤ 0) ∧
        ∃ z : nativeNeckDomain epsilon, (φ z : N) = y ∧ z.1.2 0 = c) :
    ∃ cs : ChartedSpace (SmoothCollar.HalfSpace (EuclideanSpace ℝ (Fin 2)))
        (closure (connectedComponentIn Cᶜ p)),
      letI : ChartedSpace (SmoothCollar.HalfSpace (EuclideanSpace ℝ (Fin 2)))
        (closure (connectedComponentIn Cᶜ p)) := cs
      IsManifold (SmoothCollar.halfSpaceModel (EuclideanSpace ℝ (Fin 2))) ∞
        (closure (connectedComponentIn Cᶜ p)) ∧
      IsSmoothEmbedding (SmoothCollar.halfSpaceModel (EuclideanSpace ℝ (Fin 2))) I ∞
        (Subtype.val : closure (connectedComponentIn Cᶜ p) → N) ∧
      (Subtype.val : closure (connectedComponentIn Cᶜ p) → N) ''
        (SmoothCollar.halfSpaceModel (EuclideanSpace ℝ (Fin 2))).boundary
          (closure (connectedComponentIn Cᶜ p)) = frontier (connectedComponentIn Cᶜ p) ∧
      connectedComponentIn Cᶜ p = interior (closure (connectedComponentIn Cᶜ p)) := by
  let V := EuclideanSpace ℝ (Fin 2)
  let F := V × ℝ
  have hFdim : Module.finrank ℝ F = 3 := by
    simp [F, V, Module.finrank_prod]
  let e : E ≃L[ℝ] F :=
    ContinuousLinearEquiv.ofFinrankEq (hdim.trans hFdim.symm)
  let K := I.transContinuousLinearEquiv e
  letI : K.Boundaryless := transBoundaryless I e
  letI : ChartedSpace F H := modelChartedSpace K
  letI : ChartedSpace F N := ChartedSpace.comp F H N
  letI : IsManifold (𝓘(ℝ,F)) ∞ N := standard_manifold_of_boundaryless_model K
  let D : N ≃ₘ⟮I, 𝓘(ℝ,F)⟯ N := ambientModelChangeTo I e
  have hfront : frontier (connectedComponentIn Cᶜ p) ⊆ frontier C :=
    complementary_component_frontier_subset hC hp
  obtain ⟨cs, hman, hembedStd, hboundary, hinterior⟩ :=
    SmoothCollar.exists_smoothClosure_of_smoothCollar_cover
      (X := Sphere2) (V := V) (p := p) hC (by
        intro y hy
        have hyC : y ∈ frontier C := hfront hy
        obtain ⟨epsilon, heps, Q, φ, c, s, hc, hs, hcut, z, hzy, hzc⟩ :=
          hcover y hyC
        obtain ⟨Φ, hΦsrc, hΦside, hΦzero⟩ :=
          exists_smoothCollar_of_native_neck_cut I epsilon heps Q φ C c s hc hs hcut
        let Ψ := Φ.trans D.toPartialDiffeomorph
        have hD : ∀ x : N, D x = x := by
          intro x
          rfl
        have hΨsrc : Ψ.source = Φ.source := by
          simp [Ψ, Diffeomorph.toPartialDiffeomorph]
        refine ⟨Ψ, ?_, ?_, z.1.1, ?_⟩
        · rw [hΨsrc, hΦsrc]
        · intro w hw
          have hwΦ : w ∈ Φ.source := by rw [← hΨsrc]; exact hw
          simpa [Ψ, Diffeomorph.toPartialDiffeomorph, hD] using hΦside w hwΦ
        · change D (Φ (z.1.1, 0)) = y
          rw [hD, hΦzero]
          rw [← hzy]
          refine congrArg (fun w : nativeNeckDomain epsilon => (φ w : N)) ?_
          apply Subtype.ext
          have hax : nativeAxis c = z.1.2 := by
            refine PiLp.ext fun i => ?_
            have hi : i = 0 := Fin.eq_zero i
            subst hi
            exact (nativeAxis_zero c).trans hzc.symm
          dsimp [scalarToNative]
          exact Prod.ext rfl hax)
  refine ⟨cs, hman, ?_, hboundary, hinterior⟩
  letI : ChartedSpace (SmoothCollar.HalfSpace V) (closure (connectedComponentIn Cᶜ p)) := cs
  letI : IsManifold (SmoothCollar.halfSpaceModel V) ∞ (closure (connectedComponentIn Cᶜ p)) := hman
  let b : F ≃ₘ⟮𝓘(ℝ,F), I⟯ H :=
    e.symm.toDiffeomorph.trans (modelDiffeomorph I).symm
  have hDfun : (D : N → N) = id := rfl
  have hDinv : (D.symm : N → N) = id := rfl
  refine ⟨?_, hembedStd.isEmbedding⟩
  let hi := hembedStd.isImmersion
  apply IsImmersionOfComplement.isImmersion (F := hi.complement)
  intro x
  let h := hi.isImmersionOfComplement_complement x
  let ecod := h.codChart.trans b.toHomeomorph.toOpenPartialHomeomorph
  have hsrc : ecod.source = h.codChart.source := by simp [ecod]
  have hco : ContMDiffOn I 𝓘(ℝ,F) ∞ (h.codChart : N → F) h.codChart.source := by
    simpa only [hDfun, Function.comp_id] using
      ((contMDiffOn_of_mem_maximalAtlas h.codChart_mem_maximalAtlas).comp
        D.contMDiff.contMDiffOn (by intro y hy; simpa only [Set.mem_preimage, hDfun, id_eq] using hy))
  have hback : ContMDiffOn 𝓘(ℝ,F) I ∞ (h.codChart.symm : F → N) h.codChart.target := by
    simpa only [hDinv, Function.id_comp] using
      ((D.symm.contMDiff.contMDiffOn (s := Set.univ)).comp
        (contMDiffOn_symm_of_mem_maximalAtlas h.codChart_mem_maximalAtlas)
        (by intro y hy; exact mem_univ _))
  have hecod : ecod ∈ IsManifold.maximalAtlas I ∞ N := by
    apply ecod.mem_maximalAtlas_of_contMDiffOn
    · simpa [ecod] using
        ((b.contMDiff.contMDiffOn (s := Set.univ)).comp hco (by intro y hy; exact mem_univ _))
    · change ContMDiffOn I I ∞ (h.codChart.symm ∘ b.symm) ecod.target
      exact hback.comp (b.symm.contMDiff.contMDiffOn (s := ecod.target))
        (by intro y hy; simpa [ecod] using hy)
  refine IsImmersionAtOfComplement.mk_of_charts (h.equiv.trans e.symm)
    h.domChart ecod h.mem_domChart_source ?_ h.domChart_mem_maximalAtlas hecod ?_ ?_
  · rw [hsrc]
    exact h.mem_codChart_source
  · intro y hy
    rw [hsrc]
    exact h.source_subset_preimage_source hy
  · intro y hy
    have hwr := h.writtenInCharts hy
    have hb : ∀ z : F, I (b z) = e.symm z := by
      intro z
      change I (I.symm (e.symm z)) = e.symm z
      exact I.right_inv (by rw [I.range_eq_univ]; exact mem_univ _)
    change I (b (h.codChart ((Subtype.val : closure (connectedComponentIn Cᶜ p) → N)
      ((h.domChart.extend (SmoothCollar.halfSpaceModel V)).symm y)))) =
      e.symm (h.equiv (y, 0))
    rw [hb]
    exact congrArg e.symm hwr


end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
