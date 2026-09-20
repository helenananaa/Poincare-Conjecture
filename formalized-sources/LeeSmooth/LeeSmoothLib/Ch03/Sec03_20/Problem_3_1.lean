import Mathlib
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Topology.LocallyConstant.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold Topology

noncomputable section

universe uE uH uM uE' uH' uN

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

private theorem chartedSpace_locallyConnectedSpace (I : ModelWithCorners 𝕜 E H) (M : Type uM)
    [TopologicalSpace M] [ChartedSpace H M] : LocallyConnectedSpace M := by
  -- Pull the convex local path connectedness of `range I` through `I`, then through the atlas.
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : LocallyConnectedSpace H := by
    letI : LocallyPathConnectedSpace (Set.range I) := I.convex_range.locallyPathConnectedSpace
    let e : H ≃ₜ Set.range I := I.isClosedEmbedding.toHomeomorph
    exact e.locallyConnectedSpace
  exact ChartedSpace.locallyConnectedSpace H M

variable [IsManifold I 1 M] [IsManifold I' 1 N]

-- Proof sketch: in manifold charts, the hypothesis becomes the model-space `RCLike` statement
-- that a differentiable map with vanishing derivative is locally constant on an open neighborhood.
/-- A differentiable map between `C¹` manifolds with corners is locally constant if its manifold
derivative vanishes at every point. -/
theorem isLocallyConstant_of_mfderiv_eq_zero {f : M → N} (hf : MDifferentiable I I' f)
    (hzero : ∀ p, mfderiv I I' f p = 0) : IsLocallyConstant f := by
  letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : NormedSpace ℝ E' := NormedSpace.restrictScalars ℝ 𝕜 E'
  rw [IsLocallyConstant.iff_eventually_eq]
  intro p
  let e := extChartAt I p
  let e' := extChartAt I' (f p)
  let g : E → E' := e' ∘ f ∘ e.symm
  have hpre : e.symm ⁻¹' (f ⁻¹' e'.source) ∈ nhds (e p) := by
    have hc : ContinuousAt (f ∘ e.symm) (e p) :=
      (hf (e.symm (e p))).continuousAt.comp (continuousAt_extChartAt_symm p)
    have hep : e.symm (e p) = p := e.left_inv (mem_extChartAt_source p)
    have hs : e'.source ∈ nhds ((f ∘ e.symm) (e p)) := by
      simpa only [Function.comp_apply, hep] using extChartAt_source_mem_nhds (I := I') (f p)
    exact hc.preimage_mem_nhds hs
  have hT : e.target ∩ e.symm ⁻¹' (f ⁻¹' e'.source) ∈
      nhdsWithin (e p) (Set.range I) :=
    Filter.inter_mem (extChartAt_target_mem_nhdsWithin p) (mem_nhdsWithin_of_mem_nhds hpre)
  obtain ⟨r, hr, hrT⟩ := Metric.mem_nhdsWithin_iff.mp hT
  have hpU : p ∈ e.source ∩ e ⁻¹' Metric.ball (e p) r := by
    exact ⟨mem_extChartAt_source p, Metric.mem_ball_self hr⟩
  have hUopen : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e p) r) := by
    simpa [e, extChartAt_source] using isOpen_extChartAt_preimage p Metric.isOpen_ball
  filter_upwards [hUopen.mem_nhds hpU] with q hq
  have hyTarget : e q ∈ e.target := e.map_source hq.1
  have hyRange : e q ∈ Set.range I := extChartAt_target_subset_range p hyTarget
  have hyBall : e q ∈ Metric.ball (e p) r := hq.2
  have hyT : e q ∈ e.target ∩ e.symm ⁻¹' (f ⁻¹' e'.source) :=
    hrT ⟨hyBall, hyRange⟩
  have hfpSource : f p ∈ e'.source := mem_extChartAt_source (f p)
  have hfqSource : f q ∈ e'.source := by
    have h := hyT.2
    change f (e.symm (e q)) ∈ e'.source at h
    simpa only [e.left_inv hq.1] using h
  have hdiff : DifferentiableOn 𝕜 g (Set.range I ∩ Metric.ball (e p) r) := by
    intro y hy
    have hyT' : y ∈ e.target ∩ e.symm ⁻¹' (f ⁻¹' e'.source) :=
      hrT ⟨hy.2, hy.1⟩
    have hsymm : MDifferentiableWithinAt 𝓘(𝕜, E) I e.symm (Set.range I) y :=
      mdifferentiableWithinAt_extChartAt_symm hyT'.1
    have hfe : MDifferentiableWithinAt 𝓘(𝕜, E) I' (f ∘ e.symm) (Set.range I) y := by
      apply (hf (e.symm y)).comp_mdifferentiableWithinAt y hsymm
    have he' : MDifferentiableAt I' 𝓘(𝕜, E') e' (f (e.symm y)) := by
      apply mdifferentiableAt_extChartAt
      simpa [e', extChartAt_source] using hyT'.2
    have hg : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') g (Set.range I) y := by
      exact he'.comp_mdifferentiableWithinAt y hfe
    exact hg.differentiableWithinAt.mono Set.inter_subset_left
  have hderivZero : ∀ y ∈ Set.range I ∩ Metric.ball (e p) r,
      fderivWithin 𝕜 g (Set.range I ∩ Metric.ball (e p) r) y = 0 := by
    intro y hy
    have hyT' : y ∈ e.target ∩ e.symm ⁻¹' (f ⁻¹' e'.source) :=
      hrT ⟨hy.2, hy.1⟩
    have hsymm : MDifferentiableWithinAt 𝓘(𝕜, E) I e.symm (Set.range I) y :=
      mdifferentiableWithinAt_extChartAt_symm hyT'.1
    have hfe : MDifferentiableWithinAt 𝓘(𝕜, E) I' (f ∘ e.symm) (Set.range I) y := by
      apply (hf (e.symm y)).comp_mdifferentiableWithinAt y hsymm
    have he' : MDifferentiableAt I' 𝓘(𝕜, E') e' (f (e.symm y)) := by
      apply mdifferentiableAt_extChartAt
      simpa [e', extChartAt_source] using hyT'.2
    have hfeZero : mfderivWithin 𝓘(𝕜, E) I' (f ∘ e.symm) (Set.range I) y = 0 := by
      rw [mfderiv_comp_mfderivWithin y (hf (e.symm y)) hsymm
        (I.uniqueDiffOn.uniqueMDiffOn y hy.1), hzero]
      simp
    have hgZero : mfderivWithin 𝓘(𝕜, E) 𝓘(𝕜, E') g (Set.range I) y = 0 := by
      rw [mfderiv_comp_mfderivWithin y he' hfe
        (I.uniqueDiffOn.uniqueMDiffOn y hy.1), hfeZero]
      simp
    have hgDiff : DifferentiableWithinAt 𝕜 g (Set.range I) y := by
      have hg : MDifferentiableWithinAt 𝓘(𝕜, E) 𝓘(𝕜, E') g (Set.range I) y :=
        he'.comp_mdifferentiableWithinAt y hfe
      exact hg.differentiableWithinAt
    rw [mfderivWithin_eq_fderivWithin] at hgZero
    rw [fderivWithin_subset Set.inter_subset_left
      ((I.uniqueDiffOn.inter Metric.isOpen_ball) y hy) hgDiff]
    exact hgZero
  have hx : e p ∈ Set.range I ∩ Metric.ball (e p) r :=
    ⟨Set.mem_range_self _, Metric.mem_ball_self hr⟩
  have hconst : g (e p) = g (e q) :=
    (I.convex_range.inter (convex_ball (e p) r)).is_const_of_fderivWithin_eq_zero
      hdiff hderivZero hx ⟨hyRange, hyBall⟩
  have hconst' := congrArg e'.symm hconst
  have hep : e.symm (e p) = p := e.left_inv (mem_extChartAt_source p)
  have heq : e.symm (e q) = q := e.left_inv hq.1
  have hefp : e'.symm (e' (f p)) = f p := e'.left_inv hfpSource
  have hefq : e'.symm (e' (f q)) = f q := e'.left_inv hfqSource
  simpa only [g, Function.comp_apply, hep, heq, hefp, hefq] using hconst'.symm

/-- On a `C¹` manifold with corners, a differentiable map has vanishing manifold derivative at
every point if and only if it is locally constant. -/
theorem mfderiv_eq_zero_iff_isLocallyConstant {f : M → N}
    (hf : MDifferentiable I I' f) : (∀ p, mfderiv I I' f p = 0) ↔ IsLocallyConstant f := by
  letI : LocallyConnectedSpace M := chartedSpace_locallyConnectedSpace I M
  constructor
  · exact isLocallyConstant_of_mfderiv_eq_zero hf
  · intro hloc p
    -- Route correction: the reverse implication is purely local and uses eventual equality with
    -- a constant map, so no chart computation is needed here.
    have heq : f =ᶠ[𝓝 p] fun _ : M ↦ f p := by
      change ∀ᶠ y in 𝓝 p, f y = f p
      exact hloc.eventually_eq p
    have hconst : HasMFDerivAt I I' (fun _ : M ↦ f p) p
        (0 : TangentSpace I p →L[𝕜] TangentSpace I' (f p)) := hasMFDerivAt_const (f p) p
    exact (hconst.congr_of_eventuallyEq heq).mfderiv

-- Proof sketch: use `mfderiv_eq_zero_iff_isLocallyConstant` and the canonical correspondence
-- between locally constant maps and maps constant on connected components in a locally connected
-- space.
/-- Problem 3-1: for a differentiable map between `C¹` manifolds with corners, the manifold
derivative is the zero map at every point if and only if the map is constant on each connected
component of the source space. -/
theorem mfderiv_eq_zero_iff_constant_on_components {f : M → N}
    (hf : MDifferentiable I I' f) :
    (∀ p, mfderiv I I' f p = 0) ↔ ∀ p, ∀ q ∈ connectedComponent p, f q = f p := by
  letI : LocallyConnectedSpace M := chartedSpace_locallyConnectedSpace I M
  rw [mfderiv_eq_zero_iff_isLocallyConstant hf]
  constructor
  · intro hloc p q hq
    exact hloc.apply_eq_of_isPreconnected isConnected_connectedComponent.isPreconnected
      hq mem_connectedComponent
  · exact IsLocallyConstant.of_constant_on_connected_components
