import PoincareConjecture.Topology.FiberSaturation.SmoothBundleAtlas

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Bundle Manifold
open scoped Manifold ContDiff
variable {V W U H G K B F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace K]
  [TopologicalSpace B] [ChartedSpace K B]
  [TopologicalSpace F] [ChartedSpace G F]
  (E : B → Type*) [∀ b, TopologicalSpace (E b)] [∀ b, Nonempty (E b)]
  [TopologicalSpace (TotalSpace F E)] [ChartedSpace H (TotalSpace F E)]
  [FiberBundle F E]
  {IB : ModelWithCorners ℝ U K} {I : ModelWithCorners ℝ V H}
  {J : ModelWithCorners ℝ W G} [IsManifold I ∞ (TotalSpace F E)]
  (c : C(ℝ,B)) (hc : IsLocalDiffeomorph 𝓘(ℝ,ℝ) IB ∞ c)
  (hp : ContMDiff I IB ∞ (TotalSpace.proj (F := F) (E := E)))

omit [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [∀ b, Nonempty (E b)]
  [FiberBundle F E] in
/-- The actual real-height projection is smooth, now using original smooth
bundle data as well as the smooth covering map, not mere continuity. -/
theorem contMDiff_pullback_height :
    letI := CoverPullback.bundleChartedSpace (H := H) E c hc.isLocalHomeomorph hp.continuous;
    ContMDiff I 𝓘(ℝ,ℝ) ∞
    (TotalSpace.proj : TotalSpace F ((c : ℝ → B) *ᵖ E) → ℝ) := by
  letI := CoverPullback.bundleChartedSpace (H := H) E c hc.isLocalHomeomorph hp.continuous
  have hr := CoverPullback.bundle_lift_isLocalDiffeomorph E c
    hc.isLocalHomeomorph hp.continuous I
  exact contMDiff_of_localDiffeomorph_comp hc (Pullback.continuous_proj F E c)
    (hp.comp hr.contMDiff)

omit [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
/-- Pulling back an existing smooth bundle chart preserves both smooth
chart maps in the atlas lifted from the unchanged original total space. -/
theorem isSmooth_pullback_chart {e : Trivialization F (TotalSpace.proj (F := F) (E := E))}
    (he : IsSmoothBundleChart IB I J e) :
    letI := CoverPullback.bundleChartedSpace (H := H) E c hc.isLocalHomeomorph hp.continuous;
    IsSmoothTrivialization I J (e.pullback c) := by
  letI := CoverPullback.bundleChartedSpace (H := H) E c hc.isLocalHomeomorph hp.continuous
  have hr := CoverPullback.bundle_lift_isLocalDiffeomorph E c
    hc.isLocalHomeomorph hp.continuous I
  have hh := contMDiff_pullback_height E c hc hp
  constructor
  · have hcomp := he.1.comp hr.contMDiff.contMDiffOn (fun _ hz => hz)
    exact hh.contMDiffOn.prodMk (contMDiff_snd.comp_contMDiffOn hcomp)
  · apply contMDiffOn_of_localDiffeomorph_comp hr (e.pullback c).open_target
      (e.pullback c).toOpenPartialHomeomorph.continuousOn_symm
    have hparam : ContMDiff ((𝓘(ℝ,ℝ)).prod J) (IB.prod J) ∞
        (fun y : ℝ × F => (c y.1,y.2)) :=
      (hc.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
    have h : ContMDiffOn ((𝓘(ℝ,ℝ)).prod J) I ∞
        (fun y : ℝ × F => e.toOpenPartialHomeomorph.symm (c y.1,y.2))
        (e.pullback c).target := he.2.comp hparam.contMDiffOn (by
      intro y hy
      exact e.mem_target.mpr hy.1)
    apply h.congr
    intro y hy
    exact e.mk_symm hy.1 y.2

omit [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
/-- The local smooth atlas required by the real-period theorem is derived
from the original bundle charts. It is not assumed on the pullback. -/
theorem pullback_local_smooth_charts
    (hloc : ∀ b : B, ∃ e : Trivialization F (TotalSpace.proj (F := F) (E := E)),
      b ∈ e.baseSet ∧ IsSmoothBundleChart IB I J e) :
    letI := CoverPullback.bundleChartedSpace (H := H) E c hc.isLocalHomeomorph hp.continuous;
    ∀ t : ℝ, ∃ k : Trivialization F
        (TotalSpace.proj : TotalSpace F ((c : ℝ → B) *ᵖ E) → ℝ),
      t ∈ k.baseSet ∧ IsSmoothTrivialization I J k := by
  letI := CoverPullback.bundleChartedSpace (H := H) E c hc.isLocalHomeomorph hp.continuous
  intro t
  obtain ⟨e,ht,he⟩ := hloc (c t)
  exact ⟨e.pullback c,ht,isSmooth_pullback_chart E c hc hp he⟩

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
