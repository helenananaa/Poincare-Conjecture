import PoincareConjecture.Topology.FiberSaturation.SmoothPullbackAtlas
import PoincareConjecture.Topology.FiberSaturation.SmoothCircleCover
import PoincareConjecture.Topology.FiberSaturation.BundleCut

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Bundle Manifold Function
open scoped Manifold ContDiff
variable {L : ℝ} {V W H G F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace F] [ChartedSpace G F] [Nonempty F]
  (E : AddCircle L → Type*) [∀ b, TopologicalSpace (E b)]
  [TopologicalSpace (TotalSpace F E)] [ChartedSpace H (TotalSpace F E)]
  [FiberBundle F E]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G}
  [IsManifold I ∞ (TotalSpace F E)]

local instance : ChartedSpace ℝ (AddCircle L) := CircleSmooth.chartedSpace L

/-- An actual smooth circle-bundle atlas produces a smooth all-real periodic
presentation. No pullback smoothness, deck map, twist or global coordinates
are inputs. The original total-space and fiber smooth structures are retained. -/
theorem abstract_bundle_smooth_real_presentation (hL : 0 < L)
    (hloc : ∀ b : AddCircle L, ∃ k : Trivialization F
        (TotalSpace.proj (F := F) (E := E)),
      b ∈ k.baseSet ∧ IsSmoothBundleChart 𝓘(ℝ,ℝ) I J k) :
    ∃ φ : F ≃ₘ⟮J,J⟯ F, ∃ q : F × ℝ → TotalSpace F E,
      IsLocalDiffeomorph (J.prod 𝓘(ℝ,ℝ)) I ∞ q ∧ Surjective q ∧
      (∀ z : F × ℝ, (q z).proj = (z.2 : AddCircle L)) ∧
      (∀ t : ℝ, Injective (fun x : F => q (x,t))) ∧
      (∀ x t, q (x,t+L) = q (φ x,t)) := by
  letI : ∀ b, Nonempty (E b) := fun b =>
    ⟨(FiberBundle.homeomorphAt F E b).symm (Classical.choice ‹Nonempty F›)⟩
  have hp := contMDiff_projection_of_local_charts hloc
  let c := CircleBundle.cover L
  have hc : IsLocalDiffeomorph 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ c :=
    CircleSmooth.coe_isLocalDiffeomorph L
  letI := CoverPullback.bundleChartedSpace (H := H) E c
    (AddCircle.isLocalHomeomorph_coe L) hp.continuous
  have hcharts := pullback_local_smooth_charts E c hc hp hloc
  let T := CoverPullback.nativeCircleDeck E hp.continuous I
  obtain ⟨φ,e,hheight,hequiv⟩ := exists_equivariant_real_diffeomorph
    (Pullback.continuous_proj F E c) hcharts T hL
    (CoverPullback.nativeCircleDeck_height E hp.continuous I)
  let d := (Diffeomorph.prodComm J 𝓘(ℝ,ℝ) F ℝ ∞).trans e
  let q : F × ℝ → TotalSpace F E := Pullback.lift c ∘ d
  have hr := CoverPullback.bundle_lift_isLocalDiffeomorph E c
    (AddCircle.isLocalHomeomorph_coe L) hp.continuous I
  have hq : IsLocalDiffeomorph (J.prod 𝓘(ℝ,ℝ)) I ∞ q := by
    intro z
    exact (d.isLocalDiffeomorph z).comp I (TotalSpace F E) (hr (d z))
  have hrs : Surjective (Pullback.lift c : TotalSpace F ((c : ℝ → AddCircle L) *ᵖ E) →
      TotalSpace F E) :=
    (CoverPullback.forget_surjective (p := TotalSpace.proj (F := F) (E := E))
      (show Surjective c from QuotientAddGroup.mk_surjective)).comp
        (CoverPullback.bundleHomeomorph (F := F) E c).surjective
  refine ⟨φ,q,hq,hrs.comp d.surjective,?_,?_,?_⟩
  · rintro ⟨x,t⟩
    change ((e (t,x)).proj : AddCircle L) = (t : AddCircle L)
    rw [hheight]
  · intro t x y hxy
    have he : e (t,x) = e (t,y) := by
      apply (CoverPullback.bundleHomeomorph (F := F) E c).injective
      apply Subtype.ext
      apply Prod.ext
      · change (e (t,x)).proj = (e (t,y)).proj
        rw [hheight,hheight]
      · exact hxy
    exact congrArg Prod.snd (e.injective he)
  · intro x t
    change Pullback.lift c (e (t+L,x)) = Pullback.lift c (e (t,φ x))
    have h := hequiv (1 : ℤ) t x
    simp only [Int.cast_one,one_mul,zpow_one] at h
    rw [h]
    exact CoverPullback.nativeCircleDeck_lift E hp.continuous I _

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
