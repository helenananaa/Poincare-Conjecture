import PoincareConjecture.Topology.FiberSaturation.SmoothLiftOn
import PoincareConjecture.Topology.FiberSaturation.SmoothRealTrivialization

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Bundle Manifold Filter
open scoped Manifold ContDiff Topology
variable {V W U H G K B N F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace K]
  [TopologicalSpace B] [ChartedSpace K B]
  [TopologicalSpace N] [ChartedSpace H N]
  [TopologicalSpace F] [ChartedSpace G F]
  (IB : ModelWithCorners ℝ U K) (I : ModelWithCorners ℝ V H)
  (J : ModelWithCorners ℝ W G) {p : N → B}

/-- Smoothness of an existing topological bundle chart, in the fixed base,
total-space and fiber structures. It asserts only its two chart maps. -/
def IsSmoothBundleChart (e : Trivialization F p) : Prop :=
  ContMDiffOn I (IB.prod J) ∞ e e.source ∧
    ContMDiffOn (IB.prod J) I ∞ e.toOpenPartialHomeomorph.symm e.target

variable {IB I J}

/-- A local smooth bundle atlas makes its actual bundle projection smooth. -/
theorem contMDiff_projection_of_local_charts
    (hloc : ∀ b : B, ∃ e : Trivialization F p,
      b ∈ e.baseSet ∧ IsSmoothBundleChart IB I J e) : ContMDiff I IB ∞ p := by
  intro z
  obtain ⟨e,hb,he⟩ := hloc (p z)
  have hn : e.source ∈ nhds z := e.open_source.mem_nhds (e.mem_source.mpr hb)
  have heq : p =ᶠ[nhds z] (Prod.fst ∘ e) := by
    filter_upwards [hn] with w hw
    exact (e.coe_fst hw).symm
  exact (contMDiff_fst.comp_contMDiffOn he.1).contMDiffAt hn
    |>.congr_of_eventuallyEq heq

/-- For a real base, the generic atlas predicate is exactly the prior one. -/
theorem isSmoothBundleChart_real_iff {p : N → ℝ} (e : Trivialization F p) :
    IsSmoothBundleChart 𝓘(ℝ,ℝ) I J e ↔ IsSmoothTrivialization I J e := Iff.rfl


/-- Restriction to an open part of the base preserves both smooth chart maps. -/
theorem isSmoothBundleChart_restrOpen {e : Trivialization F p}
    (he : IsSmoothBundleChart IB I J e) (A : Set B) (hA : IsOpen A) :
    IsSmoothBundleChart IB I J (e.restrOpen A hA) := by
  constructor
  · exact he.1.mono (fun z hz => e.mem_source.mpr
      (((e.restrOpen A hA).mem_source.mp hz).1))
  · exact he.2.mono (fun z hz => e.mem_target.mpr
      (((e.restrOpen A hA).mem_target.mp hz).1))

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
