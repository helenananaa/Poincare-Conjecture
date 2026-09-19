import PoincareConjecture.Topology.FiberSaturation.BoundaryRegularity
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.DomainAtlas
open Set Function Manifold
open scoped Manifold ContDiff Topology

variable {E H N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace N]

/-- A genuine restriction of an ambient local set model to its original subspace.
The fields describe exact maps and sets, not a smoothness assumption or a
replacement topology. Existence is a separate proved construction. -/
structure ModelDomainChart (I : ModelWithCorners ℝ E H) (K : Set N) where
  ambient : OpenPartialHomeomorph N E
  intrinsic : OpenPartialHomeomorph K H
  source_eq : intrinsic.source = (Subtype.val : K → N) ⁻¹' ambient.source
  target_eq : intrinsic.target = I ⁻¹' ambient.target
  forward_eq : ∀ p ∈ intrinsic.source, I (intrinsic p) = ambient p.1
  inverse_eq : ∀ y ∈ intrinsic.target, ((intrinsic.symm y : K) : N) = ambient.symm (I y)
  model_image : ambient.IsImage K (range I)

/-- Domain in model coordinates on which two restricted charts overlap. -/
def transitionDomain {I : ModelWithCorners ℝ E H} {K : Set N}
    (a b : ModelDomainChart I K) : Set E :=
  I.symm ⁻¹' (a.intrinsic.symm.trans b.intrinsic).source ∩ range I

/-- The charted structure is built on the existing induced topology of K.
Its atlas is exactly the supplied chart family, without adding a new topology. -/
abbrev domainChartedSpace {I : ModelWithCorners ℝ E H} {K : Set N}
    (c : K → ModelDomainChart I K) (hc : ∀ p, p ∈ (c p).intrinsic.source) :
    ChartedSpace H K where
  atlas := range (fun p => (c p).intrinsic)
  chartAt p := (c p).intrinsic
  mem_chart_source := hc
  chart_mem_atlas p := mem_range_self p

end PoincareConjecture.Topology.FiberSaturation.DomainAtlas
