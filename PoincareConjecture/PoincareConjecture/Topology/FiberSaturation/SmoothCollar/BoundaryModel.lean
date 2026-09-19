import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.CoordinatesSmooth
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.CoordinatesGeometry

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- A genuine smooth full collar supplies the exact ambient smooth model at a contacted center. -/
theorem smoothCollar_center_has_ambient_model {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X N : Type*} [TopologicalSpace X] [TopologicalSpace N]
    [ChartedSpace V X] [ChartedSpace (V × ℝ) N]
    [IsManifold (𝓘(ℝ, V)) ∞ X] [IsManifold (𝓘(ℝ, V × ℝ)) ∞ N] [PreconnectedSpace X]
    (Φ : PartialDiffeomorph ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ)))
      (𝓘(ℝ, V × ℝ)) (X × ℝ) N ∞)
    (hsource : Φ.source = (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1)
    {C : Set N} (hside : ∀ z ∈ Φ.source, Φ z ∈ C ↔ z.2 ≤ 0)
    {p : N} {x : X} (hx : Φ (x, 0) ∈ frontier (connectedComponentIn Cᶜ p)) :
    ∃ e : OpenPartialHomeomorph N (V × ℝ),
      Φ (x, 0) ∈ e.source ∧
      e ∈ IsManifold.maximalAtlas (𝓘(ℝ, V × ℝ)) ∞ N ∧
      e.IsImage (closure (connectedComponentIn Cᶜ p)) (range (halfSpaceModel V)) :=
/- SWARM_PROOF_BEGIN -/
by
  let a := chartAt V x
  let F := Φ.toOpenPartialHomeomorph
  let e := collarCoordinates F a
  have ha : a ∈ IsManifold.maximalAtlas (𝓘(ℝ, V)) ∞ X :=
    IsManifold.chart_mem_maximalAtlas x
  have hgeom := collarCoordinates_component_geometry F hsource hside hx a
  have hatlas := collarCoordinates_mem_maximalAtlas Φ a ha
  have hcenter : Φ (x, 0) ∈ e.source := by
    have hxsrc : x ∈ a.source := mem_chart_source V x
    have hmem := (hgeom.1 (x, neckCenter) hxsrc).1
    have hpt : collarRestriction F (x, neckCenter) = Φ (x, 0) := by
      change F (x, (neckCenter : ℝ)) = Φ.toPartialEquiv (x, 0)
      simp [neckCenter]
      rfl
    rwa [hpt] at hmem
  exact ⟨e, hcenter, hatlas, hgeom.2⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
