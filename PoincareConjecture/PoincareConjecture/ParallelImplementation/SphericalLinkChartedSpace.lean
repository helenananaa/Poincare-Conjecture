import PoincareConjecture.ParallelImplementation.RealizationOpenStarChart
import Mathlib.Geometry.Manifold.ChartedSpace
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SphericalLinkChartedSpace
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Spherical links give a genuine topological atlas on the existing realization topology. -/
theorem exists_chartedSpace_of_spherical_links
    {V : Type*} [Fintype V] [DecidableEq V] (K : FiniteAbstractComplex V)
    (hlinks : ∀ (v : V) (hv : ({v} : Finset V) ∈ K.faces),
      Nonempty ({y : V → ℝ // (∀ w, 0 ≤ y w) ∧ (∑ w, y w) = 1 ∧
        (Finset.univ.filter (fun w => 0 < y w)) ∈ (abstractLink K {v} hv).faces} ≃ₜ
        {z : E3 // ‖z‖ = 1})) :
    ∃ a : ChartedSpace E3 {x : V → ℝ // x ∈ (realization K).space},
      ∀ x, ∃ v : V, 0 < x.1 v ∧
        (a.chartAt x).source = {y | 0 < y.1 v} ∧
        (a.chartAt x).target = {z | ‖z‖ < 1} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let A := {x : V → ℝ // x ∈ (realization K).space}
  have hcover :=
    PoincareConjecture.ParallelImplementation.BarycentricOpenCover.positive_coordinate_open_cover K
  have hcoords (x : A) :
      (∀ w, 0 ≤ x.1 w) ∧ (∑ w, x.1 w) = 1 ∧
        (Finset.univ.filter (fun w => 0 < x.1 w)) ∈ K.faces :=
    PoincareConjecture.ParallelImplementation.BarycentricMembership.mem_realization_iff_barycentric
      K x.1 |>.mp x.2
  have hpositive (x : A) : ∃ v : V, 0 < x.1 v := by
    have hsumpos : 0 < x.1 :=
      (Fintype.sum_pos_iff_of_nonneg (hcoords x).1).mp (by rw [(hcoords x).2.1]; norm_num)
    exact (Pi.lt_def.mp hsumpos).2
  let vertex (x : A) : V := Classical.choose (hpositive x)
  have hvertex (x : A) : 0 < x.1 (vertex x) := Classical.choose_spec (hpositive x)
  have hvertexFace (x : A) : ({vertex x} : Finset V) ∈ K.faces := by
    apply (K.isRelLowerSet_faces (hcoords x).2.2).2
    · intro w hw
      have hwv : w = vertex x := Finset.mem_singleton.mp hw
      subst w
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvertex x⟩
    · exact ⟨vertex x, Finset.mem_singleton_self _⟩
  let starChart (x : A) : OpenPartialHomeomorph A E3 :=
    Classical.choose
      (PoincareConjecture.ParallelImplementation.RealizationOpenStarChart.exists_open_star_chart
        K (vertex x) (hvertexFace x)
        (Classical.choice (hlinks (vertex x) (hvertexFace x))))
  have hstarChart (x : A) :
      (starChart x).source = {y | 0 < y.1 (vertex x)} ∧
        (starChart x).target = {z | ‖z‖ < 1} :=
    Classical.choose_spec
      (PoincareConjecture.ParallelImplementation.RealizationOpenStarChart.exists_open_star_chart
        K (vertex x) (hvertexFace x)
        (Classical.choice (hlinks (vertex x) (hvertexFace x))))
  let a : ChartedSpace E3 A := {
    atlas := Set.range starChart
    chartAt := starChart
    mem_chart_source := by
      intro x
      rw [(hstarChart x).1]
      exact hvertex x
    chart_mem_atlas := by
      intro x
      exact ⟨x, rfl⟩
  }
  refine ⟨a, ?_⟩
  intro x
  exact ⟨vertex x, hvertex x, (hstarChart x).1, (hstarChart x).2⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SphericalLinkChartedSpace
