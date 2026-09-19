import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core
import tests.SmoothCollar.StandardCollar
import tests.SmoothCollar.StandardComponent
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.ComplementClosure

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Apply the full construction to a nonempty Euclidean complementary closure,
including its exact boundary, without supplying a pre-existing closure atlas. -/
theorem standard_complement_smooth_structure
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    let D := connectedComponentIn ({z : V × ℝ | z.2 ≤ 0}ᶜ) (0, 1)
    D.Nonempty ∧
    ∃ cs : ChartedSpace (HalfSpace V) (closure D),
      letI : ChartedSpace (HalfSpace V) (closure D) := cs
      IsManifold (halfSpaceModel V) ∞ (closure D) ∧
      IsSmoothEmbedding (halfSpaceModel V) (𝓘(ℝ, V × ℝ)) ∞
        (Subtype.val : closure D → V × ℝ) ∧
      (Subtype.val : closure D → V × ℝ) '' (halfSpaceModel V).boundary (closure D) =
        {z | z.2 = 0} :=
/- SWARM_PROOF_BEGIN -/
by
  let C : Set (V × ℝ) := {z | z.2 ≤ 0}
  obtain ⟨_, hfront⟩ := standard_upper_component_geometry V
  obtain ⟨Φ, hsource, hid, _⟩ := exists_standard_smooth_strip_collar V
  have hC : IsClosed C := isClosed_le continuous_snd continuous_const
  haveI : LocallyConnectedSpace (V × ℝ) :=
    locallyConnectedSpace_of_connected_bases
      (fun (x : V × ℝ) (r : ℝ) => Metric.ball x r) (fun _ r => 0 < r)
      (fun _ => Metric.nhds_basis_ball)
      (fun x r _ => (convex_ball x r).isPreconnected)
  have hcover :
      ∀ y ∈ frontier (connectedComponentIn Cᶜ ((0 : V), (1 : ℝ))),
        ∃ Ψ : PartialDiffeomorph ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ)))
            (𝓘(ℝ, V × ℝ)) (V × ℝ) (V × ℝ) ∞,
          Ψ.source = (univ : Set V) ×ˢ Ioo (-1 : ℝ) 1 ∧
          (∀ z ∈ Ψ.source, Ψ z ∈ C ↔ z.2 ≤ 0) ∧ ∃ x : V, Ψ (x, 0) = y := by
    intro y hy
    have hy0 : y.2 = 0 := by
      have : y ∈ {z : V × ℝ | z.2 = 0} := by
        rwa [hfront] at hy
      exact this
    refine ⟨Φ, hsource, ?_, ⟨y.1, ?_⟩⟩
    · intro z _
      simp [hid, C]
    · rw [hid]
      exact Prod.ext rfl hy0.symm
  obtain ⟨cs, hman, hembed, hbdry, _⟩ :=
    exists_smoothClosure_of_smoothCollar_cover (X := V) (p := ((0 : V), (1 : ℝ))) hC hcover
  refine ⟨⟨(0, 1), mem_connectedComponentIn (by simp)⟩, ⟨cs, hman, hembed, ?_⟩⟩
  rwa [hfront] at hbdry
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
