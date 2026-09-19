import Mathlib.Geometry.Manifold.Instances.Real
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.ComplementClosure
import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- A genuine smooth strip collar exists in the usual product Euclidean space.
This is an explicit non-vacuous input for the geometric construction. -/
theorem exists_standard_smooth_strip_collar
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∃ Φ : PartialDiffeomorph ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ)))
        (𝓘(ℝ, V × ℝ)) (V × ℝ) (V × ℝ) ∞,
      Φ.source = (univ : Set V) ×ˢ Ioo (-1 : ℝ) 1 ∧
      (∀ z, Φ z = z) ∧ Φ.target = (univ : Set V) ×ˢ Ioo (-1 : ℝ) 1 :=
/- SWARM_PROOF_BEGIN -/
by
  let strip : Set (V × ℝ) := (univ : Set V) ×ˢ Ioo (-1 : ℝ) 1
  have hopen : IsOpen strip := isOpen_univ.prod isOpen_Ioo
  refine
    ⟨{ toPartialEquiv := (PartialEquiv.refl (V × ℝ)).restr strip
       open_source := by
         simpa [PartialEquiv.refl_restr_source] using hopen
       open_target := by
         simpa [PartialEquiv.refl_restr_target] using hopen
       contMDiffOn_toFun :=
         (contMDiff_fst.prodMk_space contMDiff_snd).contMDiffOn
       contMDiffOn_invFun :=
         ((ContinuousLinearMap.fst ℝ V ℝ).contMDiff.prodMk
           (ContinuousLinearMap.snd ℝ V ℝ).contMDiff).contMDiffOn },
      PartialEquiv.refl_restr_source _, fun _ => rfl, PartialEquiv.refl_restr_target _⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- The nontrivial complementary component and its frontier in the Euclidean test case. -/
theorem standard_upper_component_geometry
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    connectedComponentIn ({z : V × ℝ | z.2 ≤ 0}ᶜ) (0, 1) = {z | 0 < z.2} ∧
    frontier (connectedComponentIn ({z : V × ℝ | z.2 ≤ 0}ᶜ) (0, 1)) =
      {z | z.2 = 0} :=
/- SWARM_PROOF_BEGIN -/
by
  have hcompl : ({z : V × ℝ | z.2 ≤ 0}ᶜ : Set (V × ℝ)) = univ ×ˢ Ioi (0 : ℝ) := by
    ext z
    simp
  have hupper : ({z : V × ℝ | 0 < z.2} : Set (V × ℝ)) = univ ×ˢ Ioi (0 : ℝ) := by
    ext z
    simp
  have hpre : IsPreconnected ((univ : Set V) ×ˢ Ioi (0 : ℝ)) :=
    isPreconnected_univ.prod isPreconnected_Ioi
  have hmem : ((0 : V), (1 : ℝ)) ∈ (univ : Set V) ×ˢ Ioi (0 : ℝ) :=
    ⟨mem_univ _, by norm_num⟩
  constructor
  · rw [hcompl, hupper]
    exact hpre.connectedComponentIn hmem
  · rw [hcompl, hpre.connectedComponentIn hmem, frontier, closure_prod_eq, interior_prod_eq,
      closure_univ, interior_univ, closure_Ioi, interior_Ioi]
    ext z
    simp [and_comm, le_antisymm_iff]
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar

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

open Set
open scoped Manifold ContDiff
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
/-- Three-dimensional, nonempty, boundary-bearing use of the actual collar-cover construction. -/
example :
    let V := EuclideanSpace ℝ (Fin 2)
    let D := connectedComponentIn ({z : V × ℝ | z.2 ≤ 0}ᶜ) (0, 1)
    ∃ cs : ChartedSpace (HalfSpace V) (closure D),
      letI : ChartedSpace (HalfSpace V) (closure D) := cs
      IsManifold (halfSpaceModel V) ∞ (closure D) := by
  obtain ⟨_, cs, hm, _, _⟩ := standard_complement_smooth_structure (EuclideanSpace ℝ (Fin 2))
  exact ⟨cs, hm⟩
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
