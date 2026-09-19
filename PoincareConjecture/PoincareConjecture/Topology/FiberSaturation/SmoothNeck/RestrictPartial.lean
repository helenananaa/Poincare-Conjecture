import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

variable {V W G X N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace G]
  [TopologicalSpace X] [TopologicalSpace N] [ChartedSpace V X] [ChartedSpace G N]
  {J : ModelWithCorners ℝ W G}

/-- Restrict a genuine partial diffeomorphism without altering its values. -/
theorem exists_partialDiffeomorph_restriction
    (Φ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) J (X × ℝ) N ∞)
    (S : Set (X × ℝ)) (hS : IsOpen S) :
    ∃ Ψ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) J (X × ℝ) N ∞,
      Ψ.source = Φ.source ∩ S ∧ (∀ z, Ψ z = Φ z) :=
/- SWARM_PROOF_BEGIN -/
by
  let r := Φ.toOpenPartialHomeomorph.restrOpen S hS
  refine ⟨{ toPartialEquiv := r.toPartialEquiv
            open_source := r.open_source
            open_target := r.open_target
            contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
            contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left },
    rfl, fun _ => rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
