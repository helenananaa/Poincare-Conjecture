import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.NormalizeChart
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

/-- Produce a genuine normalized one-sided smooth collar from an oriented
finite neck and its pointwise local cut description. -/
theorem exists_smoothCollar_of_oriented_neck
    (Ψ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) J (X × ℝ) N ∞)
    (C : Set N) (a b c s : ℝ) (ha : a < c) (hb : c < b)
    (hs : s = 1 ∨ s = -1)
    (hsource : Ψ.source = (univ : Set X) ×ˢ Ioo a b)
    (hcut : ∀ z ∈ Ψ.source, Ψ z ∈ C ↔ s*(z.2-c) ≤ 0) :
    ∃ Φ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) J (X × ℝ) N ∞,
      Φ.source = (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1 ∧
      (∀ z ∈ Φ.source, Φ z ∈ C ↔ z.2 ≤ 0) ∧
      (∀ x : X, Φ (x,0) = Ψ (x,c)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨r, _hr, hstrip, hside, Φ, hΦsrc, hΦeq⟩ :=
    exists_normalized_neck_chart Ψ a b c s ha hb hs hsource
  refine ⟨Φ, hΦsrc, ?cut, ?zero⟩
  · intro z hz
    have hzIoo : z.2 ∈ Ioo (-1 : ℝ) 1 := by
      have : z ∈ (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1 := by rwa [hΦsrc] at hz
      exact this.2
    have hmem : (z.1, c + s * r * z.2) ∈ Ψ.source := by
      rw [hsource]
      exact ⟨mem_univ _, hstrip z.2 hzIoo⟩
    rw [hΦeq z]
    exact (hcut _ hmem).trans (hside z.2)
  · intro x
    rw [hΦeq]
    simp
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
