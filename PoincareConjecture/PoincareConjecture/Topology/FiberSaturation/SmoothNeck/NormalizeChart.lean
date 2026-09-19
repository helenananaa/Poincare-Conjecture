import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.AffineAxis
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.IntervalOrientation
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.RestrictPartial
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

/-- Translate to a cut, scale to a safe subneck, and orient it to give a full
normalized partial diffeomorphism. No smoothness of piecewise/floor maps is used. -/
theorem exists_normalized_neck_chart
    (Ψ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) J (X × ℝ) N ∞)
    (a b c s : ℝ) (ha : a < c) (hb : c < b) (hs : s = 1 ∨ s = -1)
    (hsource : Ψ.source = (univ : Set X) ×ˢ Ioo a b) :
    ∃ r : ℝ, 0 < r ∧
      (∀ t ∈ Ioo (-1 : ℝ) 1, c+s*r*t ∈ Ioo a b) ∧
      (∀ t : ℝ, s*(c+s*r*t-c) ≤ 0 ↔ t ≤ 0) ∧
      ∃ Φ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) J (X × ℝ) N ∞,
        Φ.source = (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1 ∧
        (∀ z, Φ z = Ψ (z.1, c+s*r*z.2)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨r, hr, hstrip, hside⟩ := exists_oriented_strip_width a b c s ha hb hs
  have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hsr : s * r ≠ 0 := mul_ne_zero hs0 hr.ne'
  obtain ⟨e, he, _he_symm⟩ := exists_affine_axis_diffeomorph c (s * r) hsr
  let eX := (Diffeomorph.refl 𝓘(ℝ, V) X ∞).prodCongr e
  let Φ₀ := eX.toPartialDiffeomorph.trans Ψ
  let S : Set (X × ℝ) := (univ : Set X) ×ˢ Ioo (-1 : ℝ) 1
  have hS : IsOpen S := isOpen_univ.prod isOpen_Ioo
  have heX : ∀ z : X × ℝ, eX z = (z.1, c + s * r * z.2) := by
    intro z
    change (z.1, e z.2) = (z.1, c + s * r * z.2)
    rw [he]
  obtain ⟨Φ, hΦsrc, hΦeq⟩ := exists_partialDiffeomorph_restriction Φ₀ S hS
  refine ⟨r, hr, hstrip, hside, Φ, ?source, ?apply⟩
  · rw [hΦsrc]
    apply inter_eq_right.mpr
    intro z hz
    have hmem : eX z ∈ Ψ.source := by
      rw [heX, hsource]
      exact ⟨mem_univ _, hstrip z.2 hz.2⟩
    change z ∈ Φ₀.source
    simp only [Φ₀, PartialDiffeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.trans_toPartialEquiv, PartialEquiv.trans_source,
      PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv,
      Diffeomorph.toPartialDiffeomorph, Equiv.toPartialEquiv_source]
    exact ⟨mem_univ _, hmem⟩
  · intro z
    rw [hΦeq]
    change Ψ (eX z) = Ψ (z.1, c + s * r * z.2)
    rw [heX]
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
