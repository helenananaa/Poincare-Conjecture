import Mathlib.Tactic
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.NativeCollar
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.OrientedCollar
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.RestrictPartial

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology
/-- Regression: an off-center cut with reversed orientation still yields the
correct collar, rather than silently fixing the zero section or the positive axis. -/
theorem offcenter_reverse_neck_sanity (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    ∃ Φ : PartialDiffeomorph ((𝓘(ℝ,V)).prod (𝓘(ℝ,ℝ))) (𝓘(ℝ,V × ℝ)) (V × ℝ) (V × ℝ) ∞,
      Φ.source = (univ : Set V) ×ˢ Ioo (-1 : ℝ) 1 ∧
      (∀ z ∈ Φ.source, 1 ≤ (Φ z).2 ↔ z.2 ≤ 0) ∧
      (∀ x : V, Φ (x,0) = (x,1)) :=
/- SWARM_PROOF_BEGIN -/
by
  let e : Diffeomorph ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, V × ℝ)) (V × ℝ) (V × ℝ) ∞ :=
    { toEquiv := Equiv.refl (V × ℝ)
      contMDiff_toFun := contMDiff_fst.prodMk_space contMDiff_snd
      contMDiff_invFun :=
        (ContinuousLinearMap.fst ℝ V ℝ).contMDiff.prodMk
          (ContinuousLinearMap.snd ℝ V ℝ).contMDiff }
  let S : Set (V × ℝ) := (univ : Set V) ×ˢ Ioo (-2 : ℝ) 3
  have hS : IsOpen S := isOpen_univ.prod isOpen_Ioo
  obtain ⟨Ψ, hΨsrc, hΨeq⟩ :=
    exists_partialDiffeomorph_restriction e.toPartialDiffeomorph S hS
  have hsource : Ψ.source = (univ : Set V) ×ˢ Ioo (-2 : ℝ) 3 := by
    rw [hΨsrc]
    change e.toPartialDiffeomorph.source ∩ S = S
    have huniv : e.toPartialDiffeomorph.source = univ := rfl
    rw [huniv, univ_inter]
  have ha : (-2 : ℝ) < 1 := by norm_num
  have hb : (1 : ℝ) < 3 := by norm_num
  have hs : (-1 : ℝ) = 1 ∨ (-1 : ℝ) = -1 := Or.inr rfl
  let C : Set (V × ℝ) := {z | (1 : ℝ) ≤ z.2}
  have hcut : ∀ z ∈ Ψ.source, Ψ z ∈ C ↔ (-1 : ℝ) * (z.2 - 1) ≤ 0 := by
    intro z _hz
    have hring : (-1 : ℝ) * (z.2 - 1) = 1 - z.2 := by ring
    rw [hΨeq, hring]
    change (1 : ℝ) ≤ z.2 ↔ 1 - z.2 ≤ 0
    constructor <;> intro <;> linarith
  obtain ⟨Φ, hΦsrc, hΦcut, hΦzero⟩ :=
    exists_smoothCollar_of_oriented_neck Ψ C (-2 : ℝ) (3 : ℝ) (1 : ℝ) (-1 : ℝ)
      ha hb hs hsource hcut
  refine ⟨Φ, hΦsrc, ?cut, ?center⟩
  · intro z hz
    simpa [C] using hΦcut z hz
  · intro x
    rw [hΦzero, hΨeq]
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology
/-- A nonempty genuine standard spherical native-neck test, including native
R3 model transport, a noncentral cut, and reversed orientation. -/
theorem native_sphere_reverse_neck_sanity :
    ∃ Φ : PartialDiffeomorph ((𝓡 2).prod (𝓘(ℝ,ℝ))) NativeCylinderModel
        (Sphere2 × ℝ) NativeCylinder ∞,
      Φ.source = (univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1 ∧
      (∀ z ∈ Φ.source, 1 ≤ (Φ z).2 0 ↔ z.2 ≤ 0) ∧
      (∀ x : Sphere2, Φ (x,0) = (x,nativeAxis 1)) :=
/- SWARM_PROOF_BEGIN -/
by
  let epsilon : ℝ := 1 / 2
  have heps : (0 : ℝ) < epsilon := by norm_num
  let Q : TopologicalSpace.Opens NativeCylinder := nativeNeckDomain epsilon
  let φ : Diffeomorph NativeCylinderModel NativeCylinderModel
      (nativeNeckDomain epsilon) Q ∞ :=
    Diffeomorph.refl NativeCylinderModel Q ∞
  let C : Set NativeCylinder := {z | (1 : ℝ) ≤ z.2 0}
  let c : ℝ := 1
  let s : ℝ := -1
  have hc : c ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ := by
    rw [mem_Ioo]
    dsimp [epsilon, c]
    constructor <;> norm_num
  have hs : s = 1 ∨ s = -1 := Or.inr rfl
  have hcut : ∀ z : nativeNeckDomain epsilon,
      (φ z : NativeCylinder) ∈ C ↔ s * (z.1.2 0 - c) ≤ 0 := by
    intro z
    change (1 : ℝ) ≤ z.1.2 0 ↔ (-1 : ℝ) * (z.1.2 0 - 1) ≤ 0
    constructor <;> intro h <;> linarith
  obtain ⟨Φ, hsrc, hC, hzero⟩ :=
    exists_smoothCollar_of_native_neck_cut NativeCylinderModel
      epsilon heps Q φ C c s hc hs hcut
  refine ⟨Φ, hsrc, ?_, ?_⟩
  · intro z hz
    simpa [C] using hC z hz
  · intro x
    rw [hzero]
    dsimp [scalarToNative, φ, c]
    rfl
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck

namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
example : Nonempty Sphere2 := inferInstance
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
