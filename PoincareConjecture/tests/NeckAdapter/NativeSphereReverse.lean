import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.NativeCollar
import Mathlib.Tactic

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
