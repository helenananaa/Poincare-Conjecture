import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.Core
import PoincareConjecture.Topology.FiberSaturation.SmoothNeck.NativeAxis
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothNeck
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- The two finite neck parameterizations are genuinely diffeomorphic,
with the concrete coordinate formula, not merely abstractly equivalent. -/
theorem exists_native_domain_diffeomorph (epsilon : ℝ) :
    ∃ e : Diffeomorph ((𝓡 2).prod (𝓘(ℝ,ℝ))) NativeCylinderModel
        (scalarNeckDomain epsilon) (nativeNeckDomain epsilon) ∞,
      ∀ z, e z = scalarToNative z :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨eGlobal, heGlobal⟩ := exists_native_axis_diffeomorph
  have hmem : ∀ z : Sphere2 × ℝ,
      z ∈ scalarNeckDomain epsilon ↔ eGlobal z ∈ nativeNeckDomain epsilon := by
    intro z
    have hcoord : (eGlobal z).2 0 = z.2 := by
      rw [heGlobal z, nativeAxis_zero]
    change z ∈ (univ : Set Sphere2) ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ ↔
      (-epsilon⁻¹ < (eGlobal z).2 0 ∧ (eGlobal z).2 0 < epsilon⁻¹)
    simp [mem_prod, mem_Ioo, hcoord]
  let eRestr := eGlobal.toEquiv.subtypeEquiv hmem
  let e :
      Diffeomorph ((𝓡 2).prod (𝓘(ℝ, ℝ))) NativeCylinderModel
        (scalarNeckDomain epsilon) (nativeNeckDomain epsilon) ∞ :=
    { toEquiv := eRestr
      contMDiff_toFun := by
        rw [← ContMDiff.subtypeVal_comp_iff (nativeNeckDomain epsilon)
            (eRestr : scalarNeckDomain epsilon → nativeNeckDomain epsilon)]
        have hcomp :
            (Subtype.val : nativeNeckDomain epsilon → NativeCylinder) ∘ eRestr =
              eGlobal ∘ (Subtype.val : scalarNeckDomain epsilon → Sphere2 × ℝ) :=
          rfl
        rw [hcomp]
        exact eGlobal.contMDiff.comp contMDiff_subtype_val
      contMDiff_invFun := by
        rw [← ContMDiff.subtypeVal_comp_iff (scalarNeckDomain epsilon)
            (eRestr.symm : nativeNeckDomain epsilon → scalarNeckDomain epsilon)]
        have hcomp :
            (Subtype.val : scalarNeckDomain epsilon → Sphere2 × ℝ) ∘ eRestr.symm =
              eGlobal.symm ∘ (Subtype.val : nativeNeckDomain epsilon → NativeCylinder) :=
          rfl
        rw [hcomp]
        exact eGlobal.symm.contMDiff.comp contMDiff_subtype_val }
  refine ⟨e, ?_⟩
  intro z
  exact Subtype.ext (heGlobal z.1)
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothNeck
