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
