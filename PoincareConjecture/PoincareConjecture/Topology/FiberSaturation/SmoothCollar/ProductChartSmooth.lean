import PoincareConjecture.Topology.FiberSaturation.SmoothCollar.Core

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothCollar
open Set Function Manifold
open scoped Manifold ContDiff Topology

/-- Cross-section chart times the real coordinate is smooth with smooth inverse,
using a vector-space product target rather than silently identifying model type tags. -/
theorem product_chart_contMDiffOn {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {X : Type*} [TopologicalSpace X] [ChartedSpace V X]
    [IsManifold (𝓘(ℝ, V)) ∞ X]
    (a : OpenPartialHomeomorph X V)
    (ha : a ∈ IsManifold.maximalAtlas (𝓘(ℝ, V)) ∞ X) :
    let b := a.prod (Homeomorph.refl ℝ).toOpenPartialHomeomorph
    ContMDiffOn ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, V × ℝ)) ∞ b b.source ∧
    ContMDiffOn (𝓘(ℝ, V × ℝ)) ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ))) ∞ b.symm b.target :=
/- SWARM_PROOF_BEGIN -/
by
  let b := a.prod (Homeomorph.refl ℝ).toOpenPartialHomeomorph
  have ha_fwd : ContMDiffOn (𝓘(ℝ, V)) (𝓘(ℝ, V)) ∞ a a.source :=
    contMDiffOn_of_mem_maximalAtlas ha
  have ha_inv : ContMDiffOn (𝓘(ℝ, V)) (𝓘(ℝ, V)) ∞ a.symm a.target :=
    contMDiffOn_symm_of_mem_maximalAtlas ha
  have hb_source : b.source = a.source ×ˢ (univ : Set ℝ) := by
    rw [OpenPartialHomeomorph.prod_source]
    simp
  have hb_target : b.target = a.target ×ˢ (univ : Set ℝ) := by
    rw [OpenPartialHomeomorph.prod_target]
    simp
  refine ⟨?fwd, ?inv⟩
  · have h1 : ContMDiffOn ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, V)) ∞
        (fun z : X × ℝ => a z.1) b.source :=
      ha_fwd.comp (contMDiffOn_fst (s := b.source)) <| by
        rw [hb_source]; exact prod_subset_preimage_fst _ _
    have h2 : ContMDiffOn ((𝓘(ℝ, V)).prod (𝓘(ℝ, ℝ))) (𝓘(ℝ, ℝ)) ∞
        (fun z : X × ℝ => z.2) b.source :=
      contMDiffOn_snd
    refine (h1.prodMk_space h2).congr ?_
    intro z _
    change b z = (a z.1, z.2)
    simp [b, mfld_simps]
  · have hfst : ContMDiff (𝓘(ℝ, V × ℝ)) (𝓘(ℝ, V)) ∞ (Prod.fst : V × ℝ → V) :=
      contDiff_fst.contMDiff
    have hsnd : ContMDiff (𝓘(ℝ, V × ℝ)) (𝓘(ℝ, ℝ)) ∞ (Prod.snd : V × ℝ → ℝ) :=
      contDiff_snd.contMDiff
    have h1 : ContMDiffOn (𝓘(ℝ, V × ℝ)) (𝓘(ℝ, V)) ∞
        (fun z : V × ℝ => a.symm z.1) b.target :=
      ha_inv.comp hfst.contMDiffOn <| by
        rw [hb_target]; exact prod_subset_preimage_fst _ _
    have h2 : ContMDiffOn (𝓘(ℝ, V × ℝ)) (𝓘(ℝ, ℝ)) ∞
        (fun z : V × ℝ => z.2) b.target :=
      hsnd.contMDiffOn
    refine (h1.prodMk h2).congr ?_
    intro z _
    change b.symm z = (a.symm z.1, z.2)
    simp [b, mfld_simps]
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation.SmoothCollar
