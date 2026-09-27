import PoincareConjecture.ProofContract.Refinement20260927.RadialExtensionLeaves
import PoincareConjecture.ProofContract.Refinement20260927.AcceptedFortyTwo
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set
open scoped Topology Manifold ContDiff
/-- **Math.** Three independent statements construct the same explicit compact extension. -/
theorem cylinder_extension_of_radial_leaves (radial : RadialLocalSmoothStatement)
    (glue : CylinderCutoffGlueStatement) (support : CylinderCutoffSupportStatement) :
    CylinderCompactExtensionStatement := by
  intro n f hf
  let a : CylinderAmbient → ApproxAmbient n := fun z => f (z.1,radialDirection z.2)
  have ha : ∀ z : CylinderAmbient, z.2 ≠ 0 → ContDiffAt ℝ 1 a z := by
    intro z hz
    obtain ⟨d,hd,heq⟩ := radial z.2 hz
    have hd1 : ContMDiff 𝓘(ℝ,Euclidean3) (𝓡 2) 1 d := hd.of_le (by simp)
    have hfst : ContMDiff 𝓘(ℝ,CylinderAmbient) 𝓘(ℝ,ℝ) 1
        (Prod.fst : CylinderAmbient → ℝ) := contDiff_fst.contMDiff
    have hsnd : ContMDiff 𝓘(ℝ,CylinderAmbient) 𝓘(ℝ,Euclidean3) 1
        (Prod.snd : CylinderAmbient → Euclidean3) := contDiff_snd.contMDiff
    have hmap : ContMDiff 𝓘(ℝ,CylinderAmbient) SweepModel 1
        (fun w : CylinderAmbient => (w.1,d w.2)) := hfst.prodMk (hd1.comp hsnd)
    have hG : ContDiff ℝ 1 (fun w : CylinderAmbient => f (w.1,d w.2)) :=
      (hf.comp hmap).contDiff
    have hball : Metric.ball z.2 (‖z.2‖/4) ∈ 𝓝 z.2 :=
      Metric.ball_mem_nhds _ (div_pos (norm_pos_iff.mpr hz) (by norm_num))
    have hnear : ∀ᶠ w in 𝓝 z, w.2 ∈ Metric.ball z.2 (‖z.2‖/4) :=
      continuous_snd.continuousAt.preimage_mem_nhds hball
    apply hG.contDiffAt.congr_of_eventuallyEq
    filter_upwards [hnear] with w hw
    change f (w.1,radialDirection w.2) = f (w.1,d w.2)
    rw [heq hw]
  obtain ⟨hc,heq⟩ := support n f
  exact ⟨radialCylinderExtension f,glue n a ha,hc,heq⟩
/-- **Math.** The original V1 conclusion is preserved while only this analytic leaf is split. -/
theorem public_of_radial_extension_frontier (triangulate : TriangulationProducerStatement.{u})
    (atlas : FinitePLAtlasProducerStatement.{u}) (radial : RadialLocalSmoothStatement)
    (glue : CylinderCutoffGlueStatement) (support : CylinderCutoffSupportStatement)
    (geometry : C1GeometryProducerStatement.{u}) : TopologicalPoincareStatement.{u} :=
  public_after_forty_two triangulate atlas
    (cylinder_extension_of_radial_leaves radial glue support) geometry
#print axioms cylinder_extension_of_radial_leaves
#print axioms public_of_radial_extension_frontier
end PoincareConjecture.ProofContract.Refinement20260927
