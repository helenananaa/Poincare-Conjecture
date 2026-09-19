import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.CircleSmooth
open Set Function Manifold Filter
open scoped Manifold ContDiff Topology

/-- A local inverse of the actual additive-circle projection. -/
def logChart (L t : ℝ) : OpenPartialHomeomorph (AddCircle L) ℝ :=
  (AddCircle.isLocalHomeomorph_coe L).localInverseAt t

@[simp] theorem logChart_symm (L a : ℝ) :
    ((logChart L a).symm : ℝ → AddCircle L) = ((↑) : ℝ → AddCircle L) :=
  (AddCircle.isLocalHomeomorph_coe L).localInverseAt_symm a

/-- No choice of logarithm is claimed to be continuous on the whole circle. -/
def representative (L : ℝ) (z : AddCircle L) : ℝ :=
  Classical.choose (QuotientAddGroup.mk_surjective z)

@[simp] theorem representative_coe (L : ℝ) (z : AddCircle L) :
    (representative L z : AddCircle L) = z :=
  Classical.choose_spec (QuotientAddGroup.mk_surjective z)

/-- The standard real local-logarithm atlas; the quotient topology is retained. -/
@[implicit_reducible] def chartedSpace (L : ℝ) : ChartedSpace ℝ (AddCircle L) where
  atlas := range (logChart L)
  chartAt z := logChart L (representative L z)
  mem_chart_source z := by
    simpa only [logChart, representative_coe] using
      (AddCircle.isLocalHomeomorph_coe L).apply_self_mem_localInverseAt_source
        (x := representative L z)
  chart_mem_atlas z := mem_range_self (representative L z)

/-- Every local logarithm composed with the covering projection is locally
an affine translation, including points across integer-period seams. -/
theorem log_comp_coe_contDiffAt (L a t : ℝ)
    (ht : (t : AddCircle L) ∈ (logChart L a).source) :
    ContDiffAt ℝ ∞ (fun s : ℝ => logChart L a (s : AddCircle L)) t := by
  let e := logChart L a
  let d := e (t : AddCircle L) - t
  have hproj : ((e (t : AddCircle L) : ℝ) : AddCircle L) = (t : AddCircle L) :=
    (AddCircle.isLocalHomeomorph_coe L).apply_localInverseAt_of_mem ht
  have hn : ∀ᶠ s in nhds t, s+d ∈ e.target := by
    apply (show ContinuousAt (fun s : ℝ => s+d) t by fun_prop)
    have he : t+d = e (t : AddCircle L) := by dsimp [d]; ring
    change e.target ∈ nhds (t+d)
    rw [he]
    exact e.open_target.mem_nhds (e.map_source ht)
  have heq : (fun s : ℝ => logChart L a (s : AddCircle L)) =ᶠ[nhds t]
      (fun s : ℝ => s+d) := by
    filter_upwards [hn] with s hs
    have hc : ((s+d : ℝ) : AddCircle L) = (s : AddCircle L) := by
      simp only [d, AddCircle.coe_add, AddCircle.coe_sub, hproj, sub_self, add_zero]
    have h := e.right_inv hs
    change e (((AddCircle.isLocalHomeomorph_coe L).localInverseAt a).symm (s+d)) = s+d at h
    simpa only [(AddCircle.isLocalHomeomorph_coe L).localInverseAt_symm, hc] using h
  have htranslation : ContDiffAt ℝ ∞ (fun s : ℝ => s+d) t := by fun_prop
  exact htranslation.congr_of_eventuallyEq heq

/-- The local-logarithm atlas is smooth: its transitions are locally translations. -/
theorem isManifold (L : ℝ) :
    letI := chartedSpace L; IsManifold 𝓘(ℝ,ℝ) ∞ (AddCircle L) := by
  letI := chartedSpace L
  apply isManifold_of_contDiffOn
  rintro e f ⟨a,rfl⟩ ⟨b,rfl⟩ t ht
  have hb : (t : AddCircle L) ∈ (logChart L b).source := by
    have hb := ht.1.2
    change (logChart L a).symm t ∈ (logChart L b).source at hb
    rwa [logChart_symm] at hb
  change ContDiffWithinAt ℝ ∞
    (fun s => logChart L b ((logChart L a).symm s)) _ t
  simp only [logChart_symm]
  exact (log_comp_coe_contDiffAt L b t hb).contDiffWithinAt

/-- The real quotient map is locally smoothly invertible in this atlas.
The circle's topology is the existing additive quotient topology. -/
theorem coe_isLocalDiffeomorph (L : ℝ) :
    letI := chartedSpace L;
    IsLocalDiffeomorph 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ ((↑) : ℝ → AddCircle L) := by
  letI := chartedSpace L
  letI : IsManifold 𝓘(ℝ,ℝ) ∞ (AddCircle L) := isManifold L
  intro t
  have ha : logChart L t ∈ IsManifold.maximalAtlas 𝓘(ℝ,ℝ) ∞ (AddCircle L) :=
    IsManifold.subset_maximalAtlas (mem_range_self t)
  refine ⟨{ toPartialEquiv := (logChart L t).toPartialEquiv.symm
            open_source := (logChart L t).open_target
            open_target := (logChart L t).open_source
            contMDiffOn_toFun := contMDiffOn_symm_of_mem_maximalAtlas ha
            contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas ha },
    (AddCircle.isLocalHomeomorph_coe L).self_mem_localInverseAt_target, ?_⟩
  intro s _
  exact (congrFun (logChart_symm L t) s).symm

end PoincareConjecture.Topology.FiberSaturation.CircleSmooth
