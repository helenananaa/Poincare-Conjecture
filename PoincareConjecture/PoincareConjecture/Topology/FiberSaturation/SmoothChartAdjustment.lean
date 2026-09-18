import PoincareConjecture.Topology.FiberSaturation.SmoothBundleChart

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Bundle Manifold
open scoped Manifold ContDiff
variable {V W H G M F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace F] [ChartedSpace G F]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G}
  {p : M → ℝ}

/-- A smooth change of fiber coordinates leaves the base coordinate fixed. -/
def adjust (e : Trivialization F p)
    (g : (ℝ × F) ≃ₘ⟮(𝓘(ℝ, ℝ)).prod J, (𝓘(ℝ, ℝ)).prod J⟯ (ℝ × F))
    (hg : ∀ z, (g z).1 = z.1) : Trivialization F p where
  toOpenPartialHomeomorph := e.toOpenPartialHomeomorph.transHomeomorph g.toHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := by
    ext z
    change g.symm z ∈ e.target ↔ z ∈ e.baseSet ×ˢ univ
    rw [e.mem_target]
    have hh : (g.symm z).1 = z.1 := by
      simpa only [g.apply_symm_apply] using (hg (g.symm z)).symm
    simp only [hh, mem_prod, mem_univ, and_true]
  proj_toFun z hz := (hg (e z)).trans (e.coe_fst hz)

@[simp] theorem adjust_apply (e : Trivialization F p)
    (g : (ℝ × F) ≃ₘ⟮(𝓘(ℝ, ℝ)).prod J, (𝓘(ℝ, ℝ)).prod J⟯ (ℝ × F))
    (hg : ∀ z, (g z).1 = z.1) (z : M) : adjust e g hg z = g (e z) := rfl

theorem isSmooth_adjust {e : Trivialization F p} (he : IsSmoothTrivialization I J e)
    (g : (ℝ × F) ≃ₘ⟮(𝓘(ℝ, ℝ)).prod J, (𝓘(ℝ, ℝ)).prod J⟯ (ℝ × F))
    (hg : ∀ z, (g z).1 = z.1) : IsSmoothTrivialization I J (adjust e g hg) := by
  constructor
  · exact g.contMDiff.comp_contMDiffOn he.1
  · exact he.2.comp g.symm.contMDiff.contMDiffOn (fun _ hz => hz)

/-- Smoothly adjust f so that it agrees with e on an entire collar. -/
def matchNear {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    {c d : ℝ} (hd : 0 < d)
    (hsub : Ioo (c-2*d) (c+2*d) ⊆ e.baseSet ∩ f.baseSet) : Trivialization F p :=
  adjust f (transitionDiffeomorph hf he (seamClamp c d) (contDiff_seamClamp c d)
    (fun t => ⟨(hsub (seamClamp_mem hd t)).2,(hsub (seamClamp_mem hd t)).1⟩))
      (fun _ => rfl)

theorem matchNear_smooth {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    {c d : ℝ} (hd : 0 < d)
    (hsub : Ioo (c-2*d) (c+2*d) ⊆ e.baseSet ∩ f.baseSet) :
    IsSmoothTrivialization I J (matchNear he hf hd hsub) :=
  isSmooth_adjust hf _ _

theorem matchNear_eq {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    {c d : ℝ} (hd : 0 < d)
    (hsub : Ioo (c-2*d) (c+2*d) ⊆ e.baseSet ∩ f.baseSet)
    {z : M} (hz : p z ∈ Ioo (c-d) (c+d)) : matchNear he hf hd hsub z = e z := by
  have hz' : p z ∈ Ioo (c-2*d) (c+2*d) := by constructor <;> linarith [hz.1,hz.2]
  have hfe := (hsub hz').2
  have hee := (hsub hz').1
  change ((f z).1, f.coordChange e (seamClamp c d (f z).1) (f z).2) = e z
  rw [f.coe_fst' hfe, seamClamp_eq_self hd (Ioo_subset_Icc_self hz),
    f.coordChange_apply_snd e hfe]
  exact e.mk_proj_snd' hee

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
