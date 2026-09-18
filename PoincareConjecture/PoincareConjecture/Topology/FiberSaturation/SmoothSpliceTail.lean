import PoincareConjecture.Topology.FiberSaturation.SmoothIntervalTrivialization

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
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G} {p : M → ℝ}

/-- A fixed-height transition is a diffeomorphism in the original fiber structure. -/
def coordChangeDiffeomorph {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    {c : ℝ} (hc : c ∈ e.baseSet) (hc' : c ∈ f.baseSet) : F ≃ₘ⟮J, J⟯ F where
  toEquiv := (e.coordChangeHomeomorph f hc hc').toEquiv
  contMDiff_toFun := (contMDiffOn_coordChange he hf).comp_contMDiff
    (contMDiff_const.prodMk contMDiff_id) (fun _ => ⟨⟨hc,hc'⟩,mem_univ _⟩)
  contMDiff_invFun := (contMDiffOn_coordChange hf he).comp_contMDiff
    (contMDiff_const.prodMk contMDiff_id) (fun _ => ⟨⟨hc',hc⟩,mem_univ _⟩)

/-- Away from the splice, the correcting family freezes to one fiber map. -/
theorem matchNear_right_tail {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    {c d : ℝ} (hd : 0 < d)
    (hsub : Ioo (c-2*d) (c+2*d) ⊆ e.baseSet ∩ f.baseSet)
    {z : M} (hz : p z ∈ f.baseSet) (ht : c+2*d ≤ p z) :
    matchNear he hf hd hsub z = (p z, f.coordChange e c (f z).2) := by
  change ((f z).1, f.coordChange e (seamClamp c d (f z).1) (f z).2) = _
  rw [f.coe_fst' hz, seamClamp_eq_center hd (Or.inr ht)]

/-- A smooth splice preserves the left chart and has a constant fiber
transition from the right chart outside the adjustment collar. -/
theorem exists_smooth_splice_with_tail {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    (hp : Continuous p) {c d : ℝ} (hd : 0 < d)
    (hsub : Ioo (c-2*d) (c+2*d) ⊆ e.baseSet ∩ f.baseSet) :
    ∃ k : Trivialization F p, ∃ δ : F ≃ₘ⟮J, J⟯ F,
      IsSmoothTrivialization I J k ∧
      k.baseSet = (Iic c).ite e.baseSet f.baseSet ∧
      (∀ z, p z ≤ c → k z = e z) ∧
      (∀ z, c+2*d ≤ p z → p z ∈ f.baseSet → k z = (p z, δ (f z).2)) := by
  classical
  let g := matchNear he hf hd hsub
  have hg : IsSmoothTrivialization I J g := matchNear_smooth he hf hd hsub
  have hsmall : Ioo (c-d) (c+d) ⊆ e.baseSet ∩ g.baseSet := by
    intro t ht
    exact hsub (by constructor <;> linarith [ht.1,ht.2])
  have hc : c ∈ Ioo (c-d) (c+d) := by constructor <;> linarith
  have heq : EqOn e g (p ⁻¹' Ioo (c-d) (c+d)) :=
    fun _ hz => (matchNear_eq he hf hd hsub hz).symm
  have heqc : ∀ z, p z = c → e z = g z := by
    intro z hz
    apply heq
    change p z ∈ Ioo (c-d) (c+d)
    rwa [hz]
  let k := e.piecewiseLeOfEq g c (hsmall hc).1 (hsmall hc).2 heqc
  let δ := coordChangeDiffeomorph hf he (hsmall hc).2 (hsmall hc).1
  refine ⟨k, δ, smooth_piecewiseLeOfEq he hg hp hd hsmall heq
    (hsmall hc).1 (hsmall hc).2 heqc, rfl, ?_, ?_⟩
  · intro z hz
    change (if p z ≤ c then e z else g z) = e z
    exact if_pos hz
  · intro z ht hz
    change (if p z ≤ c then e z else g z) = (p z, δ (f z).2)
    rw [if_neg (by linarith : ¬ p z ≤ c)]
    exact matchNear_right_tail he hf hd hsub hz ht

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
