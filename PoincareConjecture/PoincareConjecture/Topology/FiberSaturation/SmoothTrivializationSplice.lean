import PoincareConjecture.Topology.FiberSaturation.SmoothLocalPasting

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Bundle Manifold Filter
open scoped Manifold ContDiff Topology
variable {V W H G M F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace F] [ChartedSpace G F]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G}
  {p : M → ℝ}

/-- Agreement of actual charts on whole fibers also identifies the inverse
charts there; inverse compatibility is derived rather than assumed. -/
theorem inverse_eqOn_collar {e f : Trivialization F p} {A : Set ℝ}
    (hsub : A ⊆ e.baseSet ∩ f.baseSet) (heq : EqOn e f (p ⁻¹' A)) :
    EqOn e.toOpenPartialHomeomorph.symm f.toOpenPartialHomeomorph.symm
      ((Prod.fst : ℝ × F → ℝ) ⁻¹' A) := by
  intro z hz
  have hze : z ∈ e.target := e.mem_target.mpr (hsub hz).1
  have hpz : p (e.toOpenPartialHomeomorph.symm z) = z.1 := e.proj_symm_apply hze
  have hx : e.toOpenPartialHomeomorph.symm z ∈ f.source := by
    apply f.mem_source.mpr
    rw [hpz]
    exact (hsub hz).2
  have hfe : f (e.toOpenPartialHomeomorph.symm z) = z :=
    (heq (by change p (e.toOpenPartialHomeomorph.symm z) ∈ A; rwa [hpz])).symm.trans
      (e.apply_symm_apply hze)
  calc
    e.toOpenPartialHomeomorph.symm z =
        f.toOpenPartialHomeomorph.symm (f (e.toOpenPartialHomeomorph.symm z)) :=
      (f.toOpenPartialHomeomorph.left_inv hx).symm
    _ = f.toOpenPartialHomeomorph.symm z := congrArg f.toOpenPartialHomeomorph.symm hfe

/-- Once charts agree on a collar, the standard topological piecewise
trivialization is smooth in both directions in the original structures. -/
theorem smooth_piecewiseLeOfEq {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    (hp : Continuous p) {c d : ℝ} (hd : 0 < d)
    (hsub : Ioo (c-d) (c+d) ⊆ e.baseSet ∩ f.baseSet)
    (heq : EqOn e f (p ⁻¹' Ioo (c-d) (c+d)))
    (hc : c ∈ e.baseSet) (hc' : c ∈ f.baseSet)
    (heqc : ∀ z, p z = c → e z = f z) :
    IsSmoothTrivialization I J (e.piecewiseLeOfEq f c hc hc' heqc) := by
  classical
  constructor
  · exact contMDiffOn_ite_le e.open_source f.open_source he.1 hf.1 hp hd heq
  · have hi := inverse_eqOn_collar hsub heq
    have h := contMDiffOn_ite_le e.open_target f.open_target he.2 hf.2 continuous_fst hd hi
    have ht : Iic c ×ˢ (univ : Set F) = (Prod.fst : ℝ × F → ℝ) ⁻¹' Iic c := by
      ext z
      simp
    change ContMDiffOn ((𝓘(ℝ, ℝ)).prod J) I ∞
      (fun z => if z ∈ Iic c ×ˢ (univ : Set F) then e.toOpenPartialHomeomorph.symm z
        else f.toOpenPartialHomeomorph.symm z)
      ((Iic c ×ˢ (univ : Set F)).ite e.target f.target)
    simpa only [ht, mem_preimage, mem_Iic] using h

/-- Local construction: no equality of the original charts, at the cut or
elsewhere, is required. The second chart is smoothly adjusted first. -/
theorem exists_smooth_splice_of_collar {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    (hp : Continuous p) {c d : ℝ} (hd : 0 < d)
    (hsub : Ioo (c-2*d) (c+2*d) ⊆ e.baseSet ∩ f.baseSet) :
    ∃ k : Trivialization F p, IsSmoothTrivialization I J k ∧
      k.baseSet = (Iic c).ite e.baseSet f.baseSet ∧
      ∀ z, p z ≤ c → k z = e z := by
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
  refine ⟨k, smooth_piecewiseLeOfEq he hg hp hd hsmall heq
    (hsmall hc).1 (hsmall hc).2 heqc, rfl, ?_⟩
  intro z hz
  change (if p z ≤ c then e z else g z) = e z
  exact if_pos hz


/-- Any two smooth trivializations overlapping at c can be smoothly spliced.
The collar radius and the correcting fiber diffeomorphism are constructed. -/
theorem exists_smooth_splice {e f : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hf : IsSmoothTrivialization I J f)
    (hp : Continuous p) {c : ℝ} (hc : c ∈ e.baseSet) (hc' : c ∈ f.baseSet) :
    ∃ k : Trivialization F p, IsSmoothTrivialization I J k ∧
      k.baseSet = (Iic c).ite e.baseSet f.baseSet ∧
      ∀ z, p z ≤ c → k z = e z := by
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
    ((e.open_baseSet.inter f.open_baseSet).mem_nhds ⟨hc,hc'⟩)
  apply exists_smooth_splice_of_collar he hf hp (c := c) (d := r/3) (by positivity)
  intro t ht
  apply hball
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  constructor <;> linarith [ht.1,ht.2]

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
