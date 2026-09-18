import PoincareConjecture.Topology.FiberSaturation.SmoothDeckChart

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

/-- The local construction matches both end collars by one constant fiber
DIFFEOMORPHISM. Neither matching nor the fiber map is an input. -/
theorem periodic_chart_of_collars {e : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hp : Continuous p)
    (T : M ≃ₘ⟮I,I⟯ M) {L r : ℝ} (hr : 0 < r) (hL : 4*r < L)
    (hT : ∀ z, p (T z) = p z+L) (hsegment : Icc 0 L ⊆ e.baseSet)
    (hzero : Ioo (-r) r ⊆ e.baseSet) (hend : Ioo (L-r) (L+r) ⊆ e.baseSet) :
    ∃ k : Trivialization F p, ∃ δ : F ≃ₘ⟮J,J⟯ F, ∃ ε : ℝ,
      0 < ε ∧ 2*ε < L ∧ IsSmoothTrivialization I J k ∧
      Icc 0 L ⊆ k.baseSet ∧ Ioo (-ε) ε ⊆ k.baseSet ∧
      Ioo (L-ε) (L+ε) ⊆ k.baseSet ∧
      ∀ z, p z ∈ Ioo (-ε) ε → k (T z) = (p z+L, δ (k z).2) := by
  let f := deckTranslate e T hT
  let c : ℝ := L-r/2
  let d : ℝ := r/8
  have hd : 0 < d := by dsimp [d]; positivity
  have hsub : Ioo (c-2*d) (c+2*d) ⊆ e.baseSet ∩ f.baseSet := by
    intro t ht
    constructor
    · apply hend
      dsimp [c,d] at ht
      constructor <;> linarith [ht.1,ht.2]
    · change t-L ∈ e.baseSet
      apply hzero
      dsimp [c,d] at ht
      constructor <;> linarith [ht.1,ht.2]
  obtain ⟨k,δ,hk,hbase,hleft,hright⟩ := exists_smooth_splice_with_tail he
    (deckTranslate_smooth he T hT) hp hd hsub
  have hseg : Icc 0 L ⊆ k.baseSet := by
    rw [hbase]
    apply subset_ite.mpr
    constructor
    · intro t ht
      exact hsegment ht.1
    · intro t ht
      change t-L ∈ e.baseSet
      apply hzero
      have ht' : c < t := not_le.mp ht.2
      dsimp [c] at ht'
      constructor <;> linarith [ht.1.1,ht.1.2]
  have hlow : Ioo (-(r/8)) (r/8) ⊆ k.baseSet := by
    rw [hbase]
    apply subset_ite.mpr
    constructor
    · intro t ht
      apply hzero
      constructor <;> linarith [ht.1.1,ht.1.2]
    · intro t ht
      exfalso
      apply ht.2
      change t ≤ c
      dsimp [c]
      linarith [ht.1.2]
  have hhigh : Ioo (L-r/8) (L+r/8) ⊆ k.baseSet := by
    rw [hbase]
    apply subset_ite.mpr
    constructor
    · intro t ht
      apply hend
      constructor <;> linarith [ht.1.1,ht.1.2]
    · intro t ht
      change t-L ∈ e.baseSet
      apply hzero
      constructor <;> linarith [ht.1.1,ht.1.2]
  refine ⟨k,δ,r/8,by positivity,by linarith,hk,hseg,hlow,hhigh,?_⟩
  intro z hz
  have hzleft : p z ≤ c := by dsimp [c]; linarith [hz.2]
  have hzright : c+2*d ≤ p (T z) := by
    rw [hT]
    dsimp [c,d]
    linarith [hz.1]
  have hzf : p (T z) ∈ f.baseSet := by
    change p (T z)-L ∈ e.baseSet
    rw [hT, add_sub_cancel_right]
    apply hzero
    constructor <;> linarith [hz.1,hz.2]
  rw [hright (T z) hzright hzf, hT, deckTranslate_deck_apply, hleft z hzleft]

/-- A smooth interval chart can be replaced by one whose two end germs are
related by a single constructed fiber diffeomorphism. -/
theorem exists_periodic_chart_from_interval {e : Trivialization F p}
    (he : IsSmoothTrivialization I J e) (hp : Continuous p)
    (T : M ≃ₘ⟮I,I⟯ M) {L : ℝ} (hL : 0 < L)
    (hT : ∀ z, p (T z) = p z+L) (hsegment : Icc 0 L ⊆ e.baseSet) :
    ∃ k : Trivialization F p, ∃ δ : F ≃ₘ⟮J,J⟯ F, ∃ ε : ℝ,
      0 < ε ∧ 2*ε < L ∧ IsSmoothTrivialization I J k ∧
      Icc 0 L ⊆ k.baseSet ∧ Ioo (-ε) ε ⊆ k.baseSet ∧
      Ioo (L-ε) (L+ε) ⊆ k.baseSet ∧
      ∀ z, p z ∈ Ioo (-ε) ε → k (T z) = (p z+L, δ (k z).2) := by
  obtain ⟨r₀,hr₀,hb₀⟩ := Metric.mem_nhds_iff.mp
    (e.open_baseSet.mem_nhds (hsegment ⟨le_rfl,hL.le⟩))
  obtain ⟨r₁,hr₁,hb₁⟩ := Metric.mem_nhds_iff.mp
    (e.open_baseSet.mem_nhds (hsegment ⟨hL.le,le_rfl⟩))
  let r : ℝ := min (min r₀ r₁) (L/8)
  have hr : 0 < r := lt_min (lt_min hr₀ hr₁) (by positivity)
  have hr0 : r ≤ r₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hr1 : r ≤ r₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hrL : r ≤ L/8 := min_le_right _ _
  apply periodic_chart_of_collars he hp T hr (by linarith) hT hsegment
  · intro t ht
    apply hb₀
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1,ht.2]
  · intro t ht
    apply hb₁
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [ht.1,ht.2]

/-- Local smooth bundle data plus a genuine smooth deck transformation yield
one smooth period chart with constant transition on whole end collars. -/
theorem exists_smooth_periodic_trivialization (hp : Continuous p)
    (hloc : ∀ t : ℝ, ∃ e : Trivialization F p,
      t ∈ e.baseSet ∧ IsSmoothTrivialization I J e)
    (T : M ≃ₘ⟮I,I⟯ M) {L : ℝ} (hL : 0 < L)
    (hT : ∀ z, p (T z) = p z+L) :
    ∃ k : Trivialization F p, ∃ δ : F ≃ₘ⟮J,J⟯ F, ∃ ε : ℝ,
      0 < ε ∧ 2*ε < L ∧ IsSmoothTrivialization I J k ∧
      Icc 0 L ⊆ k.baseSet ∧ Ioo (-ε) ε ⊆ k.baseSet ∧
      Ioo (L-ε) (L+ε) ⊆ k.baseSet ∧
      ∀ z, p z ∈ Ioo (-ε) ε → k (T z) = (p z+L, δ (k z).2) := by
  obtain ⟨e,he,hseg⟩ := exists_smooth_trivialization_Icc hp hloc 0 L
  exact exists_periodic_chart_from_interval he hp T hL hT hseg

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
