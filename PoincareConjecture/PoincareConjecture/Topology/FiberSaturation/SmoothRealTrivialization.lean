import PoincareConjecture.Topology.FiberSaturation.PeriodicExtensionBijective

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Function Bundle Manifold
open scoped Manifold ContDiff
variable {V W H G M F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace H] [TopologicalSpace G]
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace F] [ChartedSpace G F]
  {I : ModelWithCorners ℝ V H} {J : ModelWithCorners ℝ W G} {p : M → ℝ}

/-- Local smooth bundle charts and a smooth height-shifting deck map produce
an actual global diffeomorphism over R, equivariant for every integer period.
The original smooth structures are retained. No all-real smoothness assumption,
chosen period chart, twist, inverse or global parametrization is an input. -/
theorem exists_equivariant_real_diffeomorph (hp : Continuous p)
    (hloc : ∀ t : ℝ, ∃ k : Trivialization F p,
      t ∈ k.baseSet ∧ IsSmoothTrivialization I J k)
    (T : M ≃ₘ⟮I,I⟯ M) {L : ℝ} (hL : 0 < L)
    (hT : ∀ z, p (T z) = p z+L) :
    ∃ φ : F ≃ₘ⟮J,J⟯ F, ∃ e : (ℝ × F) ≃ₘ⟮(𝓘(ℝ,ℝ)).prod J,I⟯ M,
      (∀ t x, p (e (t,x)) = t) ∧
      (∀ n : ℤ, ∀ t x, e (t+(n : ℝ)*L,x) =
        (T.toHomeomorph ^ n) (e (t,(φ.toHomeomorph ^ n) x))) := by
  obtain ⟨k,φ,ε,hε,hwidth,_,hseg,hlow,hhigh,hseam,hinv⟩ :=
    exists_smooth_endmatched_period_chart hp hloc T hL hT
  have hwide : Ioo (-ε) (L+ε) ⊆ k.baseSet := by
    intro t ht
    by_cases ht0 : t < 0
    · exact hlow ⟨ht.1,by linarith⟩
    · by_cases htL : t ≤ L
      · exact hseg ⟨le_of_not_gt ht0,htL⟩
      · exact hhigh ⟨by linarith,ht.2⟩
  have hlocal := periodicExtend_isLocalDiffeomorph T φ k.toOpenPartialHomeomorph.symm
    hL hε (by linarith : ε < L)
    (fun t x ht => hseam x t ht) (fun t ht x => hinv t (hwide ht) x)
  have hbij := periodicExtend_bijective T φ k hL hT hseg
  let e := hlocal.diffeomorphOfBijective hbij
  refine ⟨φ,e,?_,?_⟩
  · intro t x
    exact periodicExtend_height T φ k hL hT hseg t x
  · intro n t x
    exact periodicExtend_translate T.toHomeomorph φ.toHomeomorph
      k.toOpenPartialHomeomorph.symm hL t x n

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
