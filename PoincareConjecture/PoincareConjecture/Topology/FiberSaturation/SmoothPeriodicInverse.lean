import PoincareConjecture.Topology.FiberSaturation.SmoothPeriodicChart

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

/-- Both directions of a smooth chart give a genuine local diffeomorphism,
not merely a continuous locally invertible map. -/
theorem smooth_chart_inverse_localDiffeomorphAt {k : Trivialization F p}
    (hk : IsSmoothTrivialization I J k) {t : ℝ} (ht : t ∈ k.baseSet) (x : F) :
    IsLocalDiffeomorphAt ((𝓘(ℝ, ℝ)).prod J) I ∞
      k.toOpenPartialHomeomorph.symm (t,x) := by
  refine ⟨{ toPartialEquiv := k.toPartialEquiv.symm
            open_source := k.open_target
            open_target := k.open_source
            contMDiffOn_toFun := hk.2
            contMDiffOn_invFun := hk.1 }, k.mem_target.mpr ht, ?_⟩
  exact Set.eqOn_refl _ _

/-- Forward end matching forces the inverse-chart identity on a full collar.
The inverse fiber twist is derived, rather than required as a second hypothesis. -/
theorem periodic_inverse_seam {k : Trivialization F p} (T : M ≃ₘ⟮I,I⟯ M)
    (δ : F ≃ₘ⟮J,J⟯ F) {L ε : ℝ} (hT : ∀ z, p (T z) = p z+L)
    (hlow : Ioo (-ε) ε ⊆ k.baseSet) (hhigh : Ioo (L-ε) (L+ε) ⊆ k.baseSet)
    (hseam : ∀ z, p z ∈ Ioo (-ε) ε → k (T z) = (p z+L, δ (k z).2))
    (x : F) {t : ℝ} (ht : t ∈ Ioo (-ε) ε) :
    k.toOpenPartialHomeomorph.symm (t+L,x) =
      T (k.toOpenPartialHomeomorph.symm (t,δ.symm x)) := by
  let z := k.toOpenPartialHomeomorph.symm (t,δ.symm x)
  have hpz : p z = t := k.proj_symm_apply' (hlow ht)
  have hkz : k z = (t,δ.symm x) := k.apply_symm_apply (k.mem_target.mpr (hlow ht))
  have hz : p z ∈ Ioo (-ε) ε := hpz ▸ ht
  have hpTz : p (T z) ∈ k.baseSet := by
    apply hhigh
    rw [hT,hpz]
    constructor <;> linarith [ht.1,ht.2]
  have hval : k (T z) = (t+L,x) := by
    rw [hseam z hz,hpz,hkz,δ.apply_symm_apply]
  calc
    k.toOpenPartialHomeomorph.symm (t+L,x) =
        k.toOpenPartialHomeomorph.symm (k (T z)) := congrArg _ hval.symm
    _ = T z := k.toOpenPartialHomeomorph.left_inv (k.mem_source.mpr hpTz)

/-- Local smooth trivializations and a smooth deck map produce a genuine
smooth period parametrization with matching end germs and a smooth twist.
The complete all-real periodic extension is deliberately not asserted here. -/
theorem exists_smooth_endmatched_period_chart (hp : Continuous p)
    (hloc : ∀ t : ℝ, ∃ e : Trivialization F p,
      t ∈ e.baseSet ∧ IsSmoothTrivialization I J e)
    (T : M ≃ₘ⟮I,I⟯ M) {L : ℝ} (hL : 0 < L)
    (hT : ∀ z, p (T z) = p z+L) :
    ∃ k : Trivialization F p, ∃ φ : F ≃ₘ⟮J,J⟯ F, ∃ ε : ℝ,
      0 < ε ∧ 2*ε < L ∧ IsSmoothTrivialization I J k ∧
      Icc 0 L ⊆ k.baseSet ∧ Ioo (-ε) ε ⊆ k.baseSet ∧
      Ioo (L-ε) (L+ε) ⊆ k.baseSet ∧
      (∀ x t, t ∈ Ioo (-ε) ε → k.toOpenPartialHomeomorph.symm (t+L,x) =
        T (k.toOpenPartialHomeomorph.symm (t,φ x))) ∧
      (∀ t ∈ k.baseSet, ∀ x, IsLocalDiffeomorphAt ((𝓘(ℝ,ℝ)).prod J) I ∞
        k.toOpenPartialHomeomorph.symm (t,x)) := by
  obtain ⟨k,δ,ε,hε,hwidth,hk,hseg,hlow,hhigh,hseam⟩ :=
    exists_smooth_periodic_trivialization hp hloc T hL hT
  refine ⟨k,δ.symm,ε,hε,hwidth,hk,hseg,hlow,hhigh,?_,?_⟩
  · intro x t ht
    exact periodic_inverse_seam T δ hT hlow hhigh hseam x ht
  · intro t ht x
    exact smooth_chart_inverse_localDiffeomorphAt hk ht x

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
