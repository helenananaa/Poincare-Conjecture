import PoincareConjecture.Topology.FiberSaturation.SmoothPeriodicExtension

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

/-- The integer extension has the original height, not merely its circle class. -/
theorem periodicExtend_height (T : M ≃ₘ⟮I,I⟯ M) (φ : F ≃ₘ⟮J,J⟯ F)
    (k : Trivialization F p) {L : ℝ} (hL : 0 < L)
    (hT : ∀ z, p (T z) = p z+L) (hseg : Icc 0 L ⊆ k.baseSet) (t : ℝ) (x : F) :
    p (periodicExtend T.toHomeomorph φ.toHomeomorph k.toOpenPartialHomeomorph.symm L (t,x)) = t := by
  unfold periodicExtend
  rw [height_integer_iterate T hT]
  have hr := periodRemainder_mem hL t
  rw [k.proj_symm_apply' (hseg (Ico_subset_Icc_self hr))]
  unfold periodRemainder
  ring

/-- Different heights cannot collide; within one height the original chart
and both integer iterates are injective. No global injectivity is assumed. -/
theorem periodicExtend_injective (T : M ≃ₘ⟮I,I⟯ M) (φ : F ≃ₘ⟮J,J⟯ F)
    (k : Trivialization F p) {L : ℝ} (hL : 0 < L)
    (hT : ∀ z, p (T z) = p z+L) (hseg : Icc 0 L ⊆ k.baseSet) :
    Injective (periodicExtend T.toHomeomorph φ.toHomeomorph k.toOpenPartialHomeomorph.symm L) := by
  rintro ⟨t,x⟩ ⟨s,y⟩ h
  have hts := congrArg p h
  rw [periodicExtend_height T φ k hL hT hseg,
    periodicExtend_height T φ k hL hT hseg] at hts
  subst s
  have hr := hseg (Ico_subset_Icc_self (periodRemainder_mem hL t))
  change (T.toHomeomorph ^ periodIndex L t) _ = (T.toHomeomorph ^ periodIndex L t) _ at h
  have hh := congrArg k ((T.toHomeomorph ^ periodIndex L t).injective h)
  rw [k.apply_symm_apply (k.mem_target.mpr hr),
    k.apply_symm_apply (k.mem_target.mpr hr)] at hh
  exact Prod.ext rfl ((φ.toHomeomorph ^ periodIndex L t).injective (congrArg Prod.snd hh))

/-- Every point can be moved back into the fundamental period and read in
its chart, then moved forward again. This proves full surjectivity. -/
theorem periodicExtend_surjective (T : M ≃ₘ⟮I,I⟯ M) (φ : F ≃ₘ⟮J,J⟯ F)
    (k : Trivialization F p) {L : ℝ} (hL : 0 < L)
    (hT : ∀ z, p (T z) = p z+L) (hseg : Icc 0 L ⊆ k.baseSet) :
    Surjective (periodicExtend T.toHomeomorph φ.toHomeomorph k.toOpenPartialHomeomorph.symm L) := by
  intro z
  let n := periodIndex L (p z)
  let y := (T.toHomeomorph ^ (-n)) z
  have hpy : p y = periodRemainder L (p z) := by
    rw [height_integer_iterate T hT]
    simp [periodRemainder,n,sub_eq_add_neg]
  have hyb : p y ∈ k.baseSet := by
    rw [hpy]
    exact hseg (Ico_subset_Icc_self (periodRemainder_mem hL (p z)))
  refine ⟨(p z,(φ.toHomeomorph ^ n).symm (k y).2),?_⟩
  change (T.toHomeomorph ^ n) (k.toOpenPartialHomeomorph.symm
    (periodRemainder L (p z),(φ.toHomeomorph ^ n) ((φ.toHomeomorph ^ n).symm (k y).2))) = z
  rw [Homeomorph.apply_symm_apply]
  have hpair : (periodRemainder L (p z),(k y).2) = k y := by
    rw [← hpy]
    exact k.mk_proj_snd' hyb
  rw [hpair]
  have hleft : k.toOpenPartialHomeomorph.symm (k y) = y :=
    k.toPartialEquiv.left_inv (k.mem_source.mpr hyb)
  rw [hleft]
  change (T.toHomeomorph ^ n) ((T.toHomeomorph ^ (-n)) z) = z
  rw [← Homeomorph.mul_apply,← zpow_add]
  simp

theorem periodicExtend_bijective (T : M ≃ₘ⟮I,I⟯ M) (φ : F ≃ₘ⟮J,J⟯ F)
    (k : Trivialization F p) {L : ℝ} (hL : 0 < L)
    (hT : ∀ z, p (T z) = p z+L) (hseg : Icc 0 L ⊆ k.baseSet) :
    Bijective (periodicExtend T.toHomeomorph φ.toHomeomorph k.toOpenPartialHomeomorph.symm L) :=
  ⟨periodicExtend_injective T φ k hL hT hseg,periodicExtend_surjective T φ k hL hT hseg⟩

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
