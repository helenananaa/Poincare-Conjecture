import PoincareConjecture

open Set PoincareConjecture.Topology.FiberSaturation
open PoincareConjecture.Topology.FiberSaturation.MappingTorus
noncomputable section

/-- A genuinely nonidentity twist on the actual sphere. -/
def antipodalTwist : Sphere2 ≃ₜ Sphere2 where
  toFun x := ⟨-x.1, by simp⟩
  invFun x := ⟨-x.1, by simp⟩
  left_inv x := by apply Subtype.ext; exact neg_neg x.1
  right_inv x := by apply Subtype.ext; exact neg_neg x.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

example (x : Sphere2) : proj antipodalTwist 4 (antipodalTwist x, 4) =
    proj antipodalTwist 4 (x,0) := by
  simpa using period_endpoint_identification antipodalTwist 4 0 x

example : InjOn (proj antipodalTwist 4) ((univ : Set Sphere2) ×ˢ Icc (-1 : ℝ) 1) :=
  proj_injOn_closedStrip antipodalTwist (by norm_num) (by norm_num)

example : ¬ InjOn (proj antipodalTwist 4) ((univ : Set Sphere2) ×ˢ Icc (0 : ℝ) 4) := by
  rw [proj_injOn_closedStrip_iff antipodalTwist (by norm_num)]
  norm_num

example : Nonempty (↥((univ : Set Sphere2) ×ˢ Icc (-1 : ℝ) 1) ≃ₜ
    ↥(proj antipodalTwist 4 '' ((univ : Set Sphere2) ×ˢ Icc (-1 : ℝ) 1))) :=
  ⟨closedStripHomeomorphImage antipodalTwist (by norm_num) (by norm_num)⟩

example (φ : Sphere2 ≃ₜ Sphere2) (x : Sphere2) :
    proj φ.symm 4 (x,4) = proj φ.symm 4 (φ x,0) := by
  simpa using blueprint_endpoint_convention φ 4 0 x

example : frontier (closure (proj antipodalTwist 4 ''
    ((univ : Set Sphere2) ×ˢ Ioo (0 : ℝ) 4))) = ∅ := by
  simpa using frontier_closure_image_period_empty antipodalTwist (by norm_num) 0

-- The nonempty-frontier-of-closure input has genuine sphere-quotient witnesses.
example (φ : Sphere2 ≃ₜ Sphere2) :
    (frontier (closure (proj φ 4 '' ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1)))).Nonempty := by
  let S : Set (Sphere2 × ℝ) := univ ×ˢ Ioo (-1 : ℝ) 1
  let T : Set (Sphere2 × ℝ) := univ ×ˢ Ioo (3/2 : ℝ) (5/2)
  have hdis : Disjoint (proj φ 4 '' S) (proj φ 4 '' T) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨p, hp, hpz⟩ ⟨q, hq, hqz⟩
    have hp' : p ∈ (univ : Set Sphere2) ×ˢ Icc (-1 : ℝ) (5/2) :=
      ⟨mem_univ _, by constructor <;> linarith [hp.2.1, hp.2.2]⟩
    have hq' : q ∈ (univ : Set Sphere2) ×ˢ Icc (-1 : ℝ) (5/2) :=
      ⟨mem_univ _, by constructor <;> linarith [hq.2.1, hq.2.2]⟩
    have heq := proj_injOn_closedStrip φ (by norm_num : (0 : ℝ) < 4)
      (by norm_num : (5/2 : ℝ)-(-1) < 4) hp' hq' (hpz.trans hqz.symm)
    have hh := congrArg Prod.snd heq
    linarith [hp.2.2, hq.2.1]
  have ho : IsOpen (proj φ 4 '' T) :=
    isOpenMap_proj φ 4 T (isOpen_univ.prod isOpen_Ioo)
  obtain ⟨x⟩ := (inferInstance : Nonempty Sphere2)
  have hT : proj φ 4 (x,2) ∈ proj φ 4 '' T :=
    ⟨(x,2), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hnot : proj φ 4 (x,2) ∉ closure (proj φ 4 '' S) := by
    intro h
    exact Set.disjoint_left.mp (hdis.closure_left ho) h hT
  change (frontier (closure (proj φ 4 '' S))).Nonempty
  rw [nonempty_frontier_iff]
  refine ⟨⟨proj φ 4 (x,0), subset_closure ?_⟩, ?_⟩
  · exact ⟨(x,0), ⟨mem_univ _, by norm_num⟩, rfl⟩
  · intro h
    apply hnot
    rw [h]
    exact mem_univ _
