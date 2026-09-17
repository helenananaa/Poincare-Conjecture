import PoincareConjecture

open Set PoincareConjecture.Topology.FiberSaturation
open PoincareConjecture.Topology.FiberSaturation.MappingTorus
noncomputable section

/-- A nontrivial twist, used with the actual quotient rather than a dummy map. -/
def regionAntipodalTwist : Sphere2 ≃ₜ Sphere2 where
  toFun x := ⟨-x.1, by simp⟩
  invFun x := ⟨-x.1, by simp⟩
  left_inv x := by apply Subtype.ext; exact neg_neg x.1
  right_inv x := by apply Subtype.ext; exact neg_neg x.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

example : closure (proj regionAntipodalTwist 4 ''
    ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1)) =
    proj regionAntipodalTwist 4 '' ((univ : Set Sphere2) ×ˢ Icc (-1 : ℝ) 1) :=
  closure_image_openStrip regionAntipodalTwist (by norm_num) (by norm_num)

-- A full-period region must not pass the strict-boundary test.
example : ¬ (frontier (closure (proj regionAntipodalTwist 4 ''
    ((univ : Set Sphere2) ×ˢ Ioo (0 : ℝ) 4)))).Nonempty := by
  have h := frontier_closure_image_period_empty regionAntipodalTwist
    (L := 4) (by norm_num) 0
  simpa using (h ▸ Set.not_nonempty_empty :
    ¬ (frontier (closure (proj regionAntipodalTwist 4 ''
      ((univ : Set Sphere2) ×ˢ Ioo (0 : ℝ) (0+4))))).Nonempty)

-- All hypotheses of the new classification are instantiated on an actual
-- antipodally twisted sphere quotient and a short cylinder region.
example : Nonempty
    (↥(closure (proj regionAntipodalTwist 4 '' ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1))) ≃ₜ
      (Sphere2 × Icc (0 : ℝ) 1)) := by
  let φ := regionAntipodalTwist
  let D : Set (Space φ 4) := proj φ 4 '' ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1)
  have ho : IsOpen D := isOpenMap_proj φ 4 _ (isOpen_univ.prod isOpen_Ioo)
  have hc : IsConnected D := (isConnected_univ.prod
    ⟨⟨0, by norm_num⟩, isPreconnected_Ioo⟩).image _ (continuous_proj φ 4).continuousOn
  have hs : FiberSaturated (proj φ 4 ⁻¹' D) := by
    intro x₁ x₂ t
    rintro ⟨p, hp, heq⟩
    obtain ⟨n, hn⟩ := (proj_eq_iff φ 4 p (x₁,t)).mp heq
    refine ⟨((φ ^ n).symm x₂, p.2), ⟨mem_univ _, hp.2⟩, ?_⟩
    apply (proj_eq_iff φ 4 _ _).mpr
    refine ⟨n, ?_⟩
    apply Prod.ext
    · simp [deck]
    · change p.2 + (n : ℝ) * 4 = t
      exact congrArg Prod.snd hn
  have hfr : FiberSaturated (proj φ 4 ⁻¹' frontier D) := by
    rw [(isOpenMap_proj φ 4).preimage_frontier_eq_frontier_preimage (continuous_proj φ 4)]
    rw [hs.eq_univ_prod_image]
    exact frontier_fiberSaturated_univ_prod _
  obtain ⟨x⟩ := (inferInstance : Nonempty Sphere2)
  have hnot : proj φ 4 (x,2) ∉ closure D := by
    change proj φ 4 (x,2) ∉ closure (proj φ 4 '' ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1))
    rw [closure_image_openStrip φ (by norm_num) (by norm_num),
      image_closedStrip_eq_compl_gap φ (by norm_num)]
    intro h
    exact h ⟨(x,2), ⟨mem_univ _, by norm_num⟩, rfl⟩
  have hf : (frontier (closure D)).Nonempty := by
    rw [nonempty_frontier_iff]
    refine ⟨⟨proj φ 4 (x,0), subset_closure ?_⟩, ?_⟩
    · exact ⟨(x,0), ⟨mem_univ _, by norm_num⟩, rfl⟩
    · intro h
      apply hnot
      rw [h]
      exact mem_univ _
  exact region_closure_homeomorph φ (by norm_num) ho hc hfr hf
