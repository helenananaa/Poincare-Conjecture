import PoincareConjecture

open Set PoincareConjecture.Topology.FiberSaturation
open PoincareConjecture.Topology.FiberSaturation.MappingTorus
noncomputable section

/-- A nontrivial twist, used with the actual quotient rather than a dummy map. -/
def pairingAntipodalTwist : Sphere2 ≃ₜ Sphere2 where
  toFun x := ⟨-x.1, by simp⟩
  invFun x := ⟨-x.1, by simp⟩
  left_inv x := by apply Subtype.ext; exact neg_neg x.1
  right_inv x := by apply Subtype.ext; exact neg_neg x.1
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

-- Every premise is verified on a genuine antipodally twisted sphere quotient.
example : ∃ u v : AddCircle (4 : ℝ), u ≠ v ∧
    frontier (proj pairingAntipodalTwist 4 '' ((univ : Set Sphere2) ×ˢ Ioo (-1 : ℝ) 1)) =
      circleProjection pairingAntipodalTwist 4 ⁻¹' ({u,v} : Set (AddCircle (4 : ℝ))) := by
  let φ := pairingAntipodalTwist
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
  exact region_frontier_circle_pair φ (by norm_num) ho hc hfr hf

open Bundle
abbrev BoundaryPairingBundle := Bundle.Trivial (AddCircle (2 : ℝ)) Sphere2
local instance : T2Space (TotalSpace Sphere2 BoundaryPairingBundle) :=
  (Bundle.Trivial.homeomorphProd (AddCircle (2 : ℝ)) Sphere2).symm.t2Space

-- The connectedness witnesses refer to actual fibers in a standard bundle.
example (u : AddCircle (2 : ℝ)) :
    IsConnected ((TotalSpace.proj (F := Sphere2) (E := BoundaryPairingBundle)) ⁻¹' {u}) :=
  abstract_sphere_bundle_fiber_connected BoundaryPairingBundle u

-- No coordinates or chosen twist are additional inputs to the component theorem.
example {D : Set (TotalSpace Sphere2 BoundaryPairingBundle)}
    (ho : IsOpen D) (hc : IsConnected D) (hr : D = interior (closure D))
    (hs : ProjectionSaturated (TotalSpace.proj (F := Sphere2) (E := BoundaryPairingBundle))
      (frontier D)) (hn : (frontier D).Nonempty) :
    ∃ A B : Set (TotalSpace Sphere2 BoundaryPairingBundle),
      frontier D = A ∪ B ∧ IsConnected A ∧ IsConnected B ∧ Disjoint A B ∧
      (∀ z ∈ A, connectedComponentIn (frontier D) z = A) ∧
      (∀ z ∈ B, connectedComponentIn (frontier D) z = B) := by
  obtain ⟨u,v,_,hfr,hA,hB,hd,hCA,hCB⟩ :=
    abstract_sphere_bundle_boundary_components BoundaryPairingBundle
      (by norm_num) ho hc hr hs hn
  exact ⟨_,_,hfr,hA,hB,hd,hCA,hCB⟩
