import PoincareConjecture.ProofContract.Refinement20260927.Cap
import PoincareConjecture.ParallelImplementation.CapSeamOpenCollar
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCapComplement
open PoincareConjecture.ProofContract.Refinement20260927
theorem cap_complement : CapComplementStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro c
  letI : TopologicalSpace c.carrier := c.topology
  letI : CompactSpace c.carrier := c.compact
  letI : T2Space c.carrier := c.hausdorff
  let X := c.carrier ⊕ CappedSpaceTopology.Ball
  let q : X → CappedSpaceTopology.CappedSpace c.boundaryMap :=
    Quot.mk (CappedSpaceTopology.capSeam c.boundaryMap)
  let f : c.carrier → CappedSpaceTopology.CappedSpace c.boundaryMap :=
    fun x => q (Sum.inl x)
  let g : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 →
      CappedSpaceTopology.CappedSpace c.boundaryMap := capInterior c
  have hboundary_inj : Function.Injective CappedSpaceTopology.boundary := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun z : CappedSpaceTopology.Ball => (z : EuclideanSpace ℝ (Fin 3))) h
  have hb_inj : Function.Injective c.boundaryMap := c.boundaryEmbedding.injective
  let R : X → X → Prop := fun p r =>
    p = r ∨
      (∃ s : CappedSpaceTopology.Sphere,
        p = Sum.inl (c.boundaryMap s) ∧ r = Sum.inr (CappedSpaceTopology.boundary s)) ∨
      (∃ s : CappedSpaceTopology.Sphere,
        p = Sum.inr (CappedSpaceTopology.boundary s) ∧ r = Sum.inl (c.boundaryMap s))
  have hR_equiv : Equivalence R := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact Or.inl rfl
    · intro p r hpr
      rcases hpr with hpr | ⟨s, hp, hr⟩ | ⟨s, hp, hr⟩
      · exact Or.inl hpr.symm
      · exact Or.inr (Or.inr ⟨s, hr, hp⟩)
      · exact Or.inr (Or.inl ⟨s, hr, hp⟩)
    · intro p r v hpr hrv
      rcases hpr with hpr | ⟨s, hp, hr⟩ | ⟨s, hp, hr⟩
      · cases hpr
        exact hrv
      · rcases hrv with hrv | ⟨t, hr', hv'⟩ | ⟨t, hr', hv'⟩
        · cases hrv
          exact Or.inr (Or.inl ⟨s, hp, hr⟩)
        · cases hr.symm.trans hr'
        · have hst' : CappedSpaceTopology.boundary s = CappedSpaceTopology.boundary t :=
            Sum.inr.inj (hr.symm.trans hr')
          have hst : s = t := hboundary_inj hst'
          subst t
          exact Or.inl (hp.trans hv'.symm)
      · rcases hrv with hrv | ⟨t, hr', hv'⟩ | ⟨t, hr', hv'⟩
        · cases hrv
          exact Or.inr (Or.inr ⟨s, hp, hr⟩)
        · have hst' : c.boundaryMap s = c.boundaryMap t :=
            Sum.inl.inj (hr.symm.trans hr')
          have hst : s = t := hb_inj hst'
          subst t
          exact Or.inl (hp.trans hv'.symm)
        · cases hr.symm.trans hr'
  have hseam_R : ∀ p r, CappedSpaceTopology.capSeam c.boundaryMap p r → R p r := by
    intro p r hpr
    rcases hpr with ⟨s, hp, hr⟩
    exact Or.inr (Or.inl ⟨s, hp, hr⟩)
  have hgen : ∀ p r, Relation.EqvGen (CappedSpaceTopology.capSeam c.boundaryMap) p r ↔ R p r := by
    intro p r
    constructor
    · intro hpr
      induction hpr with
      | rel x y hxy => exact hseam_R x y hxy
      | refl x => exact Or.inl rfl
      | symm x y hxy ih => exact hR_equiv.symm ih
      | trans x y z hxy hyz ihxy ihyz => exact hR_equiv.trans ihxy ihyz
    · intro hpr
      rcases hpr with hpr | ⟨s, hp, hr⟩ | ⟨s, hp, hr⟩
      · cases hpr
        exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ ⟨s, hp, hr⟩
      · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨s, hr, hp⟩)
  have hquot : ∀ p r, q p = q r ↔ R p r := by
    intro p r
    constructor
    · intro hpr
      exact (hgen p r).mp (Quot.eqvGen_exact hpr)
    · intro hpr
      exact Quot.eqvGen_sound ((hgen p r).mpr hpr)
  have htop := CappedSpaceTopology.actual_cap_quotient_topology
    c.boundaryMap c.boundaryEmbedding
  rcases htop with ⟨_, _, hfclosed, _⟩
  have hrange : Set.range f = (Set.range g)ᶜ := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      simp only [Set.mem_compl_iff, Set.mem_range]
      rintro ⟨y, hy⟩
      have hxy : R (Sum.inl x) (Sum.inr (CappedSpaceTopology.interiorPoint y)) :=
        (hquot _ _).mp hy.symm
      rcases hxy with hxy | ⟨s, hleft, hright⟩ | ⟨s, hleft, hright⟩
      · cases hxy
      · have hnormeq : ‖(y : EuclideanSpace ℝ (Fin 3))‖ = ‖(s : EuclideanSpace ℝ (Fin 3))‖ := by
          have hval := congrArg (fun v : CappedSpaceTopology.Ball => ‖(v : EuclideanSpace ℝ (Fin 3))‖)
            (Sum.inr.inj hright)
          simpa [CappedSpaceTopology.interiorPoint, CappedSpaceTopology.boundary] using hval
        have hlt : ‖(y : EuclideanSpace ℝ (Fin 3))‖ < (1 : ℝ) := by
          simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using y.2
        have hs : ‖(s : EuclideanSpace ℝ (Fin 3))‖ = (1 : ℝ) := by
          simpa [CappedSpaceTopology.Sphere, Metric.mem_sphere, dist_zero_right] using s.2
        linarith
      · have hsum : Sum.inl x = (Sum.inr (CappedSpaceTopology.boundary s) : X) := hleft
        cases hsum
    · intro hz
      refine Quot.inductionOn z ?_ hz
      intro p hp
      cases p with
      | inl x =>
          exact ⟨x, rfl⟩
      | inr y =>
          have hnotlt : ¬ ‖(y : EuclideanSpace ℝ (Fin 3))‖ < (1 : ℝ) := by
            intro hlt
            let x : Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
              ⟨y, by simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using hlt⟩
            have hpoint : CappedSpaceTopology.interiorPoint x = y := by
              apply Subtype.ext
              rfl
            apply hp
            refine ⟨x, ?_⟩
            change q (Sum.inr (CappedSpaceTopology.interiorPoint x)) = q (Sum.inr y)
            rw [hpoint]
          have hyclosed : ‖(y : EuclideanSpace ℝ (Fin 3))‖ ≤ 1 := by
            simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using y.2
          have hnorm : ‖(y : EuclideanSpace ℝ (Fin 3))‖ = (1 : ℝ) := by
            exact le_antisymm hyclosed (le_of_not_gt hnotlt)
          let s : CappedSpaceTopology.Sphere := ⟨(y : EuclideanSpace ℝ (Fin 3)), by
            simpa [CappedSpaceTopology.Sphere, Metric.mem_sphere, dist_zero_right] using hnorm⟩
          have hboundary : CappedSpaceTopology.boundary s = y := by
            apply Subtype.ext
            rfl
          have hclass : q (Sum.inr y) = f (c.boundaryMap s) := by
            apply (hquot _ _).2
            exact Or.inr (Or.inr ⟨s, by simpa [hboundary], rfl⟩)
          exact ⟨c.boundaryMap s, hclass.symm⟩
  let H : c.carrier ≃ₜ {z : CappedSpaceTopology.CappedSpace c.boundaryMap // z ∉ Set.range g} :=
    hfclosed.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
  refine ⟨H, ?_⟩
  intro x
  change ((Homeomorph.setCongr hrange (hfclosed.isEmbedding.toHomeomorph x) :
      {z : CappedSpaceTopology.CappedSpace c.boundaryMap // z ∉ Set.range g}) :
      CappedSpaceTopology.CappedSpace c.boundaryMap) =
    Quot.mk (CappedSpaceTopology.capSeam c.boundaryMap) (Sum.inl x)
  have hval :
      ((Homeomorph.setCongr hrange (hfclosed.isEmbedding.toHomeomorph x) :
        {z : CappedSpaceTopology.CappedSpace c.boundaryMap // z ∉ Set.range g}) :
        CappedSpaceTopology.CappedSpace c.boundaryMap) =
      (hfclosed.isEmbedding.toHomeomorph x : Set.range f) := rfl
  rw [hval, Topology.IsEmbedding.toHomeomorph_apply_coe]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCapComplement
