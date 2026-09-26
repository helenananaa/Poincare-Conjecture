import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CappedSpaceTopology
open Set
local notation "E3" => EuclideanSpace ℝ (Fin 3)
abbrev Sphere := Metric.sphere (0 : E3) 1
abbrev Ball := Metric.closedBall (0 : E3) 1
def boundary (s : Sphere) : Ball :=
  ⟨s.1, by simpa only [Metric.mem_closedBall, Metric.mem_sphere] using s.2.le⟩
def capSeam {C : Type*} (b : Sphere → C) (x y : C ⊕ Ball) : Prop :=
  ∃ s : Sphere, x = Sum.inl (b s) ∧ y = Sum.inr (boundary s)
abbrev CappedSpace {C : Type*} (b : Sphere → C) := Quot (capSeam b)
def interiorPoint (x : Metric.ball (0 : E3) 1) : Ball :=
  ⟨x.1, Metric.ball_subset_closedBall x.2⟩
/-- Topology of the ACTUAL ball cap quotient, glued only on its boundary.
Manifold charts across the seam are a separate, still necessary obligation. -/
theorem actual_cap_quotient_topology
    {C : Type*} [TopologicalSpace C] [CompactSpace C] [T2Space C]
    (b : Sphere → C) (hb : Topology.IsEmbedding b) :
    CompactSpace (CappedSpace b) ∧ T2Space (CappedSpace b) ∧
    Topology.IsClosedEmbedding (fun x : C => Quot.mk (capSeam b) (Sum.inl x)) ∧
    Topology.IsOpenEmbedding (fun x : Metric.ball (0 : E3) 1 =>
      Quot.mk (capSeam b) (Sum.inr (interiorPoint x))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : CompactSpace Ball := isCompact_iff_compactSpace.mp
    (isCompact_closedBall (0 : E3) 1)
  letI : CompactSpace Sphere := isCompact_iff_compactSpace.mp
    (isCompact_sphere (0 : E3) 1)
  let X := C ⊕ Ball
  letI : CompactSpace X := inferInstance
  letI : T2Space X := inferInstance
  have hboundary_inj : Function.Injective boundary := by
    intro s t h
    apply Subtype.ext
    have hv := congrArg (fun z : Ball => (z : E3)) h
    simpa [boundary] using hv
  let R : X → X → Prop := fun p q =>
    p = q ∨
      (∃ s : Sphere, p = Sum.inl (b s) ∧ q = Sum.inr (boundary s)) ∨
      (∃ s : Sphere, p = Sum.inr (boundary s) ∧ q = Sum.inl (b s))
  have hR_equiv : Equivalence R := by
    refine ⟨?_, ?_, ?_⟩
    · intro p
      exact Or.inl rfl
    · intro p q hpq
      rcases hpq with hpq | ⟨s, hp, hq⟩ | ⟨s, hp, hq⟩
      · exact Or.inl hpq.symm
      · exact Or.inr (Or.inr ⟨s, hq, hp⟩)
      · exact Or.inr (Or.inl ⟨s, hq, hp⟩)
    · intro p q r hpq hqr
      rcases hpq with hpq | ⟨s, hp, hq⟩ | ⟨s, hp, hq⟩
      · cases hpq
        exact hqr
      · rcases hqr with hqr | ⟨t, hp', hq'⟩ | ⟨t, hp', hq'⟩
        · cases hqr
          exact Or.inr (Or.inl ⟨s, hp, hq⟩)
        · cases hq.symm.trans hp'
        · have hst' : boundary s = boundary t :=
            Sum.inr.inj (hq.symm.trans hp')
          have hst : s = t := hboundary_inj hst'
          subst t
          exact Or.inl (hp.trans hq'.symm)
      · rcases hqr with hqr | ⟨t, hp', hq'⟩ | ⟨t, hp', hq'⟩
        · cases hqr
          exact Or.inr (Or.inr ⟨s, hp, hq⟩)
        · have hst' : b s = b t := Sum.inl.inj (hq.symm.trans hp')
          have hst : s = t := hb.injective hst'
          subst t
          exact Or.inl (hp.trans hq'.symm)
        · cases hq.symm.trans hp'
  have hseam_R : ∀ p q, capSeam b p q → R p q := by
    intro p q hpq
    rcases hpq with ⟨s, hp, hq⟩
    exact Or.inr (Or.inl ⟨s, hp, hq⟩)
  have hgen : ∀ p q, Relation.EqvGen (capSeam b) p q ↔ R p q := by
    intro p q
    constructor
    · intro hpq
      induction hpq with
      | rel x y hxy => exact hseam_R x y hxy
      | refl x => exact Or.inl rfl
      | symm x y hxy ih => exact hR_equiv.symm ih
      | trans x y z hxy hyz ihxy ihyz => exact hR_equiv.trans ihxy ihyz
    · intro hpq
      rcases hpq with hpq | ⟨s, hp, hq⟩ | ⟨s, hp, hq⟩
      · cases hpq
        exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ ⟨s, hp, hq⟩
      · exact Relation.EqvGen.symm _ _
          (Relation.EqvGen.rel _ _ ⟨s, hq, hp⟩)
  have hquot : ∀ p q, Quot.mk (capSeam b) p = Quot.mk (capSeam b) q ↔ R p q := by
    intro p q
    constructor
    · intro hpq
      exact (hgen p q).mp (Quot.eqvGen_exact hpq)
    · intro hpq
      exact Quot.eqvGen_sound ((hgen p q).mpr hpq)
  have hboundary_cont : Continuous boundary := by
    exact continuous_subtype_val.subtype_mk (fun s : Sphere => by
      simpa only [Metric.mem_closedBall, Metric.mem_sphere] using s.2.le)
  let seamGraph : Sphere → X × X := fun s =>
    (Sum.inl (b s), Sum.inr (boundary s))
  let seamGraphRev : Sphere → X × X := fun s =>
    (Sum.inr (boundary s), Sum.inl (b s))
  have hseamGraph_cont : Continuous seamGraph := by
    exact (continuous_inl.comp hb.continuous).prodMk
      (continuous_inr.comp hboundary_cont)
  have hseamGraphRev_cont : Continuous seamGraphRev := by
    exact (continuous_inr.comp hboundary_cont).prodMk
      (continuous_inl.comp hb.continuous)
  have hR_closed : IsClosed {p : X × X | R p.1 p.2} := by
    have hdiag : IsClosed {p : X × X | p.1 = p.2} :=
      isClosed_eq continuous_fst continuous_snd
    have hgraph : IsClosed (Set.range seamGraph) :=
      (isCompact_range hseamGraph_cont).isClosed
    have hgraphRev : IsClosed (Set.range seamGraphRev) :=
      (isCompact_range hseamGraphRev_cont).isClosed
    have hset : {p : X × X | R p.1 p.2} =
        {p | p.1 = p.2} ∪ (Set.range seamGraph ∪ Set.range seamGraphRev) := by
      ext ⟨x, y⟩
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_range, R]
      constructor
      · rintro (hxy | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩)
        · exact Or.inl hxy
        · exact Or.inr (Or.inl ⟨s, Prod.ext hx.symm hy.symm⟩)
        · exact Or.inr (Or.inr ⟨s, Prod.ext hx.symm hy.symm⟩)
      · rintro (hxy | ⟨s, hs⟩ | ⟨s, hs⟩)
        · exact Or.inl hxy
        · exact Or.inr (Or.inl ⟨s, by simpa [seamGraph] using (congrArg Prod.fst hs).symm,
            by simpa [seamGraph] using (congrArg Prod.snd hs).symm⟩)
        · exact Or.inr (Or.inr ⟨s, by simpa [seamGraphRev] using (congrArg Prod.fst hs).symm,
            by simpa [seamGraphRev] using (congrArg Prod.snd hs).symm⟩)
    rw [hset]
    exact hdiag.union (hgraph.union hgraphRev)
  let q : X → CappedSpace b := Quot.mk (capSeam b)
  have hqmap : Topology.IsQuotientMap q := isQuotientMap_quot_mk
  have hquot_t2 : T2Space (CappedSpace b) := by
    refine ⟨?_⟩
    intro qx qy hne
    revert hne
    refine Quot.inductionOn qx ?_
    intro x
    refine Quot.inductionOn qy ?_
    intro y hne
    have hnotxy : ¬ R x y := by
      intro hxy
      apply hne
      exact (hquot x y).2 hxy
    let A : Set X := {z | R x z}
    let B : Set X := {z | R y z}
    have hAclosed : IsClosed A := by
      exact hR_closed.preimage (continuous_const.prodMk continuous_id)
    have hBclosed : IsClosed B := by
      exact hR_closed.preimage (continuous_const.prodMk continuous_id)
    have hAcompact : IsCompact A := hAclosed.isCompact
    have hBcompact : IsCompact B := hBclosed.isCompact
    have hAB : A ×ˢ B ⊆ {p : X × X | R p.1 p.2}ᶜ := by
      rintro ⟨a, c⟩ ⟨hxa, hyc⟩ hac
      exact hnotxy (hR_equiv.trans (hR_equiv.trans hxa hac) (hR_equiv.symm hyc))
    obtain ⟨U, V, hUopen, hVopen, hAU, hBV, hUV⟩ :=
      generalized_tube_lemma hAcompact hBcompact hR_closed.isOpen_compl hAB
    let Ucore : Set X := {z | ∀ w, R z w → w ∈ U}
    let Vcore : Set X := {z | ∀ w, R z w → w ∈ V}
    have hUcore_sub : Ucore ⊆ U := by
      intro z hz
      exact hz z (hR_equiv.refl z)
    have hVcore_sub : Vcore ⊆ V := by
      intro z hz
      exact hz z (hR_equiv.refl z)
    have hUcore_sat : ∀ z z', R z z' → (z ∈ Ucore ↔ z' ∈ Ucore) := by
      intro z z' hzz'
      constructor
      · intro hz w hzw
        exact hz w (hR_equiv.trans hzz' hzw)
      · intro hz w hzw
        exact hz w (hR_equiv.trans (hR_equiv.symm hzz') hzw)
    have hVcore_sat : ∀ z z', R z z' → (z ∈ Vcore ↔ z' ∈ Vcore) := by
      intro z z' hzz'
      constructor
      · intro hz w hzw
        exact hz w (hR_equiv.trans hzz' hzw)
      · intro hz w hzw
        exact hz w (hR_equiv.trans (hR_equiv.symm hzz') hzw)
    have hUcore_open : IsOpen Ucore := by
      have hUc : IsClosed Uᶜ := hUopen.isClosed_compl
      let bad : Set X := {z | ∃ w, R z w ∧ w ∉ U}
      let S : Set (X × X) := {p | R p.1 p.2} ∩ (Set.univ ×ˢ Uᶜ)
      have hScompact : IsCompact S :=
        hR_closed.isCompact.inter_right (isClosed_univ.prod hUc)
      have hbad_eq : bad = Prod.fst '' S := by
        ext z
        constructor
        · rintro ⟨w, hzw, hnot⟩
          exact ⟨(z, w), ⟨hzw, by simpa using hnot⟩, rfl⟩
        · rintro ⟨⟨z', w⟩, ⟨hzw, hnot⟩, hz⟩
          cases hz
          exact ⟨w, hzw, by simpa using hnot⟩
      have hbad_closed : IsClosed bad := by
        rw [hbad_eq]
        exact (hScompact.image continuous_fst).isClosed
      change IsOpen ({z | ∀ w, R z w → w ∈ U})
      rw [show ({z | ∀ w, R z w → w ∈ U} : Set X) = badᶜ by
        ext z
        simp [bad]
      ]
      exact hbad_closed.isOpen_compl
    have hVcore_open : IsOpen Vcore := by
      have hVc : IsClosed Vᶜ := hVopen.isClosed_compl
      let bad : Set X := {z | ∃ w, R z w ∧ w ∉ V}
      let S : Set (X × X) := {p | R p.1 p.2} ∩ (Set.univ ×ˢ Vᶜ)
      have hScompact : IsCompact S :=
        hR_closed.isCompact.inter_right (isClosed_univ.prod hVc)
      have hbad_eq : bad = Prod.fst '' S := by
        ext z
        constructor
        · rintro ⟨w, hzw, hnot⟩
          exact ⟨(z, w), ⟨hzw, by simpa using hnot⟩, rfl⟩
        · rintro ⟨⟨z', w⟩, ⟨hzw, hnot⟩, hz⟩
          cases hz
          exact ⟨w, hzw, by simpa using hnot⟩
      have hbad_closed : IsClosed bad := by
        rw [hbad_eq]
        exact (hScompact.image continuous_fst).isClosed
      change IsOpen ({z | ∀ w, R z w → w ∈ V})
      rw [show ({z | ∀ w, R z w → w ∈ V} : Set X) = badᶜ by
        ext z
        simp [bad]
      ]
      exact hbad_closed.isOpen_compl
    have hUpre : q ⁻¹' (q '' Ucore) = Ucore := by
      ext z
      constructor
      · rintro ⟨w, hw, hzw⟩
        exact (hUcore_sat z w ((hquot z w).mp hzw.symm)).mpr hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    have hVpre : q ⁻¹' (q '' Vcore) = Vcore := by
      ext z
      constructor
      · rintro ⟨w, hw, hzw⟩
        exact (hVcore_sat z w ((hquot z w).mp hzw.symm)).mpr hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    have hqUopen : IsOpen (q '' Ucore) := by
      apply hqmap.isOpen_preimage.mp
      rw [hUpre]
      exact hUcore_open
    have hqVopen : IsOpen (q '' Vcore) := by
      apply hqmap.isOpen_preimage.mp
      rw [hVpre]
      exact hVcore_open
    have hxUcore : x ∈ Ucore := by
      intro z hxz
      exact hAU hxz
    have hyVcore : y ∈ Vcore := by
      intro z hyz
      exact hBV hyz
    have hqUV : Disjoint (q '' Ucore) (q '' Vcore) := by
      apply Set.disjoint_left.mpr
      intro z hzu hzv
      rcases hzu with ⟨u, hu, rfl⟩
      rcases hzv with ⟨v, hv, huv⟩
      have huvR : R u v := (hquot u v).mp huv.symm
      have hUVnot := hUV (show (u, v) ∈ U ×ˢ V from
        ⟨hUcore_sub hu, hVcore_sub hv⟩)
      exact hUVnot huvR
    exact ⟨q '' Ucore, q '' Vcore, hqUopen, hqVopen,
      ⟨x, hxUcore, rfl⟩, ⟨y, hyVcore, rfl⟩, hqUV⟩
  letI : T2Space (CappedSpace b) := hquot_t2
  have hCmap_cont : Continuous (fun x : C => q (Sum.inl x)) :=
    continuous_quot_mk.comp continuous_inl
  have hCmap_inj : Function.Injective (fun x : C => q (Sum.inl x)) := by
    intro x y hxy
    rcases (hquot (Sum.inl x) (Sum.inl y)).mp hxy with hxy | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
    · exact Sum.inl.inj hxy
    · cases hy
    · cases hx
  have hCclosed : Topology.IsClosedEmbedding (fun x : C => q (Sum.inl x)) :=
    hCmap_cont.isClosedEmbedding hCmap_inj
  have hBallmap_inj : Function.Injective (fun y : Ball => q (Sum.inr y)) := by
    intro y z hyz
    rcases (hquot (Sum.inr y) (Sum.inr z)).mp hyz with hyz | ⟨s, hy, hz⟩ | ⟨s, hy, hz⟩
    · exact Sum.inr.inj hyz
    · cases hy
    · cases hz
  have hInteriorOpen : IsOpen (Metric.ball (0 : E3) 1) := Metric.isOpen_ball
  have hInteriorEmbedding : Topology.IsOpenEmbedding interiorPoint := by
    apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    · exact continuous_subtype_val.subtype_mk (fun x => Metric.ball_subset_closedBall x.2)
    · intro x y hxy
      apply Subtype.ext
      exact congrArg (fun z : Ball => (z : E3)) hxy
    · intro s hs
      have hsource : IsOpen ((Subtype.val : Metric.ball (0 : E3) 1 → E3) '' s) :=
        hInteriorOpen.isOpenEmbedding_subtypeVal.isOpenMap _ hs
      have himage : interiorPoint '' s =
          (Subtype.val : Ball → E3) ⁻¹' ((Subtype.val : Metric.ball (0 : E3) 1 → E3) '' s) := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, hz⟩
          exact ⟨x, hx, by apply Subtype.ext; exact hz⟩
      rw [himage]
      exact hsource.preimage continuous_subtype_val
  have hInterior_cont : Continuous (fun x : Metric.ball (0 : E3) 1 =>
      q (Sum.inr (interiorPoint x))) := by
    exact continuous_quot_mk.comp (continuous_inr.comp hInteriorEmbedding.continuous)
  have hInterior_inj : Function.Injective (fun x : Metric.ball (0 : E3) 1 =>
      q (Sum.inr (interiorPoint x))) := by
    intro x y hxy
    rcases (hquot (Sum.inr (interiorPoint x)) (Sum.inr (interiorPoint y))).mp hxy with
      hxy | ⟨s, hx, hy⟩ | ⟨s, hx, hy⟩
    · apply Subtype.ext
      exact congrArg (fun z : Ball => (z : E3)) (Sum.inr.inj hxy)
    · cases hx
    · cases hy
  have hInterior_openMap : IsOpenMap (fun x : Metric.ball (0 : E3) 1 =>
      q (Sum.inr (interiorPoint x))) := by
    intro s hs
    let U : Set X := Sum.inr '' (interiorPoint '' s)
    have hUopen : IsOpen U := isOpenMap_inr _ (hInteriorEmbedding.isOpenMap _ hs)
    have hUpre : q ⁻¹' (q '' U) = U := by
      ext z
      constructor
      · rintro ⟨w, hw, hzw⟩
        rcases hw with ⟨v, ⟨x, hx, rfl⟩, rfl⟩
        have hzv : R z (Sum.inr (interiorPoint x)) := (hquot z (Sum.inr (interiorPoint x))).mp hzw.symm
        rcases hzv with hEq | ⟨s, hleft, hright⟩ | ⟨s, hleft, hright⟩
        · exact ⟨interiorPoint x, ⟨x, hx, rfl⟩, by cases hEq; rfl⟩
        · have hval : interiorPoint x = boundary s := Sum.inr.inj hright
          have hxlt : ‖(x : E3)‖ < (1 : ℝ) := by
            simpa only [Metric.mem_ball, dist_eq_norm, sub_zero] using x.2
          have hseq : ‖(s : E3)‖ = (1 : ℝ) := by
            simpa [Metric.mem_sphere, dist_eq_norm] using s.2
          have hdist := congrArg (fun z : E3 => ‖z‖)
            (congrArg (fun z : Ball => (z : E3)) hval)
          have : ‖(x : E3)‖ = ‖(s : E3)‖ := by
            simp [interiorPoint, boundary] at hdist ⊢
            exact hdist
          linarith
        · have : Sum.inr (interiorPoint x) = Sum.inl (b s) := hright
          cases this
      · intro hz
        exact ⟨z, hz, rfl⟩
    have hqUopen : IsOpen (q '' U) := by
      apply hqmap.isOpen_preimage.mp
      rw [hUpre]
      exact hUopen
    have hImage : (fun x : Metric.ball (0 : E3) 1 =>
        q (Sum.inr (interiorPoint x))) '' s = q '' U := by
      simp [U, Set.image_image]
    rw [hImage]
    exact hqUopen
  have hInteriorEmbeddingQuot : Topology.IsOpenEmbedding
      (fun x : Metric.ball (0 : E3) 1 => q (Sum.inr (interiorPoint x))) :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
      hInterior_cont hInterior_inj hInterior_openMap
  exact ⟨inferInstance, hquot_t2, hCclosed, hInteriorEmbeddingQuot⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CappedSpaceTopology
