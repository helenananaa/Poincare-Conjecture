import PoincareConjecture.ParallelImplementation.BarycentricSubdivisionRealization
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BarycentricLinkJoin
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open PoincareConjecture.ParallelImplementation.BarycentricSubdivisionRealization
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev LowerFace {K : FiniteAbstractComplex V} (s : Face K) :=
  {t : Finset V // t.Nonempty ∧ t ⊂ s.val}
abbrev UpperLinkFace (K : FiniteAbstractComplex V) (s : Face K) :=
  {t : Finset V // t.Nonempty ∧ Disjoint t s.val ∧ t ∪ s.val ∈ K.faces}
abbrev LinkVertex (K : FiniteAbstractComplex V) (s : Face K) :=
  {t : Face K // t ≠ s ∧ (t.val ⊆ s.val ∨ s.val ⊆ t.val)}
def joinComparable {K : FiniteAbstractComplex V} {s : Face K}
    (a b : LowerFace s ⊕ UpperLinkFace K s) : Prop :=
  match a,b with
  | .inl u,.inl v => u.val ⊆ v.val ∨ v.val ⊆ u.val
  | .inr u,.inr v => u.val ⊆ v.val ∨ v.val ⊆ u.val
  | _,_ => True
/-- Genuine combinatorial link decomposition: lower faces form the subdivided
boundary, upper faces map by difference to the subdivided ORIGINAL link.
The exact vertex reconstruction and chain correspondence are retained. -/
theorem barycentric_link_join_equivalence (K : FiniteAbstractComplex V) (s : Face K) :
    ∃ e : LinkVertex K s ≃ (LowerFace s ⊕ UpperLinkFace K s),
      (∀ q, (match e q with | .inl t => t.val | .inr t => t.val ∪ s.val) = q.val.val) ∧
      (∀ q r, (q.val.val ⊆ r.val.val ∨ r.val.val ⊆ q.val.val) ↔
        joinComparable (e q) (e r)) ∧
      (∀ c : Finset (LinkVertex K s),
        c.image (fun q => q.val) ∈
          (abstractLink (barycentricSubdivision K) {s}
            ((barycentricSubdivision K).singleton_mem s)).faces ↔
        c.Nonempty ∧ ∀ a ∈ c, ∀ b ∈ c, joinComparable (e a) (e b)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let toFun : LinkVertex K s → LowerFace s ⊕ UpperLinkFace K s := fun q =>
    if h : q.val.val ⊆ s.val then
      Sum.inl ⟨q.val.val, ⟨(K.isRelLowerSet_faces q.val.property).1,
        Finset.ssubset_iff_subset_ne.mpr ⟨h, by
          intro he
          apply q.property.1
          exact Subtype.ext he⟩⟩⟩
    else
      let hs : s.val ⊆ q.val.val := q.property.2.resolve_left h
      let d := q.val.val \ s.val
      Sum.inr ⟨d, ⟨by
        by_contra hne
        have he : d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        have hsub : q.val.val ⊆ s.val := by
          intro x hx
          by_contra hxs
          have hx' : x ∈ d := Finset.mem_sdiff.mpr ⟨hx, hxs⟩
          rw [he] at hx'
          simp at hx'
        apply q.property.1
        exact Subtype.ext (Finset.Subset.antisymm hsub hs),
        Finset.disjoint_left.mpr (by
          intro x hx hxS
          exact (Finset.mem_sdiff.mp hx).2 hxS),
        by
          have hu : d ∪ s.val = q.val.val := by
            ext x
            simp only [Finset.mem_union]
            constructor
            · rintro (hx | hx)
              · exact (Finset.mem_sdiff.mp hx).1
              · exact hs hx
            · intro hx
              by_cases hxS : x ∈ s.val
              · exact Or.inr hxS
              · exact Or.inl (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
          rw [hu]
          exact q.val.property⟩⟩
  let fromFun : LowerFace s ⊕ UpperLinkFace K s → LinkVertex K s := fun a =>
    match a with
    | Sum.inl u =>
        let hf : u.val ∈ K.faces :=
          (K.isRelLowerSet_faces s.property).2 u.property.2.1 u.property.1
        ⟨⟨u.val, hf⟩, by
          constructor
          · intro he
            apply u.property.2.2
            have hv : u.val = s.val := congrArg (fun f : Face K => f.val) he
            simp [hv]
          · exact Or.inl u.property.2.1⟩
    | Sum.inr u =>
        ⟨⟨u.val ∪ s.val, u.property.2.2⟩, by
          constructor
          · intro he
            obtain ⟨x, hx⟩ := u.property.1
            have hxS : x ∈ s.val := by
              have hxu : x ∈ u.val ∪ s.val := Finset.mem_union.mpr (Or.inl hx)
              have hvals : u.val ∪ s.val = s.val :=
                congrArg (fun f : Face K => f.val) he
              change x ∈ u.val ∪ s.val at hxu
              rw [hvals] at hxu
              exact hxu
            exact (Finset.disjoint_left.mp u.property.2.1) hx hxS
          · exact Or.inr (Finset.subset_union_right)⟩
  have left_inv : ∀ q : LinkVertex K s, fromFun (toFun q) = q := by
    intro q
    by_cases h : q.val.val ⊆ s.val
    · simp only [toFun, dif_pos h, fromFun]
    · simp only [toFun, dif_neg h, fromFun]
      apply Subtype.ext
      apply Subtype.ext
      dsimp
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (⟨hx, _⟩ | hx)
        · exact hx
        · exact (q.property.2.resolve_left h) hx
      · intro hx
        by_cases hxS : x ∈ s.val
        · exact Or.inr hxS
        · exact Or.inl ⟨hx, hxS⟩
  have right_inv : ∀ a : LowerFace s ⊕ UpperLinkFace K s, toFun (fromFun a) = a := by
    intro a
    cases a with
    | inl u =>
        have hs : u.val ⊆ s.val := u.property.2.1
        simp only [fromFun, toFun, dif_pos hs]
    | inr u =>
        have hnot : ¬ u.val ∪ s.val ⊆ s.val := by
          intro hsub
          obtain ⟨x, hx⟩ := u.property.1
          have hxS : x ∈ s.val := hsub (Finset.mem_union.mpr (Or.inl hx))
          exact (Finset.disjoint_left.mp u.property.2.1) hx hxS
        have hdiff : (u.val ∪ s.val) \ s.val = u.val := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hx | hx, hnotx⟩
            · exact hx
            · exact False.elim (hnotx hx)
          · intro hx
            exact ⟨Or.inl hx, (Finset.disjoint_left.mp u.property.2.1) hx⟩
        simp only [fromFun, toFun, dif_neg hnot]
        congr 1
        apply Subtype.ext
        exact hdiff
  let e : LinkVertex K s ≃ (LowerFace s ⊕ UpperLinkFace K s) :=
    ⟨toFun, fromFun, left_inv, right_inv⟩
  have reconstruct (q : LinkVertex K s) :
      (match e q with
       | Sum.inl t => t.val
       | Sum.inr t => t.val ∪ s.val) = q.val.val := by
    cases hq : e q with
    | inl t =>
        have hi : fromFun (Sum.inl t) = q := by
          have hh := left_inv q
          change fromFun (e q) = q at hh
          rw [hq] at hh
          exact hh
        simpa [hq, fromFun] using
          congrArg (fun z : LinkVertex K s => z.val.val) hi
    | inr t =>
        have hi : fromFun (Sum.inr t) = q := by
          have hh := left_inv q
          change fromFun (e q) = q at hh
          rw [hq] at hh
          exact hh
        simpa [hq, fromFun] using
          congrArg (fun z : LinkVertex K s => z.val.val) hi
  have upperSubset (a b : UpperLinkFace K s) :
      (a.val ∪ s.val ⊆ b.val ∪ s.val) ↔ a.val ⊆ b.val := by
    constructor
    · intro h x hx
      have hmem := h (Finset.mem_union.mpr (Or.inl hx))
      rcases Finset.mem_union.mp hmem with hxb | hxs
      · exact hxb
      · exact False.elim ((Finset.disjoint_left.mp a.property.2.1) hx hxs)
    · intro h x hx
      rcases Finset.mem_union.mp hx with hxb | hxs
      · exact Finset.mem_union.mpr (Or.inl (h hxb))
      · exact Finset.mem_union.mpr (Or.inr hxs)
  have compare (q r : LinkVertex K s) :
      (q.val.val ⊆ r.val.val ∨ r.val.val ⊆ q.val.val) ↔
        joinComparable (e q) (e r) := by
    cases hq : e q with
    | inl a =>
      cases hr : e r with
      | inl b =>
        have hqv : q.val.val = a.val := by
          simpa [hq] using (reconstruct q).symm
        have hrv : r.val.val = b.val := by
          simpa [hr] using (reconstruct r).symm
        constructor
        · intro h
          have h' : a.val ⊆ b.val ∨ b.val ⊆ a.val := by
            simpa [hqv, hrv] using h
          simpa [joinComparable, hq, hr] using h'
        · intro h
          have h' : a.val ⊆ b.val ∨ b.val ⊆ a.val := by
            simpa [joinComparable, hq, hr] using h
          simpa [hqv, hrv] using h'
      | inr b =>
        have hqv : q.val.val = a.val := by
          simpa [hq] using (reconstruct q).symm
        have hrv : r.val.val = b.val ∪ s.val := by
          simpa [hr] using (reconstruct r).symm
        have hsub : q.val.val ⊆ r.val.val := by
          rw [hqv, hrv]
          exact Finset.Subset.trans a.property.2.1 Finset.subset_union_right
        constructor
        · intro _
          trivial
        · intro _
          exact Or.inl hsub
    | inr a =>
      cases hr : e r with
      | inl b =>
        have hqv : q.val.val = a.val ∪ s.val := by
          simpa [hq] using (reconstruct q).symm
        have hrv : r.val.val = b.val := by
          simpa [hr] using (reconstruct r).symm
        have hsub : r.val.val ⊆ q.val.val := by
          rw [hrv, hqv]
          exact Finset.Subset.trans b.property.2.1 Finset.subset_union_right
        constructor
        · intro _
          trivial
        · intro _
          exact Or.inr hsub
      | inr b =>
        have hqv : q.val.val = a.val ∪ s.val := by
          simpa [hq] using (reconstruct q).symm
        have hrv : r.val.val = b.val ∪ s.val := by
          simpa [hr] using (reconstruct r).symm
        constructor
        · intro h
          have h' : a.val ∪ s.val ⊆ b.val ∪ s.val ∨
              b.val ∪ s.val ⊆ a.val ∪ s.val := by
            simpa [hqv, hrv] using h
          have h'' : a.val ⊆ b.val ∨ b.val ⊆ a.val := by
            rcases h' with hab | hba
            · exact Or.inl (upperSubset a b |>.mp hab)
            · exact Or.inr (upperSubset b a |>.mp hba)
          simpa [joinComparable, hq, hr] using h''
        · intro h
          have h' : a.val ⊆ b.val ∨ b.val ⊆ a.val := by
            simpa [joinComparable, hq, hr] using h
          have h'' : a.val ∪ s.val ⊆ b.val ∪ s.val ∨
              b.val ∪ s.val ⊆ a.val ∪ s.val := by
            rcases h' with hab | hba
            · exact Or.inl (upperSubset a b |>.mpr hab)
            · exact Or.inr (upperSubset b a |>.mpr hba)
          simpa [hqv, hrv] using h''
  refine ⟨e, ?_, ?_, ?_⟩
  · intro q
    exact reconstruct q
  · intro q r
    exact compare q r
  · intro c
    classical
    let D := c.image (fun q : LinkVertex K s => q.val)
    change (D ∈ (abstractLink (barycentricSubdivision K) {s}
      ((barycentricSubdivision K).singleton_mem s)).faces) ↔
      (c.Nonempty ∧ ∀ a ∈ c, ∀ b ∈ c, joinComparable (e a) (e b))
    change (D.Nonempty ∧ Disjoint D ({s} : Finset (Face K)) ∧
      D ∪ {s} ∈ (barycentricSubdivision K).faces) ↔
      (c.Nonempty ∧ ∀ a ∈ c, ∀ b ∈ c, joinComparable (e a) (e b))
    constructor
    · rintro ⟨hDne, _, hchain⟩
      have hcne : c.Nonempty := Finset.image_nonempty.mp hDne
      have hDface : D ∈ (barycentricSubdivision K).faces :=
        ((barycentricSubdivision K).isRelLowerSet_faces hchain).2
          Finset.subset_union_left hDne
      refine ⟨hcne, ?_⟩
      intro q hq r hr
      have hqD : q.val ∈ D := Finset.mem_image.mpr ⟨q, hq, rfl⟩
      have hrD : r.val ∈ D := Finset.mem_image.mpr ⟨r, hr, rfl⟩
      exact (compare q r).mp (hDface.2 q.val hqD r.val hrD)
    · rintro ⟨hcne, hcomp⟩
      have hDne : D.Nonempty := Finset.image_nonempty.mpr hcne
      have hDchain : D ∈ (barycentricSubdivision K).faces := by
        refine ⟨hDne, ?_⟩
        intro a ha b hb
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hb
        exact (compare q r).mpr (hcomp q hq r hr)
      have hDs : ∀ a ∈ D, a.val ⊆ s.val ∨ s.val ⊆ a.val := by
        intro a ha
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
        exact q.property.2
      have hunion : D ∪ {s} ∈ (barycentricSubdivision K).faces := by
        refine ⟨by simp, ?_⟩
        intro a ha b hb
        rcases Finset.mem_union.mp ha with haD | haS
        · rcases Finset.mem_union.mp hb with hbD | hbS
          · exact hDchain.2 a haD b hbD
          · have hb' : b = s := Finset.mem_singleton.mp hbS
            subst b
            exact hDs a haD
        · rcases Finset.mem_union.mp hb with hbD | hbS
          · have ha' : a = s := Finset.mem_singleton.mp haS
            subst a
            rcases hDs b hbD with hbs | hsb
            · exact Or.inr hbs
            · exact Or.inl hsb
          · have ha' : a = s := Finset.mem_singleton.mp haS
            have hb' : b = s := Finset.mem_singleton.mp hbS
            subst a
            subst b
            exact Or.inl (Finset.Subset.refl _)
      refine ⟨hDne, ?_, hunion⟩
      apply Finset.disjoint_left.mpr
      intro a ha hs'
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
      have : q.val = s := Finset.mem_singleton.mp hs'
      exact q.property.1 this
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BarycentricLinkJoin
