import PoincareConjecture.ProofContract.Refinement20260927.SurgeryProjection
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedFiniteTimeline
open PoincareConjecture.ProofContract.Refinement20260927
theorem finite_timeline : FiniteTimelineStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro X R pre post a b hab E hE hEsub hjump hinterval
  have chain : ∀ (l : List ℝ) (a b : ℝ) (E : Set ℝ),
      a < b → E.Finite → E ⊆ Set.Ioo a b →
      List.Pairwise (· ≤ ·) l → l.Nodup →
      (∀ x, x ∈ l → x ∈ E) → (∀ x, x ∈ E → x ∈ l) →
      (∀ t, t ∈ E → Relation.ReflTransGen R (pre t) (post t)) →
      (∀ s t, a ≤ s → s < t → t ≤ b → (E ∩ Set.Ioo s t = ∅) →
        Relation.ReflTransGen R (post s) (pre t)) →
      Relation.ReflTransGen R (post a) (pre b) := by
    intro l
    induction l with
    | nil =>
        intro a b E hab hE hEsub hsorted hnodup hlistE hElist hjump hinterval
        have hempty : E ∩ Set.Ioo a b = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hxE, hax, hxb⟩
          have : x ∈ ([] : List ℝ) := hElist x hxE
          simpa using this
        exact hinterval a b le_rfl hab le_rfl hempty
    | cons t l ih =>
        intro a b E hab hE hEsub hsorted hnodup hlistE hElist hjump hinterval
        rcases List.pairwise_cons.mp hsorted with ⟨hfirst, htailSorted⟩
        rcases List.nodup_cons.mp hnodup with ⟨htnot, htailNodup⟩
        have htE : t ∈ E := hlistE t (by simp)
        have htBounds : t ∈ Set.Ioo a b := hEsub htE
        have hat : a < t := htBounds.1
        have htb : t < b := htBounds.2
        have hgap : E ∩ Set.Ioo a t = ∅ := by
          ext x
          simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hxE, hax, hxt⟩
          have hxlist := hElist x hxE
          rcases List.mem_cons.mp hxlist with hxtEq | hxTail
          · subst x
            exact (lt_irrefl _ hxt)
          · exact (not_lt_of_ge (hfirst x hxTail) hxt)
        let E' : Set ℝ := {x | x ∈ E ∧ t < x}
        have hE'finite : E'.Finite := hE.subset (by
          intro x hx
          exact hx.1)
        have hE'sub : E' ⊆ Set.Ioo t b := by
          intro x hx
          have hxBounds := hEsub hx.1
          exact ⟨hx.2, hxBounds.2⟩
        have htailE : ∀ x, x ∈ l → x ∈ E' := by
          intro x hx
          have hxE := hlistE x (by simp [hx])
          have htxle := hfirst x hx
          have hne : x ≠ t := by
            intro hEq
            apply htnot
            simpa [hEq] using hx
          exact ⟨hxE, lt_of_le_of_ne htxle (Ne.symm hne)⟩
        have hE'tail : ∀ x, x ∈ E' → x ∈ l := by
          intro x hx
          have hxlist := hElist x hx.1
          rcases List.mem_cons.mp hxlist with hEq | hxTail
          · subst x
            exact False.elim (lt_irrefl _ hx.2)
          · exact hxTail
        have hjump' : ∀ x, x ∈ E' → Relation.ReflTransGen R (pre x) (post x) := by
          intro x hx
          exact hjump x hx.1
        have hinterval' : ∀ s u, t ≤ s → s < u → u ≤ b →
            (E' ∩ Set.Ioo s u = ∅) → Relation.ReflTransGen R (post s) (pre u) := by
          intro s u hts hsu hub hgap'
          apply hinterval s u (le_trans (le_of_lt hat) hts) hsu hub
          have hgap'' : E ∩ Set.Ioo s u = ∅ := by
            ext x
            simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false]
            rintro ⟨hxE, hsx, hxu⟩
            have htx : t < x := lt_of_le_of_lt hts hsx
            have hxE' : x ∈ E' := ⟨hxE, htx⟩
            have hxContra : x ∈ E' ∩ Set.Ioo s u := ⟨hxE', ⟨hsx, hxu⟩⟩
            rw [hgap'] at hxContra
            simpa using hxContra
          exact hgap''
        have hrec := ih t b E' htb hE'finite hE'sub htailSorted htailNodup
          htailE hE'tail hjump' hinterval'
        exact (hinterval a t le_rfl hat (le_of_lt htb) hgap).trans
          ((hjump t htE).trans hrec)
  let l := hE.toFinset.sort (· ≤ ·)
  have hsorted : List.Pairwise (· ≤ ·) l := by
    simpa [l] using (Finset.pairwise_sort (s := hE.toFinset) (r := (· ≤ ·)))
  have hnodup : l.Nodup := by
    simpa [l] using (Finset.sort_nodup (s := hE.toFinset) (r := (· ≤ ·)))
  have hlistE : ∀ x, x ∈ l → x ∈ E := by
    intro x hx
    have hx' : x ∈ hE.toFinset := by simpa [l] using hx
    exact hE.mem_toFinset.mp hx'
  have hElist : ∀ x, x ∈ E → x ∈ l := by
    intro x hx
    have hx' : x ∈ hE.toFinset := hE.mem_toFinset.mpr hx
    simpa [l] using hx'
  exact chain l a b E hab hE hEsub hsorted hnodup hlistE hElist hjump hinterval
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedFiniteTimeline
