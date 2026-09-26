import PoincareConjecture.ParallelImplementation.FinitePolytopeConeCover
import PoincareConjecture.ParallelImplementation.FinitePolytopeExposedTransitivity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FinitePolytopeFaceChainCover
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def faceCenter (s : Finset E) : E := ((s.card : ℝ)⁻¹) • ∑ v ∈ s, v
/-- Cover a finite hull by actual centroid simplices of saturated face chains.
The same original point set is used on every face; no chain cover is assumed. -/
theorem finite_hull_covered_by_saturated_face_chains [FiniteDimensional ℝ E]
    (s : Finset E) :
    ∀ x ∈ convexHull ℝ (s : Set E), ∃ c : Finset (Finset E),
      c.Nonempty ∧ s ∈ c ∧
      (∀ t ∈ c, t.Nonempty ∧ t ⊆ s ∧
        IsExposed ℝ (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set E)) ∧
        (t : Set E) = (s : Set E) ∩ convexHull ℝ (t : Set E)) ∧
      (∀ t ∈ c, ∀ u ∈ c, t ⊆ u ∨ u ⊆ t) ∧
      x ∈ convexHull ℝ (faceCenter '' (c : Set (Finset E))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  suffices hmain : ∀ n : ℕ, ∀ s : Finset E, s.card = n →
      ∀ x ∈ convexHull ℝ (s : Set E), ∃ c : Finset (Finset E),
        c.Nonempty ∧ s ∈ c ∧
        (∀ t ∈ c, t.Nonempty ∧ t ⊆ s ∧
          IsExposed ℝ (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set E)) ∧
          (t : Set E) = (s : Set E) ∩ convexHull ℝ (t : Set E)) ∧
        (∀ t ∈ c, ∀ u ∈ c, t ⊆ u ∨ u ⊆ t) ∧
        x ∈ convexHull ℝ (faceCenter '' (c : Set (Finset E))) by
    exact hmain s.card s rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hsCard x hx
    by_cases hs : s.Nonempty
    · let b : E := faceCenter s
      obtain ⟨t₀, ht₀s, ht₀ex, ht₀proper, hx₀⟩ :=
        _root_.PoincareConjecture.ParallelImplementation.FinitePolytopeConeCover.convexHull_covered_by_centroid_face_cones s hs x hx
      have hbdef : b = ((s.card : ℝ)⁻¹) • ∑ v ∈ s, v := rfl
      have hx₀' : x ∈ convexHull ℝ (insert b (t₀ : Set E)) := by
        simpa [b, faceCenter] using hx₀
      let t : Finset E := s.filter fun v => v ∈ convexHull ℝ (t₀ : Set E)
      have ht₀t : t₀ ⊆ t := by
        intro v hv
        simp only [t, Finset.mem_filter]
        exact ⟨ht₀s hv, subset_convexHull ℝ (t₀ : Set E) hv⟩
      have htSub : t ⊆ s := Finset.filter_subset _ _
      have htHullSub : (t : Set E) ⊆ convexHull ℝ (t₀ : Set E) := by
        intro v hv
        exact (Finset.mem_filter.mp hv).2
      have hHullEq : convexHull ℝ (t : Set E) = convexHull ℝ (t₀ : Set E) := by
        apply Set.Subset.antisymm
        · exact convexHull_min htHullSub (convex_convexHull ℝ (t₀ : Set E))
        · exact convexHull_mono (by
            intro v hv
            exact ht₀t hv)
      have htEx : IsExposed ℝ (convexHull ℝ (s : Set E))
          (convexHull ℝ (t : Set E)) := by
        rw [hHullEq]
        exact ht₀ex
      have htProper : convexHull ℝ (t : Set E) ≠ convexHull ℝ (s : Set E) := by
        intro heq
        apply ht₀proper
        calc
          convexHull ℝ (t₀ : Set E) = convexHull ℝ (t : Set E) := hHullEq.symm
          _ = convexHull ℝ (s : Set E) := heq
      have htProperSub : t ⊂ s := by
        refine ⟨htSub, ?_⟩
        intro hRev
        have hEq : s = t := Finset.Subset.antisymm hRev htSub
        apply htProper
        rw [hEq]
      have htCard : t.card < s.card := Finset.card_lt_card htProperSub
      have hSat : (t : Set E) = (s : Set E) ∩ convexHull ℝ (t : Set E) := by
        ext v
        constructor
        · intro hv
          change v ∈ t at hv
          have hv' := Finset.mem_filter.mp hv
          exact ⟨hv'.1, by rw [hHullEq]; exact hv'.2⟩
        · rintro ⟨hvS, hvHull⟩
          change v ∈ t
          simp only [t, Finset.mem_filter]
          rw [hHullEq] at hvHull
          exact ⟨hvS, hvHull⟩
      have hxSat : x ∈ convexHull ℝ (insert b (t : Set E)) := by
        apply (convexHull_mono ?_) hx₀'
        intro v hv
        rcases Set.mem_insert_iff.mp hv with rfl | hv
        · exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (ht₀t hv)
      by_cases hxb : x = b
      · subst x
        refine ⟨{s}, ?_, ?_, ?_, ?_, ?_⟩
        · exact ⟨s, by simp⟩
        · simp
        · intro u hu
          have hus : u = s := Finset.mem_singleton.mp hu
          subst u
          refine ⟨hs, Finset.Subset.rfl, IsExposed.refl (convexHull ℝ (s : Set E)), ?_⟩
          ext v
          constructor
          · intro hv
            exact ⟨hv, subset_convexHull ℝ (s : Set E) hv⟩
          · exact fun hv => hv.1
        · intro u hu v hv
          have hus : u = s := Finset.mem_singleton.mp hu
          have hvs : v = s := Finset.mem_singleton.mp hv
          subst u
          subst v
          exact Or.inl Finset.Subset.rfl
        · apply subset_convexHull ℝ _
          exact ⟨s, by simp, rfl⟩
      · have htne : t.Nonempty := by
          by_contra htn
          have htempty : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp htn
          have hxsingle : x ∈ ({b} : Set E) := by
            have hx' : x ∈ convexHull ℝ (insert b (∅ : Set E)) := by
              simpa [htempty] using hxSat
            simpa [convexHull_singleton] using hx'
          have : x = b := Set.mem_singleton_iff.mp hxsingle
          exact hxb this
        have hxJoin : x ∈ convexJoin ℝ ({b} : Set E)
            (convexHull ℝ (t : Set E)) := by
          rw [convexHull_insert htne] at hxSat
          exact hxSat
        obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.mp hxJoin
        have hab : a = b := by simpa using ha
        subst a
        have hyT : y ∈ convexHull ℝ (t : Set E) := hy
        have htCardN : t.card < n := by rw [← hsCard]; exact htCard
        obtain ⟨c₀, hc₀ne, htc₀, hc₀props, hc₀chain, hyCenters⟩ :=
          ih t.card htCardN t rfl y hyT
        let c : Finset (Finset E) := insert s c₀
        refine ⟨c, ?_, ?_, ?_, ?_, ?_⟩
        · exact ⟨s, Finset.mem_insert_self _ _⟩
        · exact Finset.mem_insert_self _ _
        · intro u hu
          rcases Finset.mem_insert.mp hu with hus | huc₀
          · subst u
            refine ⟨hs, Finset.Subset.rfl, IsExposed.refl (convexHull ℝ (s : Set E)), ?_⟩
            ext v
            constructor
            · intro hv
              exact ⟨hv, subset_convexHull ℝ (s : Set E) hv⟩
            · exact fun hv => hv.1
          · rcases hc₀props u huc₀ with ⟨huNonempty, huSub, huEx, huSat⟩
            have huExS : IsExposed ℝ (convexHull ℝ (s : Set E))
                (convexHull ℝ (u : Set E)) :=
              _root_.PoincareConjecture.ParallelImplementation.FinitePolytopeExposedTransitivity.exposed_face_transitive_of_finite_hull s
                (convexHull ℝ (t : Set E)) (convexHull ℝ (u : Set E)) htEx huEx
            have huSatS : (u : Set E) = (s : Set E) ∩ convexHull ℝ (u : Set E) := by
              ext v
              constructor
              · intro hv
                have hvt : v ∈ (t : Set E) := huSub hv
                have hvs : v ∈ (s : Set E) := htSub hvt
                have hvPair : v ∈ (t : Set E) ∩ convexHull ℝ (u : Set E) := by
                  rw [← huSat]
                  exact hv
                exact ⟨hvs, hvPair.2⟩
              · rintro ⟨hvs, hvuHull⟩
                have hvHullT : v ∈ convexHull ℝ (t : Set E) :=
                  convexHull_mono huSub hvuHull
                have hvt : v ∈ (t : Set E) := by
                  have : v ∈ (s : Set E) ∩ convexHull ℝ (t : Set E) := ⟨hvs, hvHullT⟩
                  rw [← hSat] at this
                  exact this
                rw [huSat]
                exact ⟨hvt, hvuHull⟩
            exact ⟨huNonempty, Finset.Subset.trans huSub htSub, huExS, huSatS⟩
        · intro u hu v hv
          rcases Finset.mem_insert.mp hu with hus | huc₀
          · subst u
            rcases Finset.mem_insert.mp hv with hvs | hvc₀
            · subst v
              exact Or.inl Finset.Subset.rfl
            · rcases hc₀props v hvc₀ with ⟨_, hvSub, _, _⟩
              exact Or.inr (Finset.Subset.trans hvSub htSub)
          · rcases Finset.mem_insert.mp hv with hvs | hvc₀
            · subst v
              rcases hc₀props u huc₀ with ⟨_, huSub, _, _⟩
              exact Or.inl (Finset.Subset.trans huSub htSub)
            · exact hc₀chain u huc₀ v hvc₀
        · have hbCenters : b ∈ faceCenter '' (c : Set (Finset E)) := by
            exact ⟨s, Finset.mem_insert_self _ _, rfl⟩
          have hbCentersHull : b ∈ convexHull ℝ (faceCenter '' (c : Set (Finset E))) :=
            subset_convexHull ℝ _ hbCenters
          have hyCenters' : y ∈ convexHull ℝ (faceCenter '' (c : Set (Finset E))) := by
            apply (convexHull_mono ?_) hyCenters
            exact Set.image_mono (by
              intro u hu
              exact Finset.mem_insert_of_mem hu)
          exact (convex_convexHull ℝ (faceCenter '' (c : Set (Finset E)))).segment_subset
            hbCentersHull hyCenters' hxy
    · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      simp [convexHull_empty] at hx
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FinitePolytopeFaceChainCover
