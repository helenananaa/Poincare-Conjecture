import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FinitePolytopeExposedFaces
/-- Every actual exposed face of a finite convex hull is the hull of a subset
of its original finite vertices; hence the geometric face family is finite.
No finite face-poset certificate is assumed. -/
theorem exposed_faces_are_finitely_generated
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset E) :
    (∀ F : Set E, IsExposed ℝ (convexHull ℝ (s : Set E)) F →
      ∃ t : Finset E, t ⊆ s ∧ F = convexHull ℝ (t : Set E)) ∧
    {F : Set E | IsExposed ℝ (convexHull ℝ (s : Set E)) F}.Finite :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hgen : ∀ F : Set E, IsExposed ℝ (convexHull ℝ (s : Set E)) F →
      ∃ t : Finset E, t ⊆ s ∧ F = convexHull ℝ (t : Set E) := by
    intro F hF
    by_cases hFn : F.Nonempty
    · obtain ⟨l, hEq⟩ := hF hFn
      obtain ⟨x, hxF⟩ := hFn
      have hxA : x ∈ convexHull ℝ (s : Set E) := by
        rw [hEq] at hxF
        exact hxF.1
      let a := l x
      have hmax : ∀ y ∈ convexHull ℝ (s : Set E), l y ≤ a := by
        intro y hy
        have hxmax : l y ≤ l x := by
          rw [hEq] at hxF
          exact hxF.2 y hy
        simpa [a] using hxmax
      let t := s.filter fun y => l y = a
      refine ⟨t, Finset.filter_subset _ _, ?_⟩
      apply Set.Subset.antisymm
      · intro y hyF
        have hyA : y ∈ convexHull ℝ (s : Set E) := hF.subset hyF
        have hya : l y = a := by
          rw [hEq] at hyF
          apply le_antisymm (hmax y hyA)
          simpa [a] using hyF.2 x hxA
        obtain ⟨w, hw0, hw1, hw2⟩ := Finset.mem_convexHull'.1 hyA
        have hlin : (∑ z ∈ s, w z * l z) = l y := by
          calc
            (∑ z ∈ s, w z * l z) = l (∑ z ∈ s, w z • z) := by simp
            _ = l y := congrArg l hw2
        have hdef : (∑ z ∈ s, w z * (a - l z)) = 0 := by
          calc
            (∑ z ∈ s, w z * (a - l z)) = a * (∑ z ∈ s, w z) - ∑ z ∈ s, w z * l z := by
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
                ring
            _ = 0 := by rw [hw1, hlin, hya]; simp [a]
        have hterms : ∀ z ∈ s, 0 ≤ w z * (a - l z) := by
          intro z hz
          exact mul_nonneg (hw0 z hz) (sub_nonneg.mpr (hmax z (subset_convexHull ℝ _ hz)))
        have hzsum := (Finset.sum_eq_zero_iff_of_nonneg hterms).1 hdef
        have hzero : ∀ z ∈ s, z ∉ t → w z = 0 := by
          intro z hz hzt
          have hza : l z ≠ a := by
            simpa [t, Finset.mem_filter, hz] using hzt
          have hlt : l z < a := lt_of_le_of_ne (hmax z (subset_convexHull ℝ _ hz)) hza
          have hm := hzsum z hz
          rcases mul_eq_zero.mp hm with hwz | hvalz
          · exact hwz
          · exact False.elim ((sub_ne_zero.mpr (Ne.symm hza)) hvalz)
        have ht : t ⊆ s := Finset.filter_subset _ _
        have hsumw : (∑ z ∈ s, w z) = ∑ z ∈ t, w z := by
            exact (Finset.sum_subset (s₁ := t) (s₂ := s) ht (by
              intro z hz hzt
              exact hzero z hz hzt)).symm
        have hsumv : (∑ z ∈ s, w z • z) = ∑ z ∈ t, w z • z := by
            exact (Finset.sum_subset (s₁ := t) (s₂ := s) ht (by
              intro z hz hzt
              simp [hzero z hz hzt])).symm
        rw [Finset.mem_convexHull']
        refine ⟨w, ?_, ?_, ?_⟩
        · intro z hz
          exact hw0 z (ht hz)
        · simpa [← hsumw] using hw1
        · rw [← hsumv, hw2]
      · apply convexHull_min
        · intro y hyT
          have hyS : y ∈ s := (Finset.mem_filter.mp hyT).1
          have hya : l y = a := (Finset.mem_filter.mp hyT).2
          rw [hEq]
          refine ⟨subset_convexHull ℝ _ hyS, ?_⟩
          intro z hz
          exact (hmax z hz).trans (by simpa [a] using hya.symm.le)
        · exact hF.convex (convex_convexHull ℝ (s : Set E))
    · refine ⟨∅, Finset.empty_subset _, ?_⟩
      have hFempty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hFn
      simp [hFempty]
  refine ⟨hgen, ?_⟩
  · let g : Finset E → Set E := fun t => convexHull ℝ (t : Set E)
    have hfinite : (g '' (s.powerset : Set (Finset E))).Finite := by
      exact (s.powerset.finite_toSet.image g)
    apply hfinite.subset
    intro F hF
    obtain ⟨t, ht, rfl⟩ := hgen F hF
    exact ⟨t, Finset.mem_powerset.mpr ht, rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FinitePolytopeExposedFaces
