import PoincareConjecture.ParallelImplementation.FinitePolytopeExposedFaces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FinitePolytopeExposedTransitivity
/-- Exposed-face transitivity for an ACTUAL finite convex hull.
This fails for general convex sets; finiteness must be used in the proof. -/
theorem exposed_face_transitive_of_finite_hull
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset E) (F G : Set E)
    (hF : IsExposed ℝ (convexHull ℝ (s : Set E)) F)
    (hG : IsExposed ℝ F G) :
    IsExposed ℝ (convexHull ℝ (s : Set E)) G :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases hG0 : G.Nonempty
  · have hGne := hG0
    obtain ⟨g, hg⟩ := hG0
    have hF0 : F.Nonempty := ⟨g, hG.subset hg⟩
    have hFne := hF0
    by_cases hFA : F = convexHull ℝ (s : Set E)
    · rw [← hFA]
      exact hG
    · obtain ⟨x, hx⟩ := hF0
      obtain ⟨l, hFeq⟩ := hF hFne
      obtain ⟨m, hGeq⟩ := hG hGne
      let a : ℝ := l x
      let b : ℝ := m g
      have hxA : x ∈ convexHull ℝ (s : Set E) := hF.subset hx
      have hgF : g ∈ F := hG.subset hg
      have hgA : g ∈ convexHull ℝ (s : Set E) := hF.subset hgF
      have hAmax : ∀ y ∈ convexHull ℝ (s : Set E), l y ≤ a := by
        intro y hy
        have hx' : x ∈ {z ∈ convexHull ℝ (s : Set E) | ∀ w ∈ convexHull ℝ (s : Set E), l w ≤ l z} := by
          rw [← hFeq]
          exact hx
        exact hx'.2 y hy
      have hFl : ∀ y ∈ F, l y = a := by
        intro y hy
        have hy' : y ∈ {z ∈ convexHull ℝ (s : Set E) | ∀ w ∈ convexHull ℝ (s : Set E), l w ≤ l z} := by
          rw [← hFeq]
          exact hy
        dsimp [a]
        exact le_antisymm (hAmax y hy'.1) (hy'.2 x hxA)
      have hFm : ∀ y ∈ F, m y ≤ b := by
        intro y hy
        have hg' : g ∈ {z ∈ F | ∀ w ∈ F, m w ≤ m z} := by
          rw [← hGeq]
          exact hg
        exact hg'.2 y hy
      have hGm : ∀ y ∈ G, m y = b := by
        intro y hy
        have hy' : y ∈ {z ∈ F | ∀ w ∈ F, m w ≤ m z} := by
          rw [← hGeq]
          exact hy
        have hg' : g ∈ {z ∈ F | ∀ w ∈ F, m w ≤ m z} := by
          rw [← hGeq]
          exact hg
        exact le_antisymm (hg'.2 y hy'.1) (hy'.2 g hg'.1)
      obtain ⟨t₀, ht₀s, hFt₀⟩ :=
        (PoincareConjecture.ParallelImplementation.FinitePolytopeExposedFaces.exposed_faces_are_finitely_generated s).1 F hF
      let t : Finset E := s.filter fun v => l v = a
      have ht₀t : t₀ ⊆ t := by
        intro v hv
        have hvF : v ∈ F := by
          rw [hFt₀]
          exact subset_convexHull ℝ (t₀ : Set E) hv
        simp only [t, Finset.mem_filter]
        exact ⟨ht₀s hv, hFl v hvF⟩
      have htF : (t : Set E) ⊆ F := by
        intro v hv
        have hv' := Finset.mem_filter.mp hv
        rw [hFeq]
        refine ⟨subset_convexHull ℝ (s : Set E) hv'.1, ?_⟩
        intro y hy
        exact (hAmax y hy).trans (by simpa [a] using hv'.2.symm.le)
      have hFt : F = convexHull ℝ (t : Set E) := by
        apply Set.Subset.antisymm
        · rw [hFt₀]
          exact convexHull_mono (by
            intro v hv
            exact ht₀t hv)
        · exact convexHull_min htF (hF.convex (convex_convexHull ℝ (s : Set E)))
      let u : Finset E := s.filter fun v => v ∉ t
      have hu : u.Nonempty := by
        by_contra hnu
        have hst : s ⊆ t := by
          intro v hv
          by_contra hvt
          exact hnu ⟨v, Finset.mem_filter.mpr ⟨hv, hvt⟩⟩
        have hts : t = s := Finset.Subset.antisymm (Finset.filter_subset _ _) hst
        apply hFA
        rw [hFt, hts]
      let ratio : E → ℝ := fun v =>
        (a - l v) / (max (m v - b) 0 + 1)
      have hratio : ∀ v ∈ u, 0 < ratio v := by
        intro v hv
        have hv' := Finset.mem_filter.mp hv
        have hne : l v ≠ a := by
          intro heq
          exact hv'.2 (Finset.mem_filter.mpr ⟨hv'.1, heq⟩)
        have hlt : l v < a := lt_of_le_of_ne (hAmax v (subset_convexHull ℝ _ hv'.1)) hne
        dsimp [ratio]
        exact div_pos (by simpa [a] using sub_pos.mpr hlt) (by positivity)
      obtain ⟨v₀, hv₀, hmin⟩ := Finset.exists_min_image u ratio hu
      let ε : ℝ := ratio v₀
      have hεpos : 0 < ε := hratio v₀ hv₀
      have hεle : ∀ v ∈ u, ε ≤ ratio v := by
        intro v hv
        exact hmin v hv
      let p : StrongDual ℝ E := l + ε • m
      let c : ℝ := a + ε * b
      have hpvertex : ∀ v ∈ s, p v ≤ c := by
        intro v hv
        by_cases hvt : v ∈ t
        · have hvl : l v = a := (Finset.mem_filter.mp hvt).2
          have hvF : v ∈ F := htF hvt
          have hvm : m v ≤ b := hFm v hvF
          dsimp [p, c]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul]
          nlinarith [mul_nonneg hεpos.le (sub_nonneg.mpr hvm)]
        · have hvU : v ∈ u := Finset.mem_filter.mpr ⟨hv, hvt⟩
          have hd : 0 < a - l v := by
            have hne : l v ≠ a := fun heq => hvt (Finset.mem_filter.mpr ⟨hv, heq⟩)
            exact sub_pos.mpr (lt_of_le_of_ne (hAmax v (subset_convexHull ℝ _ hv)) hne)
          let q : ℝ := m v - b
          have hqbound : ε ≤ (a - l v) / (max q 0 + 1) := by
            simpa [ε, ratio, q] using hεle v hvU
          have hpert : ε * q < a - l v := by
            by_cases hq : q ≤ 0
            · have hnonpos : ε * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hεpos.le hq
              linarith
            · have hqpos : 0 < q := lt_of_not_ge hq
              have hden : 0 < q + 1 := by linarith
              have hmul : ε * (q + 1) ≤ a - l v := by
                have hb : ε ≤ (a - l v) / (q + 1) := by
                  simpa [max_eq_left hqpos.le] using hqbound
                exact (le_div_iff₀ hden).1 hb
              nlinarith
          have hstrict : l v + ε * m v < c := by
            dsimp [c]
            dsimp [q] at hpert
            nlinarith
          dsimp [p]
          simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
            smul_eq_mul]
          exact hstrict.le
      have hpmax : ∀ y ∈ convexHull ℝ (s : Set E), p y ≤ c := by
        intro y hy
        obtain ⟨w, hw₀, hw₁, hw₂⟩ := Finset.mem_convexHull'.1 hy
        have hcalc : (∑ v ∈ s, w v * p v) = p y := by
          calc
            (∑ v ∈ s, w v * p v) = p (∑ v ∈ s, w v • v) := by simp
            _ = p y := congrArg p hw₂
        calc
          p y = ∑ v ∈ s, w v * p v := hcalc.symm
          _ ≤ ∑ v ∈ s, w v * c := Finset.sum_le_sum fun v hv =>
            mul_le_mul_of_nonneg_left (hpvertex v hv) (hw₀ v hv)
          _ = c := by rw [← Finset.sum_mul, hw₁]; simp
      have hpg : p g = c := by
        have hgl : l g = a := hFl g hgF
        have hgm : m g = b := rfl
        simp [p, c, hgl, hgm]
      have hExposure : G = {y ∈ convexHull ℝ (s : Set E) | ∀ z ∈ convexHull ℝ (s : Set E), p z ≤ p y} := by
        apply Set.Subset.antisymm
        · intro y hy
          have hyF : y ∈ F := hG.subset hy
          refine ⟨hF.subset hyF, ?_⟩
          intro z hz
          calc
            p z ≤ c := hpmax z hz
            _ = p y := by
              have hyl : l y = a := hFl y hyF
              have hym : m y = b := hGm y hy
              simp [p, c, hyl, hym]
        · rintro y ⟨hyA, hymax⟩
          have hyp : p y = c := le_antisymm (hpmax y hyA) (by
            have h := hymax g hgA
            simpa [hpg] using h)
          obtain ⟨w, hw₀, hw₁, hw₂⟩ := Finset.mem_convexHull'.1 hyA
          have hlin : (∑ v ∈ s, w v * p v) = p y := by
            calc
              (∑ v ∈ s, w v * p v) = p (∑ v ∈ s, w v • v) := by simp
              _ = p y := congrArg p hw₂
          have hdef : (∑ v ∈ s, w v * (c - p v)) = 0 := by
            calc
              (∑ v ∈ s, w v * (c - p v)) = c * (∑ v ∈ s, w v) - ∑ v ∈ s, w v * p v := by
                simp_rw [mul_sub]
                rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
                ring
              _ = 0 := by rw [hw₁, hlin, hyp]; simp
          have hterms : ∀ v ∈ s, 0 ≤ w v * (c - p v) := by
            intro v hv
            exact mul_nonneg (hw₀ v hv) (sub_nonneg.mpr (hpvertex v hv))
          have hzsum := (Finset.sum_eq_zero_iff_of_nonneg hterms).1 hdef
          have hzero : ∀ v ∈ s, v ∉ t → w v = 0 := by
            intro v hv hvt
            have hvU : v ∈ u := Finset.mem_filter.mpr ⟨hv, hvt⟩
            have hstrict : p v < c := by
              have hd : 0 < a - l v := by
                have hne : l v ≠ a := fun heq => hvt (Finset.mem_filter.mpr ⟨hv, heq⟩)
                exact sub_pos.mpr (lt_of_le_of_ne (hAmax v (subset_convexHull ℝ _ hv)) hne)
              let q : ℝ := m v - b
              have hqbound : ε ≤ (a - l v) / (max q 0 + 1) := by
                simpa [ε, ratio, q] using hεle v hvU
              have hpert : ε * q < a - l v := by
                by_cases hq : q ≤ 0
                · have hnonpos : ε * q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hεpos.le hq
                  linarith
                · have hqpos : 0 < q := lt_of_not_ge hq
                  have hden : 0 < q + 1 := by linarith
                  have hmul : ε * (q + 1) ≤ a - l v := (le_div_iff₀ hden).1 (by
                    simpa [max_eq_left hqpos.le] using hqbound)
                  nlinarith
              dsimp [p]
              simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
                smul_eq_mul]
              dsimp [q] at hpert
              dsimp [c]
              nlinarith
            have hz := hzsum v hv
            rcases mul_eq_zero.mp hz with hwv | hzero'
            · exact hwv
            · exact False.elim (ne_of_gt (sub_pos.mpr hstrict) hzero')
          have ht : t ⊆ s := Finset.filter_subset _ _
          have hsumw : (∑ v ∈ s, w v) = ∑ v ∈ t, w v := by
            exact (Finset.sum_subset ht (by
              intro v hv hvt
              exact hzero v hv hvt)).symm
          have hsumv : (∑ v ∈ s, w v • v) = ∑ v ∈ t, w v • v := by
            exact (Finset.sum_subset ht (by
              intro v hv hvt
              simp [hzero v hv hvt])).symm
          have hyF : y ∈ F := by
            rw [hFt]
            rw [Finset.mem_convexHull']
            refine ⟨w, ?_, ?_, ?_⟩
            · intro v hv
              exact hw₀ v (ht hv)
            · simpa [← hsumw] using hw₁
            · rw [← hsumv, hw₂]
          have hyl : l y = a := hFl y hyF
          have hym : m y = b := by
            have hpval : l y + ε * m y = a + ε * b := by
              simpa [p, c, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
                smul_eq_mul] using hyp
            nlinarith
          rw [hGeq]
          refine ⟨hyF, ?_⟩
          intro z hz
          rw [hym]
          exact hFm z hz
      intro _
      exact ⟨p, hExposure⟩
  · have hGe : G = ∅ := Set.not_nonempty_iff_eq_empty.mp hG0
    rw [hGe]
    exact isExposed_empty
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FinitePolytopeExposedTransitivity
