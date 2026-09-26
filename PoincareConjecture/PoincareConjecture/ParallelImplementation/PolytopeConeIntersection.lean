import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.PolytopeConeIntersection
open Set
open scoped BigOperators
/-- Cones over genuine boundary faces meet exactly over their common face.
The center is the actual average of all original generators; no cone
intersection or relative-interior certificate is assumed. -/
theorem centroid_cone_intersection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset E) (hs : s.Nonempty)
    (F G : Set E)
    (hF : IsExposed ℝ (convexHull ℝ (s : Set E)) F)
    (hG : IsExposed ℝ (convexHull ℝ (s : Set E)) G)
    (hFproper : F ≠ convexHull ℝ (s : Set E))
    (hGproper : G ≠ convexHull ℝ (s : Set E)) :
    let c : E := (s.card : ℝ)⁻¹ • ∑ v ∈ s, v
    convexHull ℝ (insert c F) ∩ convexHull ℝ (insert c G) =
      convexHull ℝ (insert c (F ∩ G)) :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp only
  let c : E := (s.card : ℝ)⁻¹ • ∑ v ∈ s, v
  change convexHull ℝ (insert c F) ∩ convexHull ℝ (insert c G) =
    convexHull ℝ (insert c (F ∩ G))
  classical
  by_cases hFe : F = ∅
  · subst F
    simp only [empty_inter, insert_empty_eq, convexHull_singleton]
    ext x
    constructor
    · rintro ⟨hx, _⟩
      exact hx
    · intro hx
      have hxc : x = c := by simpa using hx
      subst x
      exact ⟨by simp, subset_convexHull ℝ _ (by simp)⟩
  by_cases hGe : G = ∅
  · subst G
    simp only [inter_empty, insert_empty_eq, convexHull_singleton]
    ext x
    constructor
    · rintro ⟨_, hx⟩
      exact hx
    · intro hx
      have hxc : x = c := by simpa using hx
      subst x
      exact ⟨subset_convexHull ℝ _ (by simp), by simp⟩
  have hFn : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hFe
  have hGn : G.Nonempty := Set.nonempty_iff_ne_empty.mpr hGe
  let K : Set E := convexHull ℝ (s : Set E)
  have face_data : ∀ (H : Set E), IsExposed ℝ K H → H ≠ K → H.Nonempty →
      ∃ l : StrongDual ℝ E,
        H = {x ∈ K | ∀ y ∈ K, l y ≤ l x} ∧ ∀ x ∈ H, l c < l x := by
    intro H hH hHproper hHn
    obtain ⟨l, hl⟩ := hH hHn
    have hHconv : Convex ℝ H := hH.convex (convex_convexHull ℝ (s : Set E))
    have hvout : ∃ v ∈ s, v ∉ H := by
      by_contra hn
      have hsH : (s : Set E) ⊆ H := by
        intro v hv
        by_contra hvH
        exact hn ⟨v, hv, hvH⟩
      have hKH : K ⊆ H := by
        exact convexHull_min hsH hHconv
      exact hHproper (Set.Subset.antisymm hH.subset hKH)
    obtain ⟨v₀, hv₀s, hv₀H⟩ := hvout
    have hmax : ∀ x ∈ H, ∀ y ∈ K, l y ≤ l x := by
      intro x hx y hy
      rw [hl] at hx
      exact hx.2 y hy
    have hv₀lt : ∀ x ∈ H, l v₀ < l x := by
      intro x hx
      have hv₀le : l v₀ ≤ l x := hmax x hx v₀ (subset_convexHull ℝ _ hv₀s)
      apply lt_of_le_of_ne hv₀le
      intro heq
      apply hv₀H
      rw [hl]
      refine ⟨subset_convexHull ℝ _ hv₀s, ?_⟩
      intro y hy
      simpa [heq] using hmax x hx y hy
    have hc_lt : ∀ x ∈ H, l c < l x := by
      intro x hx
      have hsum := Finset.sum_lt_sum
        (fun v hv => hmax x hx v (subset_convexHull ℝ _ hv))
        ⟨v₀, hv₀s, hv₀lt x hx⟩
      have hsum' : (∑ v ∈ s, l v) < (s.card : ℝ) * l x := by
        simpa using hsum
      have hcard : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
      have hc_eval : l c = (s.card : ℝ)⁻¹ * ∑ v ∈ s, l v := by
        simp [c, map_sum, smul_eq_mul]
      calc
        l c = (s.card : ℝ)⁻¹ * ∑ v ∈ s, l v := hc_eval
        _ < (s.card : ℝ)⁻¹ * ((s.card : ℝ) * l x) :=
          mul_lt_mul_of_pos_left hsum' (inv_pos.mpr hcard)
        _ = l x := by field_simp
    exact ⟨l, hl, hc_lt⟩
  obtain ⟨lF, hFrep, hFstrict⟩ := face_data F hF hFproper hFn
  obtain ⟨lG, hGrep, hGstrict⟩ := face_data G hG hGproper hGn
  have hFconv : Convex ℝ F := hF.convex (convex_convexHull ℝ (s : Set E))
  have hGconv : Convex ℝ G := hG.convex (convex_convexHull ℝ (s : Set E))
  have hjoinF : convexHull ℝ (insert c F) = convexJoin ℝ {c} F := by
    rw [convexHull_insert hFn, hFconv.convexHull_eq]
  have hjoinG : convexHull ℝ (insert c G) = convexJoin ℝ {c} G := by
    rw [convexHull_insert hGn, hGconv.convexHull_eq]
  apply Set.Subset.antisymm
  · intro x hx
    rw [hjoinF, hjoinG] at hx
    obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.mp hx.1
    obtain ⟨b, hb, z, hz, hxz⟩ := mem_convexJoin.mp hx.2
    have ha' : a = c := by simpa using ha
    have hb' : b = c := by simpa using hb
    subst a
    subst b
    by_cases hxc : x = c
    · rw [hxc]
      exact subset_convexHull ℝ _ (by simp)
    have hxySegment : x ∈ segment ℝ c y := hxy
    rw [segment_eq_image_lineMap] at hxy hxz
    obtain ⟨t, ht, hxt⟩ := hxy
    obtain ⟨u, hu, hxu⟩ := hxz
    have hxt' : x = (1 - t) • c + t • y := by
      simpa only [AffineMap.lineMap_apply_module] using hxt.symm
    have hxu' : x = (1 - u) • c + u • z := by
      simpa only [AffineMap.lineMap_apply_module] using hxu.symm
    rcases ht with ⟨ht0, ht1⟩
    rcases hu with ⟨hu0, hu1⟩
    have htpos : 0 < t := by
      by_contra hn
      have htzero : t = 0 := le_antisymm (le_of_not_gt hn) ht0
      subst t
      have : x = c := by simpa using hxt'
      exact hxc this
    have hupos : 0 < u := by
      by_contra hn
      have huzero : u = 0 := le_antisymm (le_of_not_gt hn) hu0
      subst u
      have : x = c := by simpa using hxu'
      exact hxc this
    rcases lt_trichotomy t u with htu | htu | hut
    · have hscalar : (1 - t) * lG c + t * lG y = (1 - u) * lG c + u * lG z := by
        have hv := congrArg lG (hxt'.symm.trans hxu')
        simpa [map_add, map_smul, smul_eq_mul] using hv
      have hyK : y ∈ K := hF.subset hy
      have hz_lt : lG c < lG z := hGstrict z hz
      have hzrep : z ∈ {w ∈ K | ∀ q ∈ K, lG q ≤ lG w} := by
        simpa [hGrep] using hz
      have hzmax : ∀ w ∈ K, lG w ≤ lG z := by
        exact hzrep.2
      have hy_le : lG y ≤ lG z := hzmax y hyK
      let r : ℝ := t / u
      have hrpos : 0 < r := div_pos htpos hupos
      have hrlt : r < 1 := (div_lt_one hupos).2 htu
      have hzdecomp : lG z = (1 - r) * lG c + r * lG y := by
        dsimp [r]
        field_simp [hupos.ne']
        nlinarith [hscalar]
      have hcomb : (1 - r) * lG c + r * lG y <
          (1 - r) * lG z + r * lG z := by
        exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hz_lt (sub_pos.mpr hrlt))
          (mul_le_mul_of_nonneg_left hy_le (le_of_lt hrpos))
      have hfalse : lG z < lG z := by
        calc
          lG z = (1 - r) * lG c + r * lG y := hzdecomp
          _ < (1 - r) * lG z + r * lG z := hcomb
          _ = lG z := by ring
      exact False.elim (lt_irrefl _ hfalse)
    · have hvec : (1 - t) • c + t • y = (1 - u) • c + u • z :=
        hxt'.symm.trans hxu'
      rw [htu] at hvec
      have hsmul : u • y = u • z := add_left_cancel hvec
      have hyz : y = z := by
        calc
          y = u⁻¹ • (u • y) := by
            rw [smul_smul, inv_mul_cancel₀ hupos.ne', one_smul]
          _ = u⁻¹ • (u • z) := congrArg (fun w : E => u⁻¹ • w) hsmul
          _ = z := by
            rw [smul_smul, inv_mul_cancel₀ hupos.ne', one_smul]
      have hyG : y ∈ G := by simpa [hyz] using hz
      exact (segment_subset_convexHull (𝕜 := ℝ) (s := insert c (F ∩ G))
        (x := c) (y := y) (by simp) (Or.inr ⟨hy, hyG⟩)) hxySegment
    · have hscalar : (1 - t) * lF c + t * lF y = (1 - u) * lF c + u * lF z := by
        have hv := congrArg lF (hxt'.symm.trans hxu')
        simpa [map_add, map_smul, smul_eq_mul] using hv
      have hy_lt : lF c < lF y := hFstrict y hy
      have hyrep : y ∈ {w ∈ K | ∀ q ∈ K, lF q ≤ lF w} := by
        simpa [hFrep] using hy
      have hymax : ∀ w ∈ K, lF w ≤ lF y := by
        exact hyrep.2
      have hz_le : lF z ≤ lF y := hymax z (hG.subset hz)
      let r : ℝ := u / t
      have hrpos : 0 < r := div_pos hupos htpos
      have hrlt : r < 1 := (div_lt_one htpos).2 hut
      have hydcomp : lF y = (1 - r) * lF c + r * lF z := by
        dsimp [r]
        field_simp [htpos.ne']
        nlinarith [hscalar]
      have hcomb : (1 - r) * lF c + r * lF z <
          (1 - r) * lF y + r * lF y := by
        exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hy_lt (sub_pos.mpr hrlt))
          (mul_le_mul_of_nonneg_left hz_le (le_of_lt hrpos))
      have hfalse : lF y < lF y := by
        calc
          lF y = (1 - r) * lF c + r * lF z := hydcomp
          _ < (1 - r) * lF y + r * lF y := hcomb
          _ = lF y := by ring
      exact False.elim (lt_irrefl _ hfalse)
  · intro x hx
    have hsubF : insert c (F ∩ G) ⊆ insert c F := by
      intro w hw
      rcases Set.mem_insert_iff.mp hw with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · exact Set.mem_insert_iff.mpr (Or.inr (inter_subset_left h))
    have hsubG : insert c (F ∩ G) ⊆ insert c G := by
      intro w hw
      rcases Set.mem_insert_iff.mp hw with h | h
      · exact Set.mem_insert_iff.mpr (Or.inl h)
      · exact Set.mem_insert_iff.mpr (Or.inr (inter_subset_right h))
    constructor
    · exact convexHull_mono hsubF hx
    · exact convexHull_mono hsubG hx
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.PolytopeConeIntersection
