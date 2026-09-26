import PoincareConjecture.ParallelImplementation.PolytopeConeIntersection
import PoincareConjecture.ParallelImplementation.FinitePolytopeExposedTransitivity
import PoincareConjecture.ParallelImplementation.ExposedFaceChainBarycenters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SaturatedFaceChainIntersection
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance : DecidableEq E := Classical.decEq E
def faceCenter (s : Finset E) : E := (s.card : ℝ)⁻¹ • ∑ v ∈ s, v
def IsSaturatedFaceChain (s : Finset E) (c : Finset (Finset E)) : Prop :=
  (∀ t ∈ c, t.Nonempty ∧ t ⊆ s ∧
    IsExposed ℝ (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set E)) ∧
    (t : Set E) = (s : Set E) ∩ convexHull ℝ (t : Set E)) ∧
  (∀ t ∈ c, ∀ u ∈ c, t ⊆ u ∨ u ⊆ t)
/-- Actual centroid simplices of saturated face flags meet exactly on shared
vertices. This supplies geometric intersection compatibility, not only cover. -/
theorem saturated_face_chain_simplex_intersection [FiniteDimensional ℝ E]
    (s : Finset E) (c d : Finset (Finset E))
    (hc : IsSaturatedFaceChain s c) (hd : IsSaturatedFaceChain s d) :
    convexHull ℝ (faceCenter '' (c : Set (Finset E))) ∩
      convexHull ℝ (faceCenter '' (d : Set (Finset E))) =
    convexHull ℝ (faceCenter '' ((c ∩ d : Finset (Finset E)) : Set (Finset E))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let H : Finset E → Set E := fun t => convexHull ℝ (t : Set E)
  let Q : Finset (Finset E) → Set E :=
    fun c => convexHull ℝ (faceCenter '' (c : Set (Finset E)))
  change Q c ∩ Q d = Q (c ∩ d)

  have center_mem_hull (t : Finset E) (ht : t.Nonempty) :
      faceCenter t ∈ H t := by
    rw [Finset.mem_convexHull']
    refine ⟨fun _ => ((t.card : ℝ)⁻¹), ?_, ?_, ?_⟩
    · intro v hv
      positivity
    · have hcard : (t.card : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.card_ne_zero.mpr ht)
      simp [Finset.sum_const, nsmul_eq_mul, hcard]
    · simpa [faceCenter] using
        (Finset.smul_sum (r := (t.card : ℝ)⁻¹) (f := fun v : E => v) (s := t)).symm

  have average_le (t : Finset E) (ht : t.Nonempty) (l : StrongDual ℝ E)
      (a : ℝ) (hle : ∀ v ∈ t, l v ≤ a) : l (faceCenter t) ≤ a := by
    have hsum := Finset.sum_le_sum (fun v hv => hle v hv)
    have hsum' : (∑ v ∈ t, l v) ≤ (t.card : ℝ) * a := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hsum
    have hcard : 0 < (t.card : ℝ) := by exact_mod_cast ht.card_pos
    have hmap : l (faceCenter t) = (t.card : ℝ)⁻¹ * ∑ v ∈ t, l v := by
      simp [faceCenter, map_smul, map_sum, smul_eq_mul]
    rw [hmap]
    calc
      (t.card : ℝ)⁻¹ * ∑ v ∈ t, l v ≤ (t.card : ℝ)⁻¹ * ((t.card : ℝ) * a) :=
        mul_le_mul_of_nonneg_left hsum' (inv_nonneg.mpr (le_of_lt hcard))
      _ = a := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard), one_mul]

  have average_lt (t : Finset E) (ht : t.Nonempty) (l : StrongDual ℝ E)
      (a : ℝ) (hle : ∀ v ∈ t, l v ≤ a) (v₀ : E) (hv₀ : v₀ ∈ t)
      (hlt : l v₀ < a) : l (faceCenter t) < a := by
    have hsum := Finset.sum_lt_sum hle ⟨v₀, hv₀, hlt⟩
    have hsum' : (∑ v ∈ t, l v) < (t.card : ℝ) * a := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hsum
    have hcard : 0 < (t.card : ℝ) := by exact_mod_cast ht.card_pos
    have hmap : l (faceCenter t) = (t.card : ℝ)⁻¹ * ∑ v ∈ t, l v := by
      simp [faceCenter, map_smul, map_sum, smul_eq_mul]
    rw [hmap]
    calc
      (t.card : ℝ)⁻¹ * ∑ v ∈ t, l v < (t.card : ℝ)⁻¹ * ((t.card : ℝ) * a) :=
        mul_lt_mul_of_pos_left hsum' (inv_pos.mpr hcard)
      _ = a := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard), one_mul]

  have average_eq (t : Finset E) (ht : t.Nonempty) (l : StrongDual ℝ E)
      (a : ℝ) (heq : ∀ v ∈ t, l v = a) : l (faceCenter t) = a := by
    apply le_antisymm
    · exact average_le t ht l a (fun v hv => (heq v hv).le)
    · have hneg := average_le t ht (-l) (-a) (by
        intro v hv
        simpa using (heq v hv).symm.le)
      simpa using hneg

  have support_data : ∀ (s u : Finset E), s.Nonempty → u.Nonempty → u ⊆ s →
      IsExposed ℝ (H s) (H u) →
      (u : Set E) = (s : Set E) ∩ H u → u ≠ s →
      ∃ l : StrongDual ℝ E, ∃ a : ℝ,
        (∀ v ∈ s, l v ≤ a) ∧ (∀ v ∈ u, l v = a) ∧
        (∀ v ∈ s, v ∉ u → l v < a) ∧
        (∀ x ∈ H u, l x = a) ∧ l (faceCenter s) < a := by
    intro s u hs hu hus hU hExact hproper
    have huH : (H u).Nonempty := by
      obtain ⟨v, hv⟩ := hu
      exact ⟨v, subset_convexHull ℝ (u : Set E) hv⟩
    obtain ⟨l, hl⟩ := hU huH
    obtain ⟨q, hq⟩ := hu
    have hqU : q ∈ H u := subset_convexHull ℝ (u : Set E) hq
    have hqS : q ∈ H s := by
      exact (convexHull_mono hus) hqU
    rw [hl] at hqU
    let a : ℝ := l q
    have hmax : ∀ x ∈ H s, l x ≤ a := by
      intro x hx
      simpa [a] using hqU.2 x hx
    have hle : ∀ v ∈ s, l v ≤ a := by
      intro v hv
      exact hmax v (subset_convexHull ℝ (s : Set E) hv)
    have hlevelU : ∀ x ∈ H u, l x = a := by
      intro x hx
      rw [hl] at hx
      apply le_antisymm
      · simpa [a] using hmax x hx.1
      · simpa [a] using hx.2 q hqS
    have hstrict : ∀ v ∈ s, v ∉ u → l v < a := by
      intro v hv hvu
      apply lt_of_le_of_ne (hle v hv)
      intro heq
      have hmaxv : ∀ y ∈ H s, l y ≤ l v := by
        intro y hy
        simpa [a, heq] using hmax y hy
      have hvU : v ∈ H u := by
        rw [hl]
        exact ⟨subset_convexHull ℝ (s : Set E) hv, hmaxv⟩
      have hvExact : v ∈ (u : Set E) := by
        have hmem : v ∈ (s : Set E) ∩ H u := ⟨hv, hvU⟩
        rw [← hExact] at hmem
        exact hmem
      exact hvu hvExact
    have hout : ∃ v ∈ s, v ∉ u := by
      by_contra hn
      have hsu : s ⊆ u := by
        intro v hv
        by_contra hvu
        exact hn ⟨v, hv, hvu⟩
      exact hproper (Finset.Subset.antisymm hus hsu)
    obtain ⟨v₀, hv₀, hv₀u⟩ := hout
    have hsum := Finset.sum_lt_sum hle ⟨v₀, hv₀, hstrict v₀ hv₀ hv₀u⟩
    have hsum' : (∑ v ∈ s, l v) < (s.card : ℝ) * a := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hsum
    have hcard : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
    have hmap : l (faceCenter s) = (s.card : ℝ)⁻¹ * ∑ v ∈ s, l v := by
      simp [faceCenter, map_smul, map_sum, smul_eq_mul]
    refine ⟨l, a, hle, ?_, hstrict, hlevelU, ?_⟩
    · intro v hv
      have hvU : v ∈ H u := subset_convexHull ℝ (u : Set E) hv
      exact hlevelU v hvU
    · rw [hmap]
      calc
        (s.card : ℝ)⁻¹ * ∑ v ∈ s, l v <
            (s.card : ℝ)⁻¹ * ((s.card : ℝ) * a) :=
          mul_lt_mul_of_pos_left hsum' (inv_pos.mpr hcard)
        _ = a := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcard), one_mul]

  have center_not_mem_face : ∀ (s u t : Finset E),
      s.Nonempty → u.Nonempty → t.Nonempty → u ⊆ s → t ⊆ s →
      IsExposed ℝ (H s) (H u) →
      (u : Set E) = (s : Set E) ∩ H u → u ≠ s →
      ¬ t ⊆ u → faceCenter t ∉ H u := by
    intro s u t hs hu ht hus hts hU hExact hproper htu
    obtain ⟨l, a, hle, huval, hout, hlevel, hcenter⟩ :=
      support_data s u hs hu hus hU hExact hproper
    have houtT : ∃ v ∈ t, v ∉ u := by
      by_contra hn
      have htu' : t ⊆ u := by
        intro v hv
        by_contra hvu
        exact hn ⟨v, hv, hvu⟩
      exact htu htu'
    obtain ⟨v₀, hv₀, hv₀u⟩ := houtT
    have htlt : l (faceCenter t) < a :=
      average_lt t ht l a (fun v hv => hle v (hts hv)) v₀ hv₀ (hout v₀ (hts hv₀) hv₀u)
    intro hmem
    have := hlevel (faceCenter t) hmem
    linarith

  have center_mem_face_iff : ∀ (s u t : Finset E),
      s.Nonempty → u.Nonempty → t.Nonempty → u ⊆ s → t ⊆ s →
      IsExposed ℝ (H s) (H u) →
      (u : Set E) = (s : Set E) ∩ H u → u ≠ s →
      (faceCenter t ∈ H u ↔ t ⊆ u) := by
    intro s u t hs hu ht hus hts hU hExact hproper
    constructor
    · intro hmem
      by_contra htu
      exact center_not_mem_face s u t hs hu ht hus hts hU hExact hproper htu hmem
    · intro htu
      exact (convexHull_mono htu) (center_mem_hull t ht)

  have sat_mono : ∀ (s : Finset E) (c₁ c₂ : Finset (Finset E)),
      c₁ ⊆ c₂ → IsSaturatedFaceChain s c₂ → IsSaturatedFaceChain s c₁ := by
    intro s c₁ c₂ hsub hc
    constructor
    · intro t ht
      exact hc.1 t (hsub ht)
    · intro t ht u hu
      exact hc.2 t (hsub ht) u (hsub hu)

  have sat_filter : ∀ (s : Finset E) (c : Finset (Finset E)) (u : Finset E),
      IsSaturatedFaceChain s c → u ⊆ s →
      IsExposed ℝ (H s) (H u) → (u : Set E) = (s : Set E) ∩ H u →
      IsSaturatedFaceChain u (c.filter fun t => t ⊆ u) := by
    intro s c u hc hus hU hExact
    constructor
    · intro t ht
      have htc : t ∈ c := (Finset.mem_filter.mp ht).1
      have htU : t ⊆ u := (Finset.mem_filter.mp ht).2
      obtain ⟨htne, hts, htExp, htExact⟩ := hc.1 t htc
      have htExpU : IsExposed ℝ (H u) (H t) := by
        apply htExp.mono
        · exact convexHull_mono hus
        · exact convexHull_mono htU
      refine ⟨htne, htU, htExpU, ?_⟩
      ext x
      constructor
      · intro hx
        exact ⟨htU hx, subset_convexHull ℝ (t : Set E) hx⟩
      · rintro ⟨hxU, hxT⟩
        have hxS : x ∈ (s : Set E) := hus hxU
        have hxExact : x ∈ (s : Set E) ∩ H t := ⟨hxS, hxT⟩
        rw [← htExact] at hxExact
        exact hxExact
    · intro t ht u hu
      exact hc.2 t (Finset.mem_filter.mp ht).1 u (Finset.mem_filter.mp hu).1

  have centers_subset_hull : ∀ (s : Finset E) (c : Finset (Finset E)) (u : Finset E),
      IsSaturatedFaceChain s c → (∀ t ∈ c, t ⊆ u) → Q c ⊆ H u := by
    intro s c u hc hsub
    change convexHull ℝ (faceCenter '' (c : Set (Finset E))) ⊆ H u
    apply convexHull_min ?_ (convex_convexHull ℝ (u : Set E))
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    obtain ⟨htne, -, -, -⟩ := hc.1 t ht
    exact convexHull_mono (by
      intro v hv
      exact hsub t ht hv) (center_mem_hull t htne)

  have functional_bound_hull : ∀ (s : Finset E) (l : StrongDual ℝ E) (a : ℝ),
      (∀ v ∈ s, l v ≤ a) → ∀ x ∈ H s, l x ≤ a := by
    intro s l a hle x hx
    obtain ⟨w, hw0, hw1, hw2⟩ := Finset.mem_convexHull'.1 hx
    have hlin : (∑ v ∈ s, w v * l v) = l x := by
      calc
        (∑ v ∈ s, w v * l v) = l (∑ v ∈ s, w v • v) := by
          simp [map_sum, map_smul, smul_eq_mul]
        _ = l x := congrArg l hw2
    calc
      l x = ∑ v ∈ s, w v * l v := hlin.symm
      _ ≤ ∑ v ∈ s, w v * a :=
        Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (hle v hv) (hw0 v hv)
      _ = a := by rw [← Finset.sum_mul, hw1]; simp

  have restrict_hull : ∀ (s : Finset E) (c : Finset (Finset E)) (u : Finset E),
      (hc : IsSaturatedFaceChain s c) → u.Nonempty → u ⊆ s →
      (hU : IsExposed ℝ (H s) (H u)) →
      (u : Set E) = (s : Set E) ∩ H u → u ≠ s →
      Q c ∩ H u = Q (c.filter fun t => t ⊆ u) := by
    intro s c u hc hu hus hU hExact hproper
    obtain ⟨l, a, hleS, hvalU, hout, hlevel, hcenter⟩ :=
      support_data s u (by
        obtain ⟨v, hv⟩ := hu
        exact ⟨v, hus hv⟩) hu hus hU hExact hproper
    let cU : Finset (Finset E) := c.filter fun t => t ⊆ u
    let T : Finset E := c.image faceCenter
    let U : Finset E := cU.image faceCenter
    have hUT : U ⊆ T := Finset.image_subset_image (Finset.filter_subset _ _)
    have hTle : ∀ v ∈ T, l v ≤ a := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨t, ht, rfl⟩
      obtain ⟨htne, hts, -, -⟩ := hc.1 t ht
      exact average_le t htne l a (fun z hz => hleS z (hts hz))
    have hTstrict : ∀ v ∈ T, v ∉ U → l v < a := by
      intro v hv hvU
      rcases Finset.mem_image.mp hv with ⟨t, ht, rfl⟩
      obtain ⟨htne, hts, -, -⟩ := hc.1 t ht
      have htu : ¬ t ⊆ u := by
        intro htu
        apply hvU
        exact Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, htu⟩, rfl⟩
      have houtT : ∃ z ∈ t, z ∉ u := by
        by_contra hn
        have htu' : t ⊆ u := by
          intro z hz
          by_contra hzu
          exact hn ⟨z, hz, hzu⟩
        exact htu htu'
      obtain ⟨z, hzt, hzu⟩ := houtT
      exact average_lt t htne l a (fun w hw => hleS w (hts hw)) z hzt
        (hout z (hts hzt) hzu)
    have hImageU : faceCenter '' (cU : Set (Finset E)) ⊆ H u := by
      intro x hx
      rcases hx with ⟨t, ht, rfl⟩
      have htc : t ∈ c := (Finset.mem_filter.mp ht).1
      have htu : t ⊆ u := (Finset.mem_filter.mp ht).2
      obtain ⟨htne, -, -, -⟩ := hc.1 t htc
      exact convexHull_mono htu (center_mem_hull t htne)
    have hImageUle : ∀ v ∈ U, l v = a := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨t, ht, rfl⟩
      have htc : t ∈ c := (Finset.mem_filter.mp ht).1
      have htu : t ⊆ u := (Finset.mem_filter.mp ht).2
      obtain ⟨htne, -, -, -⟩ := hc.1 t htc
      have hmem : faceCenter t ∈ H u := hImageU (Set.mem_image_of_mem _ ht)
      exact hlevel (faceCenter t) hmem
    apply Set.Subset.antisymm
    · intro x hx
      have hxT : x ∈ convexHull ℝ (T : Set E) := by
        simpa [T, Finset.coe_image] using hx.1
      obtain ⟨w, hw0, hw1, hw2⟩ := Finset.mem_convexHull'.1 hxT
      have hxa : l x = a := hlevel x hx.2
      have hlin : (∑ v ∈ T, w v * l v) = l x := by
        calc
          (∑ v ∈ T, w v * l v) = l (∑ v ∈ T, w v • v) := by
            simp [map_sum, map_smul, smul_eq_mul]
          _ = l x := congrArg l hw2
      have hdef : (∑ v ∈ T, w v * (a - l v)) = 0 := by
        calc
          (∑ v ∈ T, w v * (a - l v)) =
              a * (∑ v ∈ T, w v) - ∑ v ∈ T, w v * l v := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
            ring
          _ = 0 := by rw [hw1, hlin, hxa]; ring
      have hterms : ∀ v ∈ T, 0 ≤ w v * (a - l v) := by
        intro v hv
        exact mul_nonneg (hw0 v hv) (sub_nonneg.mpr (hTle v hv))
      have hzeros := (Finset.sum_eq_zero_iff_of_nonneg hterms).1 hdef
      have hzero : ∀ v ∈ T, v ∉ U → w v = 0 := by
        intro v hv hvU
        have hz := hzeros v hv
        have hlt := hTstrict v hv hvU
        rcases mul_eq_zero.mp hz with hwv | hval
        · exact hwv
        · exact False.elim ((ne_of_gt (sub_pos.mpr hlt)) hval)
      have hsum : (∑ v ∈ T, w v) = ∑ v ∈ U, w v := by
        exact (Finset.sum_subset hUT (by
          intro v hv hvU
          exact hzero v hv hvU)).symm
      have hvec : (∑ v ∈ T, w v • v) = ∑ v ∈ U, w v • v := by
        exact (Finset.sum_subset hUT (by
          intro v hv hvU
          simp [hzero v hv hvU])).symm
      have hxU : x ∈ convexHull ℝ (U : Set E) := by
        rw [Finset.mem_convexHull']
        refine ⟨w, ?_, ?_, ?_⟩
        · intro v hv
          exact hw0 v (hUT hv)
        · calc
            (∑ v ∈ U, w v) = ∑ v ∈ T, w v := hsum.symm
            _ = 1 := hw1
        · calc
            (∑ v ∈ U, w v • v) = ∑ v ∈ T, w v • v := hvec.symm
            _ = x := hw2
      simpa [Q, cU, U, Finset.coe_image] using hxU
    · intro x hx
      constructor
      · change x ∈ convexHull ℝ (faceCenter '' (c : Set (Finset E)))
        exact convexHull_mono (Set.image_mono (show (cU : Set (Finset E)) ⊆ c from by
          intro t ht
          exact (Finset.mem_filter.mp ht).1)) (by
            simpa [Q, cU, Finset.coe_image] using hx)
      · exact convexHull_min hImageU (convex_convexHull ℝ (u : Set E)) (by
          simpa [Q, cU, Finset.coe_image] using hx)

  have max_face : ∀ (s : Finset E) (c : Finset (Finset E)),
      IsSaturatedFaceChain s c → c.Nonempty →
      ∃ u ∈ c, ∀ t ∈ c, t ⊆ u := by
    intro s c hc hcne
    obtain ⟨u, hu, hcard⟩ := Finset.exists_max_image c Finset.card hcne
    refine ⟨u, hu, ?_⟩
    intro t ht
    rcases hc.2 t ht u hu with htu | hut
    · exact htu
    · have htc : t.card ≤ u.card := hcard t ht
      have heq : u = t := Finset.eq_of_subset_of_card_le hut htc
      exact heq.symm ▸ Finset.Subset.rfl

  have image_insert : ∀ (u : Finset E) (c : Finset (Finset E)),
      faceCenter '' ((insert u c : Finset (Finset E)) : Set (Finset E)) =
        insert (faceCenter u) (faceCenter '' (c : Set (Finset E))) := by
    intro u c
    ext x
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_insert, Set.mem_insert_iff]
    constructor
    · rintro ⟨t, rfl | ht, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨t, ht, rfl⟩
    · rintro (hx | ⟨t, ht, rfl⟩)
      · exact ⟨u, Or.inl rfl, hx.symm⟩
      · exact ⟨t, Or.inr ht, rfl⟩

  have erase_inter : ∀ (s : Finset E) (c d : Finset (Finset E)),
      s ∈ c → s ∈ d →
      c ∩ d = insert s (c.erase s ∩ d.erase s) := by
    intro s c d hcs hds
    ext t
    by_cases hts : t = s <;> simp [hts, hcs, hds]

  have main : ∀ n : ℕ, ∀ s : Finset E, s.card = n →
      ∀ c d, IsSaturatedFaceChain s c → IsSaturatedFaceChain s d →
      Q c ∩ Q d = Q (c ∩ d) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih s hcard c d hc hd
    by_cases hc0 : c = ∅
    · subst c
      simp [Q]
    by_cases hd0 : d = ∅
    · subst d
      simp [Q]
    have hcne : c.Nonempty := Finset.nonempty_iff_ne_empty.mpr hc0
    have hdne : d.Nonempty := Finset.nonempty_iff_ne_empty.mpr hd0
    by_cases hcs : s ∈ c
    · by_cases hds : s ∈ d
      · let c' : Finset (Finset E) := c.erase s
        let d' : Finset (Finset E) := d.erase s
        have hc' : IsSaturatedFaceChain s c' :=
          sat_mono s c' c (Finset.erase_subset _ _) hc
        have hd' : IsSaturatedFaceChain s d' :=
          sat_mono s d' d (Finset.erase_subset _ _) hd
        have hcDecomp : c = insert s c' := by
          exact (Finset.insert_erase hcs).symm
        have hdDecomp : d = insert s d' := by
          exact (Finset.insert_erase hds).symm
        have hImgC : faceCenter '' (c : Set (Finset E)) =
            insert (faceCenter s) (faceCenter '' (c' : Set (Finset E))) := by
          rw [hcDecomp, image_insert]
        have hImgD : faceCenter '' (d : Set (Finset E)) =
            insert (faceCenter s) (faceCenter '' (d' : Set (Finset E))) := by
          rw [hdDecomp, image_insert]
        have hcommon : c ∩ d = insert s (c' ∩ d') := by
          simpa [c', d'] using erase_inter s c d hcs hds
        have hImgCommon : faceCenter '' ((c ∩ d : Finset (Finset E)) : Set (Finset E)) =
            insert (faceCenter s) (faceCenter '' ((c' ∩ d' : Finset (Finset E)) : Set (Finset E))) := by
          rw [hcommon, image_insert]
        have lowerInter : Q c' ∩ Q d' = Q (c' ∩ d') := by
          by_cases hc'e : c' = ∅
          · simp [Q, hc'e]
          · have hc'ne : c'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hc'e
            obtain ⟨u, huC', hmaxC'⟩ := max_face s c' hc' hc'ne
            have huData := hc'.1 u huC'
            obtain ⟨hune, hus, hU, hUexact⟩ := huData
            have huNeS : u ≠ s := by
              intro heq
              subst u
              exact (Finset.mem_erase.mp huC').1 rfl
            have huStrict : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hus, huNeS⟩
            have huCard : u.card < n := by
              rw [← hcard]
              exact Finset.card_lt_card huStrict
            let cU : Finset (Finset E) := c'.filter fun t => t ⊆ u
            let dU : Finset (Finset E) := d'.filter fun t => t ⊆ u
            have hcU : IsSaturatedFaceChain u cU := sat_filter s c' u hc' hus hU hUexact
            have hdU : IsSaturatedFaceChain u dU := sat_filter s d' u hd' hus hU hUexact
            have hcUeq : cU = c' := by
              apply Finset.filter_eq_self.mpr
              exact hmaxC'
            have hcUsub : ∀ t ∈ c', t ⊆ u := hmaxC'
            have hCsub : Q c' ⊆ H u := centers_subset_hull s c' u hc' hcUsub
            have hRestrD : Q d' ∩ H u = Q dU :=
              restrict_hull s d' u hd' hune hus hU hUexact huNeS
            have hcommonU : cU ∩ dU = c' ∩ d' := by
              ext t
              simp only [Finset.mem_inter, Finset.mem_filter, cU, dU]
              constructor
              · rintro ⟨⟨htc, _⟩, ⟨htd, _⟩⟩
                exact ⟨htc, htd⟩
              · rintro ⟨htc, htd⟩
                exact ⟨⟨htc, hmaxC' t htc⟩, ⟨htd, hmaxC' t htc⟩⟩
            calc
              Q c' ∩ Q d' = Q c' ∩ (H u ∩ Q d') := by
                ext x
                simp only [Set.mem_inter_iff]
                constructor
                · rintro ⟨hxC, hxD⟩
                  exact ⟨hxC, ⟨hCsub hxC, hxD⟩⟩
                · rintro ⟨hxC, ⟨_, hxD⟩⟩
                  exact ⟨hxC, hxD⟩
              _ = Q cU ∩ Q dU := by
                rw [Set.inter_comm (H u) (Q d'), hRestrD, hcUeq]
              _ = Q (cU ∩ dU) := ih u.card huCard u rfl cU dU hcU hdU
              _ = Q (c' ∩ d') := by rw [hcommonU]
        by_cases hc'e : c' = ∅
        · have hQc : Q c = {faceCenter s} := by
            change convexHull ℝ (faceCenter '' (c : Set (Finset E))) = {faceCenter s}
            rw [hImgC]
            simp [hc'e]
          have hceq : c ∩ d = {s} := by
            rw [hcommon]
            simp [hc'e]
          have hbD : faceCenter s ∈ Q d := by
            exact subset_convexHull ℝ _ ⟨s, hds, rfl⟩
          have hleft : Q c ∩ Q d = {faceCenter s} := by
            rw [hQc]
            ext x
            constructor
            · intro hx
              exact hx.1
            · intro hx
              have hxb : x = faceCenter s := by simpa using hx
              subst x
              exact ⟨by simp, hbD⟩
          rw [hleft, hceq]
          simp [Q]
        · by_cases hd'e : d' = ∅
          · have hQd : Q d = {faceCenter s} := by
              change convexHull ℝ (faceCenter '' (d : Set (Finset E))) = {faceCenter s}
              rw [hImgD]
              simp [hd'e]
            have hdeq : c ∩ d = {s} := by
              rw [hcommon]
              simp [hd'e]
            have hbC : faceCenter s ∈ Q c := by
              exact subset_convexHull ℝ _ ⟨s, hcs, rfl⟩
            have hleft : Q c ∩ Q d = {faceCenter s} := by
              rw [hQd]
              ext x
              constructor
              · rintro ⟨_, hx⟩
                exact hx
              · intro hx
                have hxb : x = faceCenter s := by simpa using hx
                subst x
                exact ⟨hbC, by simp⟩
            rw [hleft, hdeq]
            simp [Q]
          · have hc'ne : c'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hc'e
            have hd'ne : d'.Nonempty := Finset.nonempty_iff_ne_empty.mpr hd'e
            have hHullC : Q c = convexJoin ℝ {faceCenter s} (Q c') := by
              change convexHull ℝ (faceCenter '' (c : Set (Finset E))) =
                convexJoin ℝ {faceCenter s}
                  (convexHull ℝ (faceCenter '' (c' : Set (Finset E))))
              rw [hImgC, convexHull_insert (by
                obtain ⟨t, ht⟩ := hc'ne
                exact ⟨faceCenter t, Set.mem_image_of_mem _ ht⟩)]
            have hHullD : Q d = convexJoin ℝ {faceCenter s} (Q d') := by
              change convexHull ℝ (faceCenter '' (d : Set (Finset E))) =
                convexJoin ℝ {faceCenter s}
                  (convexHull ℝ (faceCenter '' (d' : Set (Finset E))))
              rw [hImgD, convexHull_insert (by
                obtain ⟨t, ht⟩ := hd'ne
                exact ⟨faceCenter t, Set.mem_image_of_mem _ ht⟩)]
            have hleftSubset : Q c ∩ Q d ⊆ Q (c ∩ d) := by
              intro x hx
              rw [hHullC, hHullD] at hx
              obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.mp hx.1
              obtain ⟨b, hb, z, hz, hxz⟩ := mem_convexJoin.mp hx.2
              have ha' : a = faceCenter s := by simpa using ha
              have hb' : b = faceCenter s := by simpa using hb
              subst a
              subst b
              by_cases hxb : x = faceCenter s
              · subst x
                exact subset_convexHull ℝ _ ⟨s, Finset.mem_inter.mpr ⟨hcs, hds⟩, rfl⟩
              have hyseg : x ∈ segment ℝ (faceCenter s) y := hxy
              have hzseg : x ∈ segment ℝ (faceCenter s) z := hxz
              have hysegOrig : x ∈ segment ℝ (faceCenter s) y := hyseg
              rw [segment_eq_image_lineMap] at hyseg hzseg
              obtain ⟨t, ht, hxt⟩ := hyseg
              obtain ⟨v, hv, hxv⟩ := hzseg
              have hxt' : x = (1 - t) • faceCenter s + t • y := by
                simpa only [AffineMap.lineMap_apply_module] using hxt.symm
              have hxv' : x = (1 - v) • faceCenter s + v • z := by
                simpa only [AffineMap.lineMap_apply_module] using hxv.symm
              rcases ht with ⟨ht0, ht1⟩
              rcases hv with ⟨hv0, hv1⟩
              have htpos : 0 < t := by
                by_contra hn
                have htzero : t = 0 := le_antisymm (le_of_not_gt hn) ht0
                subst t
                have : x = faceCenter s := by simpa using hxt'
                exact hxb this
              have hvpos : 0 < v := by
                by_contra hn
                have hvzero : v = 0 := le_antisymm (le_of_not_gt hn) hv0
                subst v
                have : x = faceCenter s := by simpa using hxv'
                exact hxb this
              obtain ⟨u, huC', hmaxC'⟩ := max_face s c' hc' hc'ne
              obtain ⟨w, hwD', hmaxD'⟩ := max_face s d' hd' hd'ne
              have huData := hc'.1 u huC'
              have hwData := hd'.1 w hwD'
              obtain ⟨hune, hus, hU, hUexact⟩ := huData
              obtain ⟨hwne, hws, hW, hWexact⟩ := hwData
              have huNeS : u ≠ s := by
                intro heq
                subst u
                exact (Finset.mem_erase.mp huC').1 rfl
              have hwNeS : w ≠ s := by
                intro heq
                subst w
                exact (Finset.mem_erase.mp hwD').1 rfl
              have hhu : Q c' ⊆ H u := centers_subset_hull s c' u hc' hmaxC'
              have hhw : Q d' ⊆ H w := centers_subset_hull s d' w hd' hmaxD'
              have hyU : y ∈ H u := hhu hy
              have hzW : z ∈ H w := hhw hz
              have hcAllS : ∀ t ∈ c', t ⊆ s := by
                intro t ht
                exact (hc'.1 t ht).2.1
              have hdAllS : ∀ t ∈ d', t ⊆ s := by
                intro t ht
                exact (hd'.1 t ht).2.1
              have hyS : y ∈ H s := centers_subset_hull s c' s hc' hcAllS hy
              have hzS : z ∈ H s := centers_subset_hull s d' s hd' hdAllS hz
              have hdataU := support_data s u (by
                obtain ⟨q, hq⟩ := hune
                exact ⟨q, hus hq⟩) hune hus hU hUexact huNeS
              obtain ⟨lU, aU, hleU, hvalU, houtU, hlevelU, hcenterU⟩ := hdataU
              have hdataW := support_data s w (by
                obtain ⟨q, hq⟩ := hwne
                exact ⟨q, hws hq⟩) hwne hws hW hWexact hwNeS
              obtain ⟨lW, aW, hleW, hvalW, houtW, hlevelW, hcenterW⟩ := hdataW
              have hlyU : lU y = aU := hlevelU y hyU
              have hlzU : lU z ≤ aU := functional_bound_hull s lU aU hleU z hzS
              have hlyW : lW y ≤ aW := functional_bound_hull s lW aW hleW y hyS
              have hlzW : lW z = aW := hlevelW z hzW
              have hscalarU : (1 - t) * lU (faceCenter s) + t * lU y =
                  (1 - v) * lU (faceCenter s) + v * lU z := by
                have h := congrArg lU (hxt'.symm.trans hxv')
                simpa only [map_add, map_smul, smul_eq_mul] using h
              have hscalarW : (1 - t) * lW (faceCenter s) + t * lW y =
                  (1 - v) * lW (faceCenter s) + v * lW z := by
                have h := congrArg lW (hxt'.symm.trans hxv')
                simpa only [map_add, map_smul, smul_eq_mul] using h
              have hDeltaU : 0 < aU - lU (faceCenter s) := sub_pos.mpr hcenterU
              have htermU : v * lU z ≤ v * aU :=
                mul_le_mul_of_nonneg_left hlzU (le_of_lt hvpos)
              have hprodU : t * (aU - lU (faceCenter s)) ≤
                  v * (aU - lU (faceCenter s)) := by
                rw [hlyU] at hscalarU
                nlinarith [hscalarU, htermU]
              have htv : t ≤ v := le_of_mul_le_mul_right hprodU hDeltaU
              have hDeltaW : 0 < aW - lW (faceCenter s) := sub_pos.mpr hcenterW
              have htermW : t * lW y ≤ t * aW :=
                mul_le_mul_of_nonneg_left hlyW (le_of_lt htpos)
              have hprodW : v * (aW - lW (faceCenter s)) ≤
                  t * (aW - lW (faceCenter s)) := by
                rw [hlzW] at hscalarW
                nlinarith [hscalarW, htermW]
              have hvt : v ≤ t := le_of_mul_le_mul_right hprodW hDeltaW
              have htvEq : t = v := le_antisymm htv hvt
              have hvec : (1 - t) • faceCenter s + t • y =
                  (1 - t) • faceCenter s + t • z := by
                have hvec' := hxt'.symm.trans hxv'
                rw [← htvEq] at hvec'
                exact hvec'
              have hsmul : t • y = t • z := add_left_cancel hvec
              have hyz : y = z := by
                calc
                  y = t⁻¹ • (t • y) := by
                    rw [smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
                  _ = t⁻¹ • (t • z) := congrArg (fun q : E => t⁻¹ • q) hsmul
                  _ = z := by
                    rw [smul_smul, inv_mul_cancel₀ htpos.ne', one_smul]
              have hyShared : y ∈ Q (c' ∩ d') := by
                rw [← lowerInter]
                exact ⟨hy, by simpa [hyz] using hz⟩
              change x ∈ convexHull ℝ
                (faceCenter '' ((c ∩ d : Finset (Finset E)) : Set (Finset E)))
              rw [hImgCommon]
              exact ((convex_convexHull ℝ
                (insert (faceCenter s)
                  (faceCenter '' ((c' ∩ d' : Finset (Finset E)) : Set (Finset E))))).segment_subset
                (subset_convexHull ℝ _ (by simp))
                (convexHull_mono (Set.subset_insert _ _) hyShared)) hysegOrig
            have hrightSubset : Q (c ∩ d) ⊆ Q c ∩ Q d := by
              intro x hx
              constructor
              · exact convexHull_mono (Set.image_mono Finset.inter_subset_left) hx
              · exact convexHull_mono (Set.image_mono Finset.inter_subset_right) hx
            exact Set.Subset.antisymm hleftSubset hrightSubset
      · obtain ⟨u, huD, hmaxD⟩ := max_face s d hd hdne
        obtain ⟨hune, hus, hU, hUexact⟩ := hd.1 u huD
        have huNeS : u ≠ s := by
          intro heq
          subst u
          exact hds huD
        have huStrict : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hus, huNeS⟩
        have huCard : u.card < n := by
          rw [← hcard]
          exact Finset.card_lt_card huStrict
        let cU : Finset (Finset E) := c.filter fun t => t ⊆ u
        let dU : Finset (Finset E) := d.filter fun t => t ⊆ u
        have hcU : IsSaturatedFaceChain u cU := sat_filter s c u hc hus hU hUexact
        have hdU0 : IsSaturatedFaceChain u dU := sat_filter s d u hd hus hU hUexact
        have hdUeq : dU = d := by
          apply Finset.filter_eq_self.mpr
          exact hmaxD
        have hRestrC : Q c ∩ H u = Q cU :=
          restrict_hull s c u hc hune hus hU hUexact huNeS
        have hDsub : Q d ⊆ H u := centers_subset_hull s d u hd hmaxD
        have hcommonU : cU ∩ dU = c ∩ d := by
          ext t
          simp only [Finset.mem_inter, Finset.mem_filter, cU, dU]
          constructor
          · rintro ⟨⟨htc, _⟩, ⟨htd, _⟩⟩
            exact ⟨htc, htd⟩
          · rintro ⟨htc, htd⟩
            exact ⟨⟨htc, hmaxD t htd⟩, ⟨htd, hmaxD t htd⟩⟩
        calc
          Q c ∩ Q d = (Q c ∩ H u) ∩ Q d := by
            ext x
            simp only [Set.mem_inter_iff]
            constructor
            · rintro ⟨hxC, hxD⟩
              exact ⟨⟨hxC, hDsub hxD⟩, hxD⟩
            · rintro ⟨⟨hxC, _⟩, hxD⟩
              exact ⟨hxC, hxD⟩
          _ = Q cU ∩ Q dU := by rw [hRestrC, hdUeq]
          _ = Q (cU ∩ dU) := ih u.card huCard u rfl cU dU hcU hdU0
          _ = Q (c ∩ d) := by rw [hcommonU]
    · obtain ⟨u, huC, hmaxC⟩ := max_face s c hc hcne
      obtain ⟨hune, hus, hU, hUexact⟩ := hc.1 u huC
      have huNeS : u ≠ s := by
        intro heq
        subst u
        exact hcs huC
      have huStrict : u ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hus, huNeS⟩
      have huCard : u.card < n := by
        rw [← hcard]
        exact Finset.card_lt_card huStrict
      let cU : Finset (Finset E) := c.filter fun t => t ⊆ u
      let dU : Finset (Finset E) := d.filter fun t => t ⊆ u
      have hcU0 : IsSaturatedFaceChain u cU := sat_filter s c u hc hus hU hUexact
      have hdU : IsSaturatedFaceChain u dU := sat_filter s d u hd hus hU hUexact
      have hcUeq : cU = c := by
        apply Finset.filter_eq_self.mpr
        exact hmaxC
      have hRestrD : Q d ∩ H u = Q dU :=
        restrict_hull s d u hd hune hus hU hUexact huNeS
      have hCsub : Q c ⊆ H u := centers_subset_hull s c u hc hmaxC
      have hcommonU : cU ∩ dU = c ∩ d := by
        ext t
        simp only [Finset.mem_inter, Finset.mem_filter, cU, dU]
        constructor
        · rintro ⟨⟨htc, _⟩, ⟨htd, _⟩⟩
          exact ⟨htc, htd⟩
        · rintro ⟨htc, htd⟩
          exact ⟨⟨htc, hmaxC t htc⟩, ⟨htd, hmaxC t htc⟩⟩
      calc
        Q c ∩ Q d = Q c ∩ (Q d ∩ H u) := by
          ext x
          simp only [Set.mem_inter_iff]
          constructor
          · rintro ⟨hxC, hxD⟩
            exact ⟨hxC, ⟨hxD, hCsub hxC⟩⟩
          · rintro ⟨hxC, ⟨hxD, _⟩⟩
            exact ⟨hxC, hxD⟩
        _ = Q cU ∩ Q dU := by rw [hRestrD, ← hcUeq]
        _ = Q (cU ∩ dU) := ih u.card huCard u rfl cU dU hcU0 hdU
        _ = Q (c ∩ d) := by rw [hcommonU]
  exact main s.card s rfl c d hc hd
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SaturatedFaceChainIntersection
