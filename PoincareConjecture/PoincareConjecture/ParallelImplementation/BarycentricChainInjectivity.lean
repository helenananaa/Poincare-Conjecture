import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BarycentricChainInjectivity
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Nonnegative weights supported on inclusion chains of nonempty subsets
are determined by their actual barycentric coordinates. No normalization is assumed. -/
theorem chain_weights_eq_of_barycenter_eq
    (w z : Finset V → ℝ)
    (hw0 : w ∅ = 0) (hz0 : z ∅ = 0)
    (hw : ∀ s, 0 ≤ w s) (hz : ∀ s, 0 ≤ z s)
    (hwchain : ∀ a b, 0 < w a → 0 < w b → a ⊆ b ∨ b ⊆ a)
    (hzchain : ∀ a b, 0 < z a → 0 < z b → a ⊆ b ∨ b ⊆ a)
    (hcoords : ∀ v : V,
      (∑ s : Finset V, w s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0)) =
      (∑ s : Finset V, z s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0))) :
    w = z :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let term : (Finset V → ℝ) → V → Finset V → ℝ := fun f v s =>
    f s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0)
  let coord : (Finset V → ℝ) → V → ℝ := fun f v =>
    ∑ s : Finset V, term f v s
  let supp : (Finset V → ℝ) → Finset (Finset V) := fun f =>
    Finset.univ.filter (fun s : Finset V => 0 < f s)
  let cnt : (Finset V → ℝ) → ℕ := fun f => (supp f).card
  change ∀ v, coord w v = coord z v at hcoords

  have maxSupport : ∀ f : Finset V → ℝ,
      (∀ s, 0 ≤ f s) →
      (∀ a b, 0 < f a → 0 < f b → a ⊆ b ∨ b ⊆ a) →
      (∃ s, 0 < f s) →
      ∃ S, 0 < f S ∧ ∀ t, 0 < f t → t ⊆ S := by
    intro f hf hc hex
    let A : Finset (Finset V) := Finset.univ.filter (fun s => 0 < f s)
    have hA : A.Nonempty := by
      rcases hex with ⟨s, hs⟩
      exact ⟨s, by simp [A, hs]⟩
    obtain ⟨S, hSmem, hmax⟩ := Finset.exists_max_image A Finset.card hA
    refine ⟨S, (Finset.mem_filter.mp hSmem).2, ?_⟩
    intro t ht
    have hS : 0 < f S := (Finset.mem_filter.mp hSmem).2
    rcases hc t S ht hS with h | h
    · exact h
    · have htm : t ∈ A := by simp [A, ht]
      have hcard : t.card ≤ S.card := hmax t htm
      have heq : S = t := Finset.eq_of_subset_of_card_le h hcard
      simpa [heq]

  have coordPos : ∀ f : Finset V → ℝ,
      f ∅ = 0 →
      (∀ s, 0 ≤ f s) →
      (∀ a b, 0 < f a → 0 < f b → a ⊆ b ∨ b ⊆ a) →
      ∀ S, 0 < f S → (∀ t, 0 < f t → t ⊆ S) →
      ∀ v, 0 < coord f v ↔ v ∈ S := by
    intro f hfempty hf hc S hS hmax v
    have hnonneg : ∀ s ∈ (Finset.univ : Finset (Finset V)), 0 ≤ term f v s := by
      intro s hs
      dsimp [term]
      apply mul_nonneg (hf s)
      apply mul_nonneg
      · exact inv_nonneg.mpr (Nat.cast_nonneg _)
      · split_ifs <;> norm_num
    constructor
    · intro h
      have hpos := (Finset.sum_pos_iff_of_nonneg hnonneg).mp (by simpa [coord] using h)
      rcases hpos with ⟨t, ht, hterm⟩
      have htpos : 0 < f t := by
        by_contra hn
        have hzero : f t = 0 := le_antisymm (not_lt.mp hn) (hf t)
        simp [term, hzero] at hterm
      have hvt : v ∈ t := by
        by_contra hv
        simp [term, hv] at hterm
      exact hmax t htpos hvt
    · intro hv
      apply (Finset.sum_pos_iff_of_nonneg hnonneg).mpr
      refine ⟨S, Finset.mem_univ S, ?_⟩
      have hSne : S.Nonempty := by
        by_contra h
        have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
        subst S
        rw [hfempty] at hS
        norm_num at hS
      have hcard : 0 < S.card := Finset.card_pos.mpr hSne
      simp only [term, if_pos hv, mul_one]
      exact mul_pos hS (inv_pos.mpr (Nat.cast_pos.mpr hcard))

  have activeCoord : ∀ f : Finset V → ℝ,
      f ∅ = 0 →
      (∀ s, 0 ≤ f s) →
      (∀ a b, 0 < f a → 0 < f b → a ⊆ b ∨ b ⊆ a) →
      ((∃ s, 0 < f s) ↔ ∃ v, 0 < coord f v) := by
    intro f hfempty hf hc
    constructor
    · intro h
      obtain ⟨S, hS, hmax⟩ := maxSupport f hf hc h
      have hSne : S.Nonempty := by
        by_contra hne
        have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        subst S
        rw [hfempty] at hS
        norm_num at hS
      obtain ⟨v, hv⟩ := hSne
      exact ⟨v, (coordPos f hfempty hf hc S hS hmax v).2 hv⟩
    · rintro ⟨v, hv⟩
      have hnonneg : ∀ s ∈ (Finset.univ : Finset (Finset V)), 0 ≤ term f v s := by
        intro s hs
        dsimp [term]
        apply mul_nonneg (hf s)
        apply mul_nonneg
        · exact inv_nonneg.mpr (Nat.cast_nonneg _)
        · split_ifs <;> norm_num
      have hpos := (Finset.sum_pos_iff_of_nonneg hnonneg).mp (by simpa [coord] using hv)
      rcases hpos with ⟨s, hs, hterm⟩
      have hspos : 0 < f s := by
        by_contra hn
        have hzero : f s = 0 := le_antisymm (not_lt.mp hn) (hf s)
        simp [term, hzero] at hterm
      exact ⟨s, hspos⟩

  have coordLower : ∀ f : Finset V → ℝ,
      (∀ s, 0 ≤ f s) → ∀ S, 0 < f S → ∀ v, v ∈ S →
      f S * (S.card : ℝ)⁻¹ ≤ coord f v := by
    intro f hf S hS v hv
    have hle : term f v S ≤ coord f v := by
      change term f v S ≤ ∑ s : Finset V, term f v s
      exact Finset.single_le_sum (fun s hs => by
        dsimp [term]
        apply mul_nonneg (hf s)
        apply mul_nonneg
        · exact inv_nonneg.mpr (Nat.cast_nonneg _)
        · split_ifs <;> norm_num) (Finset.mem_univ S)
    simpa [term, hv] using hle

  have coordWitness : ∀ f : Finset V → ℝ,
      f ∅ = 0 →
      (∀ s, 0 ≤ f s) →
      (∀ a b, 0 < f a → 0 < f b → a ⊆ b ∨ b ⊆ a) →
      ∀ S, 0 < f S → (∀ t, 0 < f t → t ⊆ S) →
      ∃ v, v ∈ S ∧ coord f v = f S * (S.card : ℝ)⁻¹ := by
    intro f hfempty hf hc S hS hmax
    let A : Finset (Finset V) := (Finset.univ.filter (fun t => 0 < f t)).filter (fun t => t ≠ S)
    have hSne : S.Nonempty := by
      by_contra hne
      have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      rw [hfempty] at hS
      norm_num at hS
    have havoid : ∃ v, v ∈ S ∧ ∀ t, 0 < f t → t ≠ S → v ∉ t := by
      by_cases hA : A.Nonempty
      · obtain ⟨T, hTm, hTmax⟩ := Finset.exists_max_image A Finset.card hA
        have hTpos : 0 < f T := (Finset.mem_filter.mp (Finset.mem_filter.mp hTm).1).2
        have hTne : T ≠ S := (Finset.mem_filter.mp hTm).2
        have hTS : T ⊆ S := hmax T hTpos
        have hnotST : ¬ S ⊆ T := by
          intro hST
          exact hTne (Finset.Subset.antisymm hTS hST)
        obtain ⟨v, hvS, hvT⟩ := Finset.not_subset.mp hnotST
        have hsubT : ∀ t, 0 < f t → t ≠ S → t ⊆ T := by
          intro t ht htS
          rcases hc t T ht hTpos with htT | hTt
          · exact htT
          · have htm : t ∈ A := by simp [A, ht, htS]
            have hcard : t.card ≤ T.card := hTmax t htm
            have heq : T = t := Finset.eq_of_subset_of_card_le hTt hcard
            simpa [heq]
        refine ⟨v, hvS, ?_⟩
        intro t ht htS hvt
        exact hvT (hsubT t ht htS hvt)
      · obtain ⟨v, hv⟩ := hSne
        refine ⟨v, hv, ?_⟩
        intro t ht htS hvt
        have htm : t ∈ A := by simp [A, ht, htS]
        exact (hA ⟨t, htm⟩).elim
    rcases havoid with ⟨v, hvS, hvavoid⟩
    refine ⟨v, hvS, ?_⟩
    have hsum : (∑ t : Finset V, term f v t) = term f v S := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset (Finset V)) (fun t => term f v t)
        (Finset.mem_univ S)]
      have hzero : ∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term f v t = 0 := by
        apply Finset.sum_eq_zero
        intro t ht
        have htS : t ≠ S := (Finset.mem_erase.mp ht).1
        by_cases htp : 0 < f t
        · have hvt : v ∉ t := hvavoid t htp htS
          simp [term, hvt]
        · have htf : f t = 0 := le_antisymm (not_lt.mp htp) (hf t)
          simp [term, htf]
      rw [hzero, zero_add]
    rw [show coord f v = ∑ t : Finset V, term f v t by rfl, hsum]
    simp [term, hvS]

  have countErase : ∀ (f : Finset V → ℝ) (S : Finset V),
      0 < f S → cnt (fun t => if t = S then 0 else f t) + 1 = cnt f := by
    intro f S hS
    let f' : Finset V → ℝ := fun t => if t = S then 0 else f t
    have hfilter : supp f' = (supp f).erase S := by
      ext t
      by_cases ht : t = S
      · subst t
        simp [supp, f', hS]
      · simp [supp, f', ht]
    have hmem : S ∈ supp f := by simp [supp, hS]
    have hcard : 0 < (supp f).card := Finset.card_pos.mpr ⟨S, hmem⟩
    change (supp f').card + 1 = (supp f).card
    rw [hfilter, Finset.card_erase_of_mem hmem]
    omega

  have aux : ∀ n (w z : Finset V → ℝ), cnt w + cnt z = n →
      w ∅ = 0 → z ∅ = 0 →
      (∀ s, 0 ≤ w s) → (∀ s, 0 ≤ z s) →
      (∀ a b, 0 < w a → 0 < w b → a ⊆ b ∨ b ⊆ a) →
      (∀ a b, 0 < z a → 0 < z b → a ⊆ b ∨ b ⊆ a) →
      (∀ v, coord w v = coord z v) → w = z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w z hn hw0 hz0 hw hz hwchain hzchain hcoords
      have hactive : (∃ s, 0 < w s) ↔ ∃ s, 0 < z s := by
        rw [activeCoord w hw0 hw hwchain, activeCoord z hz0 hz hzchain]
        constructor
        · rintro ⟨v, hv⟩
          exact ⟨v, by simpa [hcoords v] using hv⟩
        · rintro ⟨v, hv⟩
          exact ⟨v, by simpa [hcoords v] using hv⟩
      by_cases hwa : ∃ s, 0 < w s
      · have hza : ∃ s, 0 < z s := hactive.mp hwa
        obtain ⟨S, hSw, hmaxW⟩ := maxSupport w hw hwchain hwa
        obtain ⟨T, hTz, hmaxZ⟩ := maxSupport z hz hzchain hza
        have hST : S = T := by
          apply Finset.ext
          intro v
          have hpw := coordPos w hw0 hw hwchain S hSw hmaxW v
          have hpz := coordPos z hz0 hz hzchain T hTz hmaxZ v
          constructor
          · intro hv
            have hpos : 0 < coord w v := hpw.mpr hv
            have hposz : 0 < coord z v := by simpa [hcoords v] using hpos
            exact hpz.mp hposz
          · intro hv
            have hpos : 0 < coord z v := hpz.mpr hv
            have hposw : 0 < coord w v := by simpa [hcoords v] using hpos
            exact hpw.mp hposw
        have hTzS : 0 < z S := by simpa [hST] using hTz
        have hmaxZ' : ∀ t, 0 < z t → t ⊆ S := by simpa [hST] using hmaxZ
        obtain ⟨vw, hvw, hwvw⟩ := coordWitness w hw0 hw hwchain S hSw hmaxW
        obtain ⟨vz, hvz, hzvz⟩ := coordWitness z hz0 hz hzchain S hTzS hmaxZ'
        have hSne : S.Nonempty := by
          by_contra h
          have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
          rw [he, hw0] at hSw
          norm_num at hSw
        have hdenNat : 0 < S.card := Finset.card_pos.mpr hSne
        have hden : (0 : ℝ) < (S.card : ℝ)⁻¹ := by positivity
        have hcWZ : w S * (S.card : ℝ)⁻¹ = z S * (S.card : ℝ)⁻¹ := by
          apply le_antisymm
          · calc
              w S * (S.card : ℝ)⁻¹ ≤ coord w vz := coordLower w hw S hSw vz hvz
              _ = coord z vz := hcoords vz
              _ = z S * (S.card : ℝ)⁻¹ := hzvz
          · calc
              z S * (S.card : ℝ)⁻¹ ≤ coord z vw := coordLower z hz S hTzS vw hvw
              _ = coord w vw := (hcoords vw).symm
              _ = w S * (S.card : ℝ)⁻¹ := hwvw
        have hWS : w S = z S := mul_right_cancel₀ (ne_of_gt hden) hcWZ
        let w' : Finset V → ℝ := fun t => if t = S then 0 else w t
        let z' : Finset V → ℝ := fun t => if t = S then 0 else z t
        have hcW : cnt w' + 1 = cnt w := countErase w S hSw
        have hcZ : cnt z' + 1 = cnt z := countErase z S hTzS
        have hn' : cnt w' + cnt z' < n := by omega
        have hw'0 : w' ∅ = 0 := by
          have hSne : S ≠ ∅ := by
            intro h
            rw [h, hw0] at hSw
            norm_num at hSw
          simp [w', hw0, hSne]
        have hz'0 : z' ∅ = 0 := by
          have hSne : S ≠ ∅ := by
            intro h
            rw [h, hz0] at hTzS
            norm_num at hTzS
          simp [z', hz0, hSne]
        have hw' : ∀ t, 0 ≤ w' t := by
          intro t
          by_cases ht : t = S <;> simp [w', ht, hw]
        have hz' : ∀ t, 0 ≤ z' t := by
          intro t
          by_cases ht : t = S <;> simp [z', ht, hz]
        have hw'chain : ∀ a b, 0 < w' a → 0 < w' b → a ⊆ b ∨ b ⊆ a := by
          intro a b ha hb
          by_cases haS : a = S
          · subst a
            simp [w'] at ha
          · by_cases hbS : b = S
            · subst b
              simp [w'] at hb
            · exact hwchain a b (by simpa [w', haS] using ha) (by simpa [w', hbS] using hb)
        have hz'chain : ∀ a b, 0 < z' a → 0 < z' b → a ⊆ b ∨ b ⊆ a := by
          intro a b ha hb
          by_cases haS : a = S
          · subst a
            simp [z'] at ha
          · by_cases hbS : b = S
            · subst b
              simp [z'] at hb
            · exact hzchain a b (by simpa [z', haS] using ha) (by simpa [z', hbS] using hb)
        have hcoords' : ∀ v, coord w' v = coord z' v := by
          intro v
          have hsumW : coord w' v = ∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term w v t := by
            have hsumErase :
                (∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term w' v t) =
                (∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term w v t) := by
              apply Finset.sum_congr rfl
              intro t ht
              have hne : t ≠ S := (Finset.mem_erase.mp ht).1
              simp [term, w', hne]
            calc
              coord w' v = ∑ t : Finset V, term w' v t := rfl
              _ = (∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term w' v t) + term w' v S := by
                rw [← Finset.sum_erase_add (Finset.univ : Finset (Finset V)) (fun t => term w' v t)
                  (Finset.mem_univ S)]
              _ = ∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term w v t := by
                rw [hsumErase]
                simp [term, w']
          have hsumZ : coord z' v = ∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term z v t := by
            have hsumErase :
                (∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term z' v t) =
                (∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term z v t) := by
              apply Finset.sum_congr rfl
              intro t ht
              have hne : t ≠ S := (Finset.mem_erase.mp ht).1
              simp [term, z', hne]
            calc
              coord z' v = ∑ t : Finset V, term z' v t := rfl
              _ = (∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term z' v t) + term z' v S := by
                rw [← Finset.sum_erase_add (Finset.univ : Finset (Finset V)) (fun t => term z' v t)
                  (Finset.mem_univ S)]
              _ = ∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term z v t := by
                rw [hsumErase]
                simp [term, z']
          have hdecompW : coord w v = coord w' v + term w v S := by
            calc
              coord w v = (∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term w v t) + term w v S := by
                change (∑ t : Finset V, term w v t) = _
                rw [← Finset.sum_erase_add (Finset.univ : Finset (Finset V)) (fun t => term w v t)
                  (Finset.mem_univ S)]
              _ = coord w' v + term w v S := by rw [← hsumW]
          have hdecompZ : coord z v = coord z' v + term z v S := by
            calc
              coord z v = (∑ t ∈ (Finset.univ : Finset (Finset V)).erase S, term z v t) + term z v S := by
                change (∑ t : Finset V, term z v t) = _
                rw [← Finset.sum_erase_add (Finset.univ : Finset (Finset V)) (fun t => term z v t)
                  (Finset.mem_univ S)]
              _ = coord z' v + term z v S := by rw [← hsumZ]
          have htop : term w v S = term z v S := by simp [term, hWS]
          have hcv := hcoords v
          rw [hdecompW, hdecompZ, htop] at hcv
          exact add_right_cancel hcv
        have hres := ih (cnt w' + cnt z') hn' w' z' rfl hw'0 hz'0 hw' hz' hw'chain hz'chain hcoords'
        funext s
        by_cases hs : s = S
        · subst s
          simp [w', z', hWS]
        · have h := congrFun hres s
          simpa [w', hs, z', hs] using h
      · have hzA : ¬ ∃ s, 0 < z s := by
          intro hza
          exact hwa (hactive.mpr hza)
        have hwAll : ∀ s, w s = 0 := by
            intro s
            have hn : ¬ 0 < w s := by
              intro hs
              exact hwa ⟨s, by simp [supp, hs]⟩
            exact le_antisymm (not_lt.mp hn) (hw s)
        have hzAll : ∀ s, z s = 0 := by
          intro s
          have hn : ¬ 0 < z s := fun hs => hzA ⟨s, hs⟩
          exact le_antisymm (not_lt.mp hn) (hz s)
        funext s
        simp [hwAll s, hzAll s]

  apply aux (cnt w + cnt z) w z rfl hw0 hz0 hw hz hwchain hzchain hcoords
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BarycentricChainInjectivity
