import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FiniteBarycentricInverse
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
def outsideMax (y : V → ℝ) (s : Finset V) : ℝ :=
  (insert 0 ((Finset.univ \ s).image y)).max' (Finset.insert_nonempty 0 _)
def recoveredWeight (y : V → ℝ) (s : Finset V) : ℝ :=
  if hs : s.Nonempty then
    (s.card : ℝ) * max 0 (s.inf' hs y - outsideMax y s)
  else 0
def barycenterCoordinates (w : Finset V → ℝ) (v : V) : ℝ :=
  ∑ s : Finset V, w s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0)
theorem finite_layer_cake (y : V → ℝ) (hy : ∀ v, 0 ≤ y v) :
    (∀ s : Finset V, 0 ≤ recoveredWeight y s) ∧
    (∀ a b : Finset V, 0 < recoveredWeight y a → 0 < recoveredWeight y b →
      a ⊆ b ∨ b ⊆ a) ∧
    (∀ s : Finset V, 0 < recoveredWeight y s → ∀ v ∈ s, 0 < y v) ∧
    (∀ v : V, barycenterCoordinates (recoveredWeight y) v = y v) ∧
    (∑ s : Finset V, recoveredWeight y s) = ∑ v : V, y v :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let support : (V → ℝ) → Finset V := fun f => Finset.univ.filter fun v => 0 < f v
  let supportSize : (V → ℝ) → ℕ := fun f => (support f).card
  have aux : ∀ n : ℕ, ∀ f : V → ℝ, (∀ v, 0 ≤ f v) → supportSize f = n →
      (∀ s : Finset V, 0 ≤ recoveredWeight f s) ∧
      (∀ a b : Finset V, 0 < recoveredWeight f a → 0 < recoveredWeight f b →
        a ⊆ b ∨ b ⊆ a) ∧
      (∀ s : Finset V, 0 < recoveredWeight f s → ∀ v ∈ s, 0 < f v) ∧
      (∀ v : V, barycenterCoordinates (recoveredWeight f) v = f v) ∧
      (∑ s : Finset V, recoveredWeight f s) = ∑ v : V, f v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro f hf hn
      let P : Finset V := support f
      have hP : ∀ v, v ∈ P ↔ 0 < f v := by
        intro v
        simp [P, support]
      by_cases hPne : P.Nonempty
      · let c : ℝ := P.inf' hPne f
        let f' : V → ℝ := fun v => max 0 (f v - c)
        have hc_eq : c = (P.image f).min' (hPne.image f) := by
          dsimp [c, Finset.min']
          simpa only [Function.id_comp] using
            (Finset.inf'_comp_eq_image (f := f) hPne id)
        have hc_mem : c ∈ P.image f := by
          rw [hc_eq]
          exact Finset.min'_mem _ _
        have hc_pos : 0 < c := by
          rcases Finset.mem_image.mp hc_mem with ⟨v, hvP, hcv⟩
          rw [← hcv]
          exact (hP v).1 hvP
        have hc_le (v : V) (hv : v ∈ P) : c ≤ f v := by
          dsimp [c]
          exact Finset.inf'_le (f := f) hv
        obtain ⟨v₀, hv₀P, hv₀_eq⟩ := Finset.mem_image.mp hc_mem
        have hfzero (v : V) (hv : v ∉ P) : f v = 0 := by
          have hnot : ¬ 0 < f v := by simpa [hP v] using hv
          exact le_antisymm (le_of_not_gt hnot) (hf v)
        have hf'P (v : V) (hv : v ∈ P) : f' v = f v - c := by
          dsimp [f']
          rw [max_eq_right (sub_nonneg.mpr (hc_le v hv))]
        have hf'zero (v : V) (hv : v ∉ P) : f' v = 0 := by
          dsimp [f']
          rw [hfzero v hv]
          rw [max_eq_left (by linarith [hc_pos] : (0 : ℝ) - c ≤ 0)]
        have hf'nonneg : ∀ v, 0 ≤ f' v := fun v => le_max_left _ _
        have hf'Psub : support f' ⊆ P := by
          intro v hv
          by_contra hvP
          have hz := hf'zero v hvP
          simp [support] at hv
          rw [hz] at hv
          exact (lt_irrefl 0 hv)
        have hv₀not : v₀ ∉ support f' := by
          have hminzero : f' v₀ = 0 := by
            rw [hf'P v₀ hv₀P, hv₀_eq]
            simp
          simp [support, hminzero]
        have hproper : support f' ⊂ P := by
          refine Finset.ssubset_iff_subset_ne.mpr ⟨hf'Psub, ?_⟩
          intro heq
          have : v₀ ∈ support f' := by simpa [heq] using hv₀P
          exact hv₀not this
        have hsize' : supportSize f' < n := by
          rw [← hn]
          exact Finset.card_lt_card hproper
        have ih' := ih (supportSize f') hsize' f' hf'nonneg rfl
        let base : Finset V → ℝ := fun s => if s = P then (P.card : ℝ) * c else 0
        have hf'le (v : V) : f' v ≤ f v := by
          dsimp [f']
          exact max_le (hf v) (sub_le_self _ hc_pos.le)
        have hfdecomp_coord (v : V) : f v = f' v + if v ∈ P then c else 0 := by
          by_cases hv : v ∈ P
          · rw [if_pos hv, hf'P v hv]
            ring
          · rw [if_neg hv, hfzero v hv, hf'zero v hv]
            ring
        have outside_nonneg (g : V → ℝ) (s : Finset V) : 0 ≤ outsideMax g s := by
          have h := Finset.le_max' (insert 0 ((Finset.univ \ s).image g)) 0
            (Finset.mem_insert_self 0 _)
          simpa [outsideMax] using h
        have outside_zero (g : V → ℝ) (hg : ∀ v ∉ P, g v = 0) :
            outsideMax g P = 0 := by
          apply le_antisymm
          · unfold outsideMax
            apply Finset.max'_le
            intro z hz
            rcases Finset.mem_insert.mp hz with hz0 | hz
            · simp [hz0]
            · rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
              have hvnot : v ∉ P := (Finset.mem_sdiff.mp hv).2
              rw [hg v hvnot]
          · unfold outsideMax
            exact Finset.le_max' (insert 0 ((Finset.univ \ P).image g)) 0
              (Finset.mem_insert_self 0 _)
        have inf_shift (s : Finset V) (hs : s.Nonempty) (hsub : s ⊆ P) :
            s.inf' hs f = c + s.inf' hs f' := by
          have hfun : ∀ v ∈ s, f v = c + f' v := by
            intro v hv
            rw [hf'P v (hsub hv)]
            ring
          calc
            s.inf' hs f = s.inf' hs (fun v => c + f' v) := by
              apply Finset.inf'_congr hs rfl
              exact hfun
            _ = c + s.inf' hs f' := by
              symm
              exact Finset.apply_inf'_eq_inf'_comp hs (fun x : ℝ => c + x)
                (by intro x y; simp [min_add_add_left])
        have outside_shift (s : Finset V) (hsub : s ⊆ P) (hne : s ≠ P) :
            outsideMax f s = c + outsideMax f' s := by
          have hdiff : (P \ s).Nonempty := by
            by_contra h
            have hPs : P ⊆ s := by
              intro v hv
              by_contra hvs
              exact h ⟨v, Finset.mem_sdiff.mpr ⟨hv, hvs⟩⟩
            exact hne (Finset.Subset.antisymm hsub hPs)
          have hc_out : c ≤ outsideMax f s := by
            obtain ⟨p, hp⟩ := hdiff
            have hpP : p ∈ P := (Finset.mem_sdiff.mp hp).1
            have hps : p ∉ s := (Finset.mem_sdiff.mp hp).2
            have hmem : f p ∈ insert 0 ((Finset.univ \ s).image f) := by
              apply Finset.mem_insert_of_mem
              exact Finset.mem_image.mpr ⟨p, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hps⟩, rfl⟩
            exact (hc_le p hpP).trans
              (Finset.le_max' (insert 0 ((Finset.univ \ s).image f)) (f p) hmem)
          apply le_antisymm
          · unfold outsideMax
            apply Finset.max'_le
            intro z hz
            rcases Finset.mem_insert.mp hz with hz0 | hz
            · have hm : 0 ≤ outsideMax f' s := outside_nonneg f' s
              rw [hz0]
              exact add_nonneg hc_pos.le (outside_nonneg f' s)
            · rcases Finset.mem_image.mp hz with ⟨v, hv, rfl⟩
              have hvnotS : v ∉ s := (Finset.mem_sdiff.mp hv).2
              have hmem' : f' v ∈ insert 0 ((Finset.univ \ s).image f') := by
                apply Finset.mem_insert_of_mem
                exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvnotS⟩, rfl⟩
              have hvle : f' v ≤ outsideMax f' s :=
                Finset.le_max' (insert 0 ((Finset.univ \ s).image f')) (f' v) hmem'
              by_cases hvP : v ∈ P
              · have hfeq : f v = c + f' v := by
                  rw [hf'P v hvP]
                  ring
                rw [hfeq]
                unfold outsideMax at hvle
                linarith
              · rw [hfzero v hvP]
                have hm : 0 ≤ outsideMax f' s := outside_nonneg f' s
                exact add_nonneg hc_pos.le (outside_nonneg f' s)
          · have hmemb : outsideMax f' s ∈ insert 0 ((Finset.univ \ s).image f') := by
              unfold outsideMax at *
              exact Finset.max'_mem _ _
            rcases Finset.mem_insert.mp hmemb with hz0 | hz
            · rw [hz0]
              simpa using hc_out
            · rcases Finset.mem_image.mp hz with ⟨v, hv, hvEq⟩
              have hvnotS : v ∉ s := (Finset.mem_sdiff.mp hv).2
              by_cases hvP : v ∈ P
              · have hmem : f v ∈ insert 0 ((Finset.univ \ s).image f) := by
                  apply Finset.mem_insert_of_mem
                  exact Finset.mem_image.mpr ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hvnotS⟩, rfl⟩
                have hvle : f v ≤ outsideMax f s :=
                  Finset.le_max' (insert 0 ((Finset.univ \ s).image f)) (f v) hmem
                rw [← hvEq, hf'P v hvP]
                linarith
              · rw [← hvEq, hf'zero v hvP]
                simpa using hc_out
        have zero_weight (g : V → ℝ) (hg : ∀ v, 0 ≤ g v) (s : Finset V)
            (hs : s.Nonempty) (v : V) (hvs : v ∈ s) (hvzero : g v = 0) :
            recoveredWeight g s = 0 := by
          have hinf : s.inf' hs g = 0 := by
            apply le_antisymm
            · have hle := Finset.inf'_le (f := g) hvs
              simpa [hvzero] using hle
            · apply (Finset.le_inf'_iff hs g).2
              intro u hu
              exact hg u
          have hout := outside_nonneg g s
          have hgap : (0 : ℝ) - outsideMax g s ≤ 0 := by linarith [hout]
          unfold recoveredWeight
          rw [dif_pos hs, hinf, max_eq_left hgap]
          simp
        have hdecomp : ∀ s : Finset V,
            recoveredWeight f s = recoveredWeight f' s + base s := by
          intro s
          by_cases hseq : s = P
          · subst s
            have hInf' : P.inf' hPne f' = 0 := by
              apply le_antisymm
              · have hle := Finset.inf'_le (f := f') hv₀P
                simpa [f', hv₀_eq, max_eq_left, hc_pos.le] using hle
              · apply (Finset.le_inf'_iff hPne f').2
                intro v hv
                exact hf'nonneg v
            have hout : outsideMax f P = 0 := outside_zero f hfzero
            have hout' : outsideMax f' P = 0 := outside_zero f' (fun v hv => hf'zero v hv)
            have hw : recoveredWeight f P = (P.card : ℝ) * c := by
              simp [recoveredWeight, hPne, c, hout, hc_pos.le]
            have hw' : recoveredWeight f' P = 0 := by
              simp [recoveredWeight, hPne, hInf', hout']
            rw [hw, hw']
            simp [base]
          · by_cases hs : s.Nonempty
            · by_cases hsub : s ⊆ P
              · have hinf := inf_shift s hs hsub
                have hout := outside_shift s hsub hseq
                have hw : recoveredWeight f s = recoveredWeight f' s := by
                  simp [recoveredWeight, hs, hinf, hout]
                rw [hw]
                simp [base, hseq]
              · obtain ⟨v, hvs, hvnotP⟩ := Finset.not_subset.mp hsub
                have hw : recoveredWeight f s = 0 := zero_weight f hf s hs v hvs (hfzero v hvnotP)
                have hw' : recoveredWeight f' s = 0 := zero_weight f' hf'nonneg s hs v hvs (hf'zero v hvnotP)
                rw [hw, hw']
                simp [base, hseq]
            · have hw : recoveredWeight f s = 0 := by simp [recoveredWeight, hs]
              have hw' : recoveredWeight f' s = 0 := by simp [recoveredWeight, hs]
              rw [hw, hw']
              simp [base, hseq]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro s
          rw [hdecomp s]
          by_cases hs : s = P
          · simp [base, hs]
            exact add_nonneg ((ih').1 P) (mul_nonneg (Nat.cast_nonneg _) hc_pos.le)
          · simpa [base, hs] using (ih').1 s
        · intro a b ha hb
          by_cases haP : a = P
          · subst a
            by_cases hbP : b = P
            · exact Or.inl (by simp [hbP])
            · have hwb : 0 < recoveredWeight f' b := by
                have heq : recoveredWeight f b = recoveredWeight f' b := by
                  simpa [base, hbP] using hdecomp b
                rw [← heq]
                exact hb
              have hsub : b ⊆ P := by
                intro v hv
                have hvpos := (ih').2.2.1 b hwb v hv
                exact (hP v).2 (lt_of_lt_of_le hvpos (hf'le v))
              exact Or.inr hsub
          · by_cases hbP : b = P
            · subst b
              have hwa : 0 < recoveredWeight f' a := by
                have heq : recoveredWeight f a = recoveredWeight f' a := by
                  simpa [base, haP] using hdecomp a
                rw [← heq]
                exact ha
              have hsub : a ⊆ P := by
                intro v hv
                have hvpos := (ih').2.2.1 a hwa v hv
                exact (hP v).2 (lt_of_lt_of_le hvpos (hf'le v))
              exact Or.inl hsub
            · have hwa : 0 < recoveredWeight f' a := by
                have heq : recoveredWeight f a = recoveredWeight f' a := by
                  simpa [base, haP] using hdecomp a
                rw [← heq]
                exact ha
              have hwb : 0 < recoveredWeight f' b := by
                have heq : recoveredWeight f b = recoveredWeight f' b := by
                  simpa [base, hbP] using hdecomp b
                rw [← heq]
                exact hb
              exact (ih').2.1 a b hwa hwb
        · intro s hs v hv
          by_cases hsP : s = P
          · subst s
            exact (hP v).1 hv
          · have hw : recoveredWeight f' s = recoveredWeight f s := by
              rw [hdecomp s]
              simp [base, hsP]
            have hpos : 0 < recoveredWeight f' s := by rw [hw]; exact hs
            have hvpos := (ih').2.2.1 s hpos v hv
            exact lt_of_lt_of_le hvpos (hf'le v)
        · intro v
          have hbase : (∑ s : Finset V,
              base s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0)) =
              if v ∈ P then c else 0 := by
            classical
            rw [Finset.sum_eq_single P]
            · by_cases hv : v ∈ P
              · simp [base, hv]
                have hcard : (P.card : ℝ) ≠ 0 := by
                  exact_mod_cast hPne.card_pos.ne'
                field_simp
              · simp [base, hv]
            · intro s hs hne
              simp [base, hne]
            · simp
          calc
            barycenterCoordinates (recoveredWeight f) v =
                ∑ s : Finset V,
                  (recoveredWeight f' s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0) +
                    base s * ((s.card : ℝ)⁻¹ * if v ∈ s then 1 else 0)) := by
                  unfold barycenterCoordinates
                  apply Finset.sum_congr rfl
                  intro s hs
                  rw [hdecomp s]
                  ring
            _ = barycenterCoordinates (recoveredWeight f') v +
                  (if v ∈ P then c else 0) := by
                  unfold barycenterCoordinates
                  rw [Finset.sum_add_distrib, hbase]
            _ = f v := by rw [(ih').2.2.2.1 v, hfdecomp_coord v]
        · calc
            (∑ s : Finset V, recoveredWeight f s) =
                (∑ s : Finset V, (recoveredWeight f' s + base s)) := by
                  apply Finset.sum_congr rfl
                  intro s hs
                  exact hdecomp s
            _ = (∑ s : Finset V, recoveredWeight f' s) +
                (∑ s : Finset V, base s) := Finset.sum_add_distrib
            _ = (∑ v : V, f' v) + (P.card : ℝ) * c := by
                  rw [(ih').2.2.2.2]
                  have hsumBase : (∑ s : Finset V, base s) = (P.card : ℝ) * c := by
                    classical
                    rw [Finset.sum_eq_single P]
                    · simp [base]
                    · intro s hs hne
                      simp [base, hne]
                    · simp
                  rw [hsumBase]
            _ = ∑ v : V, f v := by
                  have hmassLayer :
                      (∑ v : V, if v ∈ P then c else 0) = (P.card : ℝ) * c := by
                    classical
                    rw [Finset.sum_ite_mem_eq]
                    simp
                  rw [← hmassLayer, ← Finset.sum_add_distrib]
                  apply Finset.sum_congr rfl
                  intro v hv
                  exact (hfdecomp_coord v).symm
      · have hzeroCoord : ∀ v, f v = 0 := by
          intro v
          by_contra hne
          have hpos : 0 < f v := by
            rcases lt_or_eq_of_le (hf v) with hpos | heq
            · exact hpos
            · exact (hne heq.symm).elim
          exact hPne ⟨v, (hP v).2 hpos⟩
        have hout_nonneg (s : Finset V) : 0 ≤ outsideMax f s := by
          unfold outsideMax
          exact Finset.le_max' (insert 0 ((Finset.univ \ s).image f)) 0
            (Finset.mem_insert_self 0 _)
        have hws (s : Finset V) : recoveredWeight f s = 0 := by
          by_cases hs : s.Nonempty
          · have hinf : s.inf' hs f = 0 := by
              apply le_antisymm
              · obtain ⟨v, hv⟩ := hs
                simpa [hzeroCoord v] using (Finset.inf'_le (f := f) hv)
              · apply (Finset.le_inf'_iff hs f).2
                intro v hv
                rw [hzeroCoord v]
            have hgap : (0 : ℝ) - outsideMax f s ≤ 0 := by
              linarith [hout_nonneg s]
            unfold recoveredWeight
            rw [dif_pos hs, hinf, max_eq_left hgap]
            simp
          · simp [recoveredWeight, hs]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro s
          rw [hws s]
        · intro a b ha hb
          rw [hws a] at ha
          norm_num at ha
        · intro s hs v hv
          rw [hws s] at hs
          norm_num at hs
        · intro v
          simp [barycenterCoordinates, hws, hzeroCoord]
        · simp [hws, hzeroCoord]
  have h := aux (supportSize y) y hy rfl
  exact h
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FiniteBarycentricInverse
