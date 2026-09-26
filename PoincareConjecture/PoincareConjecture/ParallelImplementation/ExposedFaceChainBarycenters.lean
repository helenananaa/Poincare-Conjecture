import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ExposedFaceChainBarycenters
open scoped BigOperators
/-- Centroids of a strict flag of actual exposed finite faces are affinely
independent. This supplies the geometric simplex test for coherent polytope
face-chain triangulations, not an assumed independence certificate. -/
theorem affineIndependent_exposed_face_chain_barycenters
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (s : Fin (n+1) → Finset E) (hs : ∀ i, (s i).Nonempty)
    (l : Fin n → E →ₗ[ℝ] ℝ) (a : Fin n → ℝ)
    (hface : ∀ (i : Fin n) (v : E),
      v ∈ s i.castSucc ↔ v ∈ s i.succ ∧ l i v = a i)
    (hsupport : ∀ (i : Fin n) (v : E), v ∈ s i.succ → l i v ≤ a i)
    (hproper : ∀ i : Fin n, ∃ v ∈ s i.succ, l i v < a i) :
    AffineIndependent ℝ (fun i : Fin (n+1) =>
      ((s i).card : ℝ)⁻¹ • ∑ v ∈ s i, v) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let b : Fin (n + 1) → E := fun i =>
    ((s i).card : ℝ)⁻¹ • ∑ v ∈ s i, v
  have hstep (i : Fin n) : s i.castSucc ⊆ s i.succ := by
    intro v hv
    exact (hface i v).mp hv |>.1
  have hchain : ∀ j k : Fin (n + 1), j ≤ k → s j ⊆ s k := by
    intro j k
    induction k using Fin.induction with
    | zero =>
        intro hj
        have hjv : j.val ≤ 0 := by
          simpa using Fin.le_iff_val_le_val.mp hj
        have : j = 0 := Fin.ext (Nat.eq_zero_of_le_zero hjv)
        subst j
        exact Finset.Subset.rfl
    | succ k ih =>
        intro hj
        by_cases hle : j ≤ k.castSucc
        · exact (ih hle).trans (hstep k)
        · have heq : j = k.succ := by
            have hlt : k.castSucc < j := lt_of_not_ge hle
            have hsucc : k.succ ≤ j := (Fin.castSucc_lt_iff_succ_le).mp hlt
            exact le_antisymm hj hsucc
          simp [heq]
  have hb_eq (i : Fin n) (j : Fin (n + 1)) (hji : j ≤ i.castSucc) :
      l i (b j) = a i := by
    have hvals : ∀ v ∈ s j, l i v = a i := by
      intro v hv
      exact ((hface i v).mp (hchain j i.castSucc hji hv)).2
    have hsum : (∑ v ∈ s j, l i v) = ∑ v ∈ s j, a i := by
      apply Finset.sum_congr rfl
      intro v hv
      exact hvals v hv
    have hcard : ((s j).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_ne_zero.mpr (hs j))
    calc
      l i (b j) = ((s j).card : ℝ)⁻¹ • (∑ v ∈ s j, l i v) := by
        simp [b, map_smul, map_sum]
      _ = ((s j).card : ℝ)⁻¹ • (∑ v ∈ s j, a i) := by rw [hsum]
      _ = a i := by
        simp [Finset.sum_const, nsmul_eq_mul]
        field_simp
  have hb_strict (i : Fin n) : l i (b i.succ) < a i := by
    obtain ⟨v₀, hv₀, hlt₀⟩ := hproper i
    have hsum : (∑ v ∈ s i.succ, l i v) < ∑ _v ∈ s i.succ, a i := by
      exact Finset.sum_lt_sum (fun v hv => hsupport i v hv) ⟨v₀, hv₀, hlt₀⟩
    have hsum' : (∑ v ∈ s i.succ, l i v) < (s i.succ).card • a i := by
      simpa using hsum
    have hcard : 0 < ((s i.succ).card : ℝ) := by
      exact_mod_cast (Finset.card_pos.mpr (hs i.succ))
    have hmap : l i (b i.succ) =
        ((s i.succ).card : ℝ)⁻¹ * (∑ v ∈ s i.succ, l i v) := by
      simp [b, map_smul, map_sum, smul_eq_mul]
    rw [hmap]
    calc
      ((s i.succ).card : ℝ)⁻¹ * (∑ v ∈ s i.succ, l i v) <
          ((s i.succ).card : ℝ)⁻¹ * ((s i.succ).card • a i) :=
        mul_lt_mul_of_pos_left hsum' (inv_pos.mpr hcard)
      _ = a i := by
        simp only [nsmul_eq_mul]
        field_simp
  have triangular : ∀ m (v : Fin m → E) (φ : Fin m → E →ₗ[ℝ] ℝ),
      (∀ i j, j < i → φ i (v j) = 0) →
      (∀ i, φ i (v i) ≠ 0) → LinearIndependent ℝ v := by
    intro m
    induction m with
    | zero =>
        intro v φ _ _
        rw [Fintype.linearIndependent_iff]
        intro g _ i
        exact Fin.elim0 i
    | succ m ih =>
        intro v φ htri hdiag
        have hprefix : LinearIndependent ℝ (fun i : Fin m => v i.castSucc) := by
          apply ih
          · intro i k hki
            exact htri i.castSucc k.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hki)
          · intro i
            exact hdiag i.castSucc
        have hs : Fin.snoc (fun i : Fin m => v i.castSucc) (v (Fin.last m)) = v := by
          funext i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp
          · simp
        have hli : LinearIndependent ℝ
            (Fin.snoc (fun i : Fin m => v i.castSucc) (v (Fin.last m))) := by
          refine LinearIndependent.finSnoc' (fun i : Fin m => v i.castSucc)
            (v (Fin.last m)) hprefix ?_
          intro c y hy hcy
          have hyzero : φ (Fin.last m) y = 0 := by
            refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
            · intro z hz
              rcases hz with ⟨i, rfl⟩
              exact htri (Fin.last m) i.castSucc (Fin.castSucc_lt_last i)
            · simp
            · intro y₁ y₂ _ _ h₁ h₂
              simp [map_add, h₁, h₂]
            · intro r z _ hz
              simp [map_smul, hz]
          have heq : c * φ (Fin.last m) (v (Fin.last m)) = 0 := by
            calc
              c * φ (Fin.last m) (v (Fin.last m)) =
                  φ (Fin.last m) (c • v (Fin.last m) + y) := by
                    simp [map_add, map_smul, smul_eq_mul, hyzero]
              _ = 0 := by rw [hcy]; simp
          rcases mul_eq_zero.mp heq with hc | hx
          · exact hc
          · exact (hdiag (Fin.last m) hx).elim
        have hli' : LinearIndependent ℝ v := hs ▸ hli
        rw [Fintype.linearIndependent_iff] at hli' ⊢
        exact hli'
  have hli : LinearIndependent ℝ (fun j : Fin n => b j.succ -ᵥ b 0) := by
    apply triangular n (fun j => b j.succ -ᵥ b 0) l
    · intro i j hji
      rw [vsub_eq_sub, map_sub]
      rw [hb_eq i j.succ (Fin.succ_le_castSucc_iff.mpr hji),
        hb_eq i 0 (Fin.zero_le _), sub_self]
    · intro i
      rw [vsub_eq_sub, map_sub, hb_eq i 0 (Fin.zero_le _)]
      exact ne_of_lt (sub_lt_zero.mpr (hb_strict i))
  have hindep : AffineIndependent ℝ b := by
    rw [affineIndependent_iff_of_fintype]
    intro w hw hs i
    rw [Finset.univ.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero w b hw (b 0),
      Finset.weightedVSubOfPoint_apply] at hs
    have htail :
        (∑ j : Fin n, w j.succ • (b j.succ -ᵥ b 0)) = 0 := by
      simpa only [Fin.sum_univ_succ, vsub_self, smul_zero, zero_add] using hs
    have hall := (Fintype.linearIndependent_iff.mp hli)
      (fun j : Fin n => w j.succ) htail
    have hzero : w 0 = 0 := by
      rw [Fin.sum_univ_succ] at hw
      have hrest : (∑ j : Fin n, w j.succ) = 0 := by simp [hall]
      simpa [hrest] using hw
    exact Fin.cases hzero hall i
  simpa [b] using hindep
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ExposedFaceChainBarycenters
