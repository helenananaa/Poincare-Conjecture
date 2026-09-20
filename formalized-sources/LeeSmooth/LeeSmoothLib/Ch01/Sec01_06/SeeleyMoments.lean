import LeeSmoothLib.Ch01.Sec01_06.SeeleyCoefficientData
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Normed

/-!
Infinite Seeley moment identities and rapid weighted summability for the exact
coefficients defined in `SeeleyCoefficientData`.
-/

noncomputable section

open Set Filter Finset
open scoped Topology

namespace LeeSmooth.SeeleyExtension

universe u v

/-! ## Product formula for the finite Lagrange coefficients -/

private lemma seeleyCoeffFinite_eq_prod (N j : ℕ) (hj : j < N) :
    seeleyCoeffFinite N ⟨j, hj⟩ =
      ∏ i ∈ (range N).erase j,
        (1 - seeleyNode i) / (seeleyNode j - seeleyNode i) := by
  classical
  unfold seeleyCoeffFinite Lagrange.basis
  rw [Polynomial.eval_prod]
  have hmap :
      (((univ : Finset (Fin N)).erase ⟨j, hj⟩).map Fin.valEmbedding) =
        (range N).erase j := by
    rw [map_erase Fin.valEmbedding]
    simp [Fin.map_valEmbedding_univ, Nat.Iio_eq_range]
  rw [← hmap, prod_map]
  refine prod_congr rfl ?_
  intro i hi
  have hne : (i : ℕ) ≠ j := by
    intro h
    exact (mem_erase.mp hi).1 (Fin.ext h)
  simp only [Fin.valEmbedding_apply]
  rw [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, mul_comm]
  exact (div_eq_mul_inv (1 - seeleyNode (i : ℕ))
      (seeleyNode j - seeleyNode (i : ℕ))).symm

private lemma range_succ_erase_self (j : ℕ) :
    (range (j + 1)).erase j = range j := by
  rw [range_add_one, erase_insert]
  exact notMem_range_self

private lemma seeleyCoeffFinite_succ (N j : ℕ) (hj : j < N) :
    seeleyCoeffFinite (N + 1) ⟨j, Nat.lt_succ_of_lt hj⟩ =
      seeleyCoeffFinite N ⟨j, hj⟩ * seeleyTailFactor j (N - j - 1) := by
  classical
  have hjN : j ≠ N := ne_of_lt hj
  have h_erase :
      (range (N + 1)).erase j = insert N ((range N).erase j) := by
    rw [range_add_one, erase_insert_of_ne hjN.symm]
  have hN : N ∉ (range N).erase j := by
    simp [mem_erase]
  rw [seeleyCoeffFinite_eq_prod, seeleyCoeffFinite_eq_prod, h_erase, prod_insert hN]
  have hk : N - j - 1 + j + 1 = N := by omega
  simp [seeleyTailFactor, hk]
  ring

private lemma seeleyCoeffFiniteNat_eq_head_mul_prod (N j : ℕ) (hj : j < N) :
    seeleyCoeffFiniteNat N j =
      seeleyCoeffFinite (j + 1) ⟨j, Nat.lt_succ_self j⟩ *
        ∏ k ∈ range (N - j - 1), seeleyTailFactor j k := by
  induction N generalizing j with
  | zero =>
      exact (Nat.not_lt_zero j hj).elim
  | succ N ih =>
      rw [seeleyCoeffFiniteNat, dif_pos hj]
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hj) with hje | hjN
      · subst j
        simp
      · have ihj := ih j hjN
        rw [seeleyCoeffFiniteNat, dif_pos hjN] at ihj
        have hlen : N + 1 - j - 1 = N - j - 1 + 1 := by omega
        rw [seeleyCoeffFinite_succ N j hjN, ihj, hlen, prod_range_succ]
        ring

/-! ## Convergence of truncated coefficients to the infinite coefficients -/

lemma tendsto_seeleyCoeffFiniteNat (j : ℕ) :
    Tendsto (fun N ↦ seeleyCoeffFiniteNat N j) atTop (𝓝 (seeleyCoeff j)) := by
  have h_ev : ∀ᶠ N : ℕ in atTop, j + 1 ≤ N := eventually_ge_atTop (j + 1)
  have h_eq : ∀ᶠ N : ℕ in atTop,
      seeleyCoeffFiniteNat N j =
        seeleyCoeffFinite (j + 1) ⟨j, Nat.lt_succ_self j⟩ *
          ∏ k ∈ range (N - (j + 1)), seeleyTailFactor j k := by
    filter_upwards [h_ev] with N hN
    have hj : j < N := lt_of_lt_of_le (Nat.lt_succ_self j) hN
    have hsub : N - (j + 1) = N - j - 1 := by omega
    rw [seeleyCoeffFiniteNat_eq_head_mul_prod N j hj, hsub]
  have hprod :
      Tendsto (fun N : ℕ ↦ ∏ k ∈ range (N - (j + 1)), seeleyTailFactor j k)
        atTop (𝓝 (∏' k, seeleyTailFactor j k)) :=
    (multipliable_seeleyTailFactor j).tendsto_prod_tprod_nat.comp
      (tendsto_sub_atTop_nat (j + 1))
  have hmul :=
    (tendsto_const_nhds
        (x := seeleyCoeffFinite (j + 1) ⟨j, Nat.lt_succ_self j⟩)).mul hprod
  refine hmul.congr' ?_
  filter_upwards [h_eq] with N hN
  exact hN.symm

/-! ## Uniform tail-product bound -/

private lemma seeleyTailFactor_prod_range_le (j n : ℕ) :
    ∏ k ∈ range n, seeleyTailFactor j k ≤ Real.exp 4 := by
  have hpos : ∀ k, 0 ≤ seeleyTailFactor j k - 1 :=
    fun k ↦ le_of_lt (sub_pos.mpr (seeleyTailFactor_one_lt j k))
  calc
    ∏ k ∈ range n, seeleyTailFactor j k
        = ∏ k ∈ range n, (1 + (seeleyTailFactor j k - 1)) := by
          refine prod_congr rfl fun k _ ↦ by ring
    _ ≤ Real.exp (∑ k ∈ range n, (seeleyTailFactor j k - 1)) :=
        Real.prod_one_add_le_exp_sum _ hpos
    _ ≤ Real.exp (∑ k ∈ range n, (2 : ℝ) * ((1 : ℝ) / 2) ^ k) := by
          gcongr
          exact seeleyTailFactor_sub_one_le j _
    _ = Real.exp (2 * ∑ k ∈ range n, ((1 : ℝ) / 2) ^ k) := by
          simp [mul_sum]
    _ ≤ Real.exp (2 * 2) := by
          gcongr
          exact sum_geometric_two_le n
    _ = Real.exp 4 := by norm_num

private lemma seeleyTailFactor_tprod_le (j : ℕ) :
    ∏' k, seeleyTailFactor j k ≤ Real.exp 4 :=
  (multipliable_seeleyTailFactor j).tprod_le_of_prod_range_le
    (fun n ↦ seeleyTailFactor_prod_range_le j n)

/-! ## Quadratic-decay bound on the finite Lagrange head -/

private lemma nat_triangle_succ (j : ℕ) :
    (j + 1) * (j + 2) / 2 = j * (j + 1) / 2 + (j + 1) := by
  have h1 : 2 * (j * (j + 1) / 2) = j * (j + 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self j).two_dvd
  have h2 : 2 * ((j + 1) * (j + 2) / 2) = (j + 1) * (j + 2) :=
    Nat.mul_div_cancel' (Nat.even_mul_succ_self (j + 1)).two_dvd
  apply Nat.mul_left_cancel (Nat.zero_lt_two)
  calc
    2 * ((j + 1) * (j + 2) / 2) = (j + 1) * (j + 2) := h2
    _ = j * (j + 1) + 2 * (j + 1) := by ring
    _ = 2 * (j * (j + 1) / 2) + 2 * (j + 1) := by rw [h1]
    _ = 2 * (j * (j + 1) / 2 + (j + 1)) := by ring

private lemma nat_sq_gap (j : ℕ) : (j + 1) * j = j * (j - 1) + 2 * j := by
  cases j with
  | zero => simp
  | succ k =>
      simp
      ring

private lemma sum_range_add_one (n : ℕ) :
    ∑ i ∈ range n, (i + 1) = n * (n + 1) / 2 := by
  have : ∑ i ∈ range n, (i + 1) = ∑ i ∈ range n, i + n := by
    simp [sum_add_distrib, sum_const, card_range]
  rw [this, sum_range_id]
  cases n with
  | zero => simp
  | succ k =>
      have h1 : 2 * (k.succ * k / 2) = k.succ * k :=
        Nat.mul_div_cancel' (by
          rw [Nat.mul_comm]
          exact (Nat.even_mul_succ_self k).two_dvd)
      have h2 : 2 * (k.succ * (k.succ + 1) / 2) = k.succ * (k.succ + 1) :=
        Nat.mul_div_cancel' (Nat.even_mul_succ_self k.succ).two_dvd
      apply Nat.mul_left_cancel (Nat.zero_lt_two)
      calc
        2 * (k.succ * k / 2 + k.succ)
            = 2 * (k.succ * k / 2) + 2 * k.succ := by ring
        _ = k.succ * k + 2 * k.succ := by rw [h1]
        _ = k.succ * (k + 2) := by
            rw [Nat.mul_comm 2, ← Nat.mul_add]
        _ = 2 * (k.succ * (k.succ + 1) / 2) := by
            simp [h2, Nat.succ_eq_add_one]

/-- Coarse but summable majorant for the absolute value of the length-`j+1` head. -/
private def seeleyHeadBound (j : ℕ) : ℝ :=
  (2 : ℝ) ^ (j * (j + 1) / 2) / (2 : ℝ) ^ (j * (j - 1))

private lemma seeleyHeadBound_pos (j : ℕ) : 0 < seeleyHeadBound j := by
  unfold seeleyHeadBound
  exact div_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)

private lemma seeleyNode_abs (j : ℕ) : |seeleyNode j| = (2 : ℝ) ^ j := by
  simp [seeleyNode, abs_neg, abs_of_nonneg, pow_nonneg]

private lemma seeleyNode_pow_abs (j m : ℕ) :
    |seeleyNode j ^ m| = (2 : ℝ) ^ (j * m) := by
  rw [abs_pow, seeleyNode_abs, ← pow_mul]

private lemma one_add_two_pow_le (i : ℕ) :
    1 + (2 : ℝ) ^ i ≤ (2 : ℝ) ^ (i + 1) := by
  have : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
  have hsplit : (2 : ℝ) ^ (i + 1) = (2 : ℝ) ^ i + (2 : ℝ) ^ i := by
    rw [pow_succ]
    ring
  linarith

private lemma two_pow_sub_le {j i : ℕ} (hi : i < j) :
    (2 : ℝ) ^ (j - 1) ≤ (2 : ℝ) ^ j - (2 : ℝ) ^ i := by
  have hj : 1 ≤ j := Nat.succ_le_of_lt (Nat.zero_lt_of_lt hi)
  have hsplit : (2 : ℝ) ^ j = (2 : ℝ) ^ (j - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hj]
  have hdiff : (2 : ℝ) ^ j - (2 : ℝ) ^ (j - 1) = (2 : ℝ) ^ (j - 1) := by
    rw [hsplit]
    ring
  have hle : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ (j - 1) :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_sub_one_of_lt hi)
  linarith

private lemma seeley_head_term_abs {j i : ℕ} (hi : i < j) :
    |(1 - seeleyNode i) / (seeleyNode j - seeleyNode i)| =
      (1 + (2 : ℝ) ^ i) / ((2 : ℝ) ^ j - (2 : ℝ) ^ i) := by
  have hile : (2 : ℝ) ^ i ≤ (2 : ℝ) ^ j :=
    pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_of_lt hi)
  rw [abs_div, seeleyNode, seeleyNode]
  have hnum : |1 - -((2 : ℝ) ^ i)| = 1 + (2 : ℝ) ^ i := by
    simp [abs_of_nonneg (add_nonneg zero_le_one (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i))]
  have hden : |-((2 : ℝ) ^ j) - -((2 : ℝ) ^ i)| = (2 : ℝ) ^ j - (2 : ℝ) ^ i := by
    have : -((2 : ℝ) ^ j) - -((2 : ℝ) ^ i) = (2 : ℝ) ^ i - (2 : ℝ) ^ j := by ring
    rw [this, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hile)]
  rw [hnum, hden]

private lemma seeley_head_term_le {j i : ℕ} (hi : i < j) :
    (1 + (2 : ℝ) ^ i) / ((2 : ℝ) ^ j - (2 : ℝ) ^ i) ≤
      (2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ (j - 1) := by
  have hdenpos : 0 < (2 : ℝ) ^ j - (2 : ℝ) ^ i := by
    have : (2 : ℝ) ^ i < (2 : ℝ) ^ j :=
      pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hi
    linarith
  have hpowpos : 0 < (2 : ℝ) ^ (j - 1) := pow_pos (by norm_num) _
  calc
    (1 + (2 : ℝ) ^ i) / ((2 : ℝ) ^ j - (2 : ℝ) ^ i)
        ≤ (2 : ℝ) ^ (i + 1) / ((2 : ℝ) ^ j - (2 : ℝ) ^ i) := by
          gcongr
          exact one_add_two_pow_le i
    _ ≤ (2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ (j - 1) := by
          gcongr
          exact two_pow_sub_le hi

private lemma seeleyCoeffFinite_head_abs_le (j : ℕ) :
    |seeleyCoeffFinite (j + 1) ⟨j, Nat.lt_succ_self j⟩| ≤ seeleyHeadBound j := by
  rw [seeleyCoeffFinite_eq_prod, range_succ_erase_self]
  cases j with
  | zero =>
      simp [seeleyHeadBound]
  | succ j =>
      have habs :
          |∏ i ∈ range (j + 1),
              (1 - seeleyNode i) / (seeleyNode (j + 1) - seeleyNode i)| =
            ∏ i ∈ range (j + 1),
              (1 + (2 : ℝ) ^ i) / ((2 : ℝ) ^ (j + 1) - (2 : ℝ) ^ i) := by
        rw [abs_prod]
        refine prod_congr rfl fun i hi ↦
          seeley_head_term_abs (Finset.mem_range.mp hi)
      have hterm : ∀ i ∈ range (j + 1),
          (1 + (2 : ℝ) ^ i) / ((2 : ℝ) ^ (j + 1) - (2 : ℝ) ^ i) ≤
            (2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ j :=
        fun i hi ↦ by
          simpa using seeley_head_term_le (Finset.mem_range.mp hi)
      have hprodle :=
        prod_le_prod (fun i hi ↦ by
          have hi' := Finset.mem_range.mp hi
          have : 0 < (2 : ℝ) ^ (j + 1) - (2 : ℝ) ^ i := by
            have : (2 : ℝ) ^ i < (2 : ℝ) ^ (j + 1) :=
              pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) hi'
            linarith
          positivity) hterm
      have hclosed :
          ∏ i ∈ range (j + 1), (2 : ℝ) ^ (i + 1) / (2 : ℝ) ^ j =
            seeleyHeadBound (j + 1) := by
        rw [prod_div_distrib]
        have hnum :
            ∏ i ∈ range (j + 1), (2 : ℝ) ^ (i + 1) =
              (2 : ℝ) ^ ∑ i ∈ range (j + 1), (i + 1) :=
          (prod_pow_eq_pow_sum (range (j + 1)) (fun i ↦ i + 1) (2 : ℝ))
        have hden :
            ∏ i ∈ range (j + 1), (2 : ℝ) ^ j =
              (2 : ℝ) ^ (j * (j + 1)) := by
          simp [prod_const, card_range, pow_mul]
        rw [hnum, hden, sum_range_add_one]
        simp [seeleyHeadBound, Nat.mul_comm]
      rw [habs]
      exact hprodle.trans_eq hclosed

private lemma seeleyHeadBound_succ (j : ℕ) :
    seeleyHeadBound (j + 1) =
      seeleyHeadBound j * (2 : ℝ) ^ (j + 1) / (2 : ℝ) ^ (2 * j) := by
  unfold seeleyHeadBound
  have htri := nat_triangle_succ j
  have hgap := nat_sq_gap j
  rw [htri, pow_add, show (j + 1) * ((j + 1) - 1) = (j + 1) * j by simp, hgap, pow_add]
  field_simp
  ring

/-! ## Uniform majorant, independent of the interpolation cutoff -/

private def seeleyMajorant (m j : ℕ) : ℝ :=
  Real.exp 4 * seeleyHeadBound j * (2 : ℝ) ^ (j * m)

private lemma seeleyMajorant_pos (m j : ℕ) : 0 < seeleyMajorant m j := by
  unfold seeleyMajorant
  exact mul_pos (mul_pos (Real.exp_pos 4) (seeleyHeadBound_pos j))
    (pow_pos (by norm_num) _)

private lemma seeleyMajorant_nonneg (m j : ℕ) : 0 ≤ seeleyMajorant m j :=
  (seeleyMajorant_pos m j).le

private lemma seeleyMajorant_succ (m j : ℕ) :
    seeleyMajorant m (j + 1) =
      seeleyMajorant m j * ((2 : ℝ) ^ (m + 1) / (2 : ℝ) ^ j) := by
  unfold seeleyMajorant
  rw [seeleyHeadBound_succ, pow_add, pow_one]
  have h2j : (2 : ℝ) ^ (2 * j) = (2 : ℝ) ^ j * (2 : ℝ) ^ j := by
    rw [two_mul, pow_add]
  rw [h2j]
  field_simp
  ring

private lemma seeleyMajorant_ratio_le (m j : ℕ) (hj : m + 2 ≤ j) :
    seeleyMajorant m (j + 1) ≤ (1 / 2 : ℝ) * seeleyMajorant m j := by
  have hjpos : 0 < seeleyMajorant m j := seeleyMajorant_pos m j
  have hpow : (2 : ℝ) ^ (m + 1) / (2 : ℝ) ^ j ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (pow_pos (by norm_num) j) (by norm_num : (0 : ℝ) < 2)]
    have : (2 : ℝ) ^ (m + 2) ≤ (2 : ℝ) ^ j :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj
    have hsplit : (2 : ℝ) ^ (m + 2) = (2 : ℝ) ^ (m + 1) * 2 := by
      rw [pow_succ]
    linarith
  rw [seeleyMajorant_succ, mul_comm (1 / 2 : ℝ)]
  exact mul_le_mul_of_nonneg_left hpow hjpos.le

private lemma summable_seeleyMajorant (m : ℕ) : Summable (seeleyMajorant m) := by
  refine summable_of_ratio_norm_eventually_le (by norm_num : (1 / 2 : ℝ) < 1) ?_
  filter_upwards [eventually_ge_atTop (m + 2)] with j hj
  have hpos : 0 ≤ seeleyMajorant m j := seeleyMajorant_nonneg m j
  have hpos' : 0 ≤ seeleyMajorant m (j + 1) := seeleyMajorant_nonneg m (j + 1)
  simp only [Real.norm_eq_abs, abs_of_nonneg hpos, abs_of_nonneg hpos']
  exact seeleyMajorant_ratio_le m j hj

private lemma abs_seeleyCoeffFiniteNat_le (N j : ℕ) :
    |seeleyCoeffFiniteNat N j| ≤ Real.exp 4 * seeleyHeadBound j := by
  by_cases hj : j < N
  · have hprod : 0 ≤ ∏ k ∈ range (N - j - 1), seeleyTailFactor j k :=
      prod_nonneg fun k _ ↦ (seeleyTailFactor_pos j k).le
    have htprod := seeleyTailFactor_prod_range_le j (N - j - 1)
    have hhead : 0 ≤ seeleyHeadBound j := (seeleyHeadBound_pos j).le
    rw [seeleyCoeffFiniteNat_eq_head_mul_prod N j hj, abs_mul, abs_of_nonneg hprod]
    calc
      |seeleyCoeffFinite (j + 1) ⟨j, Nat.lt_succ_self j⟩| *
          ∏ k ∈ range (N - j - 1), seeleyTailFactor j k
          ≤ seeleyHeadBound j *
              ∏ k ∈ range (N - j - 1), seeleyTailFactor j k :=
            mul_le_mul_of_nonneg_right (seeleyCoeffFinite_head_abs_le j) hprod
      _ ≤ seeleyHeadBound j * Real.exp 4 :=
            mul_le_mul_of_nonneg_left htprod hhead
      _ = Real.exp 4 * seeleyHeadBound j := mul_comm _ _
  · have : seeleyCoeffFiniteNat N j = 0 := dif_neg hj
    simp [this]
    exact mul_nonneg (Real.exp_pos 4).le (seeleyHeadBound_pos j).le

private lemma abs_seeleyCoeff_le (j : ℕ) :
    |seeleyCoeff j| ≤ Real.exp 4 * seeleyHeadBound j := by
  have hprod : 0 ≤ ∏' k, seeleyTailFactor j k := seeleyTailFactor_tprod_nonneg j
  unfold seeleyCoeff
  have hhead : 0 ≤ seeleyHeadBound j := (seeleyHeadBound_pos j).le
  rw [abs_mul, abs_of_nonneg hprod]
  calc
    |seeleyCoeffFinite (j + 1) ⟨j, Nat.lt_succ_self j⟩| * ∏' k, seeleyTailFactor j k
        ≤ seeleyHeadBound j * ∏' k, seeleyTailFactor j k :=
          mul_le_mul_of_nonneg_right (seeleyCoeffFinite_head_abs_le j) hprod
    _ ≤ seeleyHeadBound j * Real.exp 4 :=
          mul_le_mul_of_nonneg_left (seeleyTailFactor_tprod_le j) hhead
    _ = Real.exp 4 * seeleyHeadBound j := mul_comm _ _

private lemma abs_seeleyCoeffFiniteNat_weighted_le (N m j : ℕ) :
    abs (seeleyCoeffFiniteNat N j * seeleyNode j ^ m) ≤ seeleyMajorant m j := by
  rw [abs_mul, seeleyNode_pow_abs]
  unfold seeleyMajorant
  exact mul_le_mul_of_nonneg_right (abs_seeleyCoeffFiniteNat_le N j)
    (pow_nonneg (by norm_num) _)

private lemma abs_seeleyCoeff_weighted_le (m j : ℕ) :
    |seeleyCoeff j| * (2 : ℝ) ^ (j * m) ≤ seeleyMajorant m j := by
  unfold seeleyMajorant
  exact mul_le_mul_of_nonneg_right (abs_seeleyCoeff_le j) (pow_nonneg (by norm_num) _)

/-! ## Rapid weighted summability of the infinite coefficients -/

/-- Absolute weighted summability of the exact Seeley coefficients. -/
lemma summable_abs_seeleyCoeff_mul_pow (m : ℕ) :
    Summable fun j : ℕ ↦ |seeleyCoeff j| * (2 : ℝ) ^ (j * m) :=
  (summable_seeleyMajorant m).of_nonneg_of_le
    (fun j ↦ mul_nonneg (abs_nonneg _) (pow_nonneg (by norm_num) _))
    (fun j ↦ abs_seeleyCoeff_weighted_le m j)

lemma summable_seeleyCoeff_mul_seeleyNode_pow (m : ℕ) :
    Summable fun j : ℕ ↦ seeleyCoeff j * seeleyNode j ^ m :=
  (summable_abs_seeleyCoeff_mul_pow m).of_norm_bounded (fun j ↦ by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, seeleyNode_pow_abs])

/-! ## Infinite moment identities via Tannery's theorem -/

private lemma tsum_seeleyCoeffFiniteNat_mul_node_pow (N m : ℕ) (hm : m < N) :
    ∑' j : ℕ, seeleyCoeffFiniteNat N j * seeleyNode j ^ m = 1 := by
  have hzero : ∀ j ∉ range N, seeleyCoeffFiniteNat N j * seeleyNode j ^ m = 0 := by
    intro j hj
    have : ¬ j < N := by simpa [Finset.mem_range] using hj
    simp [seeleyCoeffFiniteNat, this]
  rw [tsum_eq_sum hzero, sum_seeleyCoeffFiniteNat_mul_node_pow N m hm]

/-- The infinite geometric Seeley coefficients reproduce every moment. -/
lemma tsum_seeleyCoeff_mul_seeleyNode_pow (m : ℕ) :
    ∑' j : ℕ, seeleyCoeff j * seeleyNode j ^ m = 1 := by
  let f : ℕ → ℕ → ℝ := fun N j ↦ seeleyCoeffFiniteNat N j * seeleyNode j ^ m
  let g : ℕ → ℝ := fun j ↦ seeleyCoeff j * seeleyNode j ^ m
  have hsum : Summable (seeleyMajorant m) := summable_seeleyMajorant m
  have hab : ∀ j : ℕ, Tendsto (fun N ↦ f N j) atTop (𝓝 (g j)) := by
    intro j
    exact (tendsto_seeleyCoeffFiniteNat j).mul tendsto_const_nhds
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ j, ‖f N j‖ ≤ seeleyMajorant m j :=
    Eventually.of_forall fun N j ↦ by
      simpa [Real.norm_eq_abs, f] using abs_seeleyCoeffFiniteNat_weighted_le N m j
  have hT :=
    tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := f) (g := g)
      (bound := seeleyMajorant m) hsum hab hbound
  have h1 : Tendsto (fun N : ℕ ↦ ∑' j, f N j) atTop (𝓝 (1 : ℝ)) := by
    have hev : ∀ᶠ N : ℕ in atTop, ∑' j, f N j = (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop m] with N hN
      exact tsum_seeleyCoeffFiniteNat_mul_node_pow N m hN
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N hN
    exact hN.symm
  exact tendsto_nhds_unique hT h1

/-! ## Infinite weighted multilinear identity -/

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

private lemma seeley_weighted_multilinear_finiteNat (N m : ℕ) (hm : m < N)
    (M : E [×m]→L[ℝ] F) (u v : Fin m → E) :
    ∑ j ∈ range N, seeleyCoeffFiniteNat N j •
      M (fun i ↦ seeleyNode j • u i + v i) =
      M (fun i ↦ u i + v i) := by
  have h := seeley_weighted_multilinear N m hm M u v
  rw [sum_range]
  convert h using 1
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp [seeleyCoeffFiniteNat]

private lemma seeleyTerm_norm_le (m : ℕ)
    (M : E [×m]→L[ℝ] F) (u v : Fin m → E) (a : ℝ) (j : ℕ) :
    ‖a • M (fun i ↦ seeleyNode j • u i + v i)‖ ≤
      |a| * ‖M‖ * (∏ i : Fin m, (‖u i‖ + ‖v i‖)) * (2 : ℝ) ^ (j * m) := by
  have hsmul : ‖a • M (fun i ↦ seeleyNode j • u i + v i)‖ =
      |a| * ‖M (fun i ↦ seeleyNode j • u i + v i)‖ := by
    simp [norm_smul, Real.norm_eq_abs]
  rw [hsmul]
  have hop := M.le_opNorm (fun i ↦ seeleyNode j • u i + v i)
  have harg : ∀ i : Fin m,
      ‖seeleyNode j • u i + v i‖ ≤ (2 : ℝ) ^ j * (‖u i‖ + ‖v i‖) := by
    intro i
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    calc
      ‖seeleyNode j • u i + v i‖
          ≤ ‖seeleyNode j • u i‖ + ‖v i‖ := norm_add_le _ _
      _ = (2 : ℝ) ^ j * ‖u i‖ + ‖v i‖ := by
            simp [norm_smul, Real.norm_eq_abs, seeleyNode_abs]
      _ ≤ (2 : ℝ) ^ j * ‖u i‖ + (2 : ℝ) ^ j * ‖v i‖ := by
            gcongr
            exact le_mul_of_one_le_left (norm_nonneg (v i)) htwo
      _ = (2 : ℝ) ^ j * (‖u i‖ + ‖v i‖) := by ring
  have hprod :
      (∏ i : Fin m, ‖seeleyNode j • u i + v i‖) ≤
        (∏ i : Fin m, (2 : ℝ) ^ j) * ∏ i : Fin m, (‖u i‖ + ‖v i‖) := by
    rw [← prod_mul_distrib]
    exact prod_le_prod (fun _ _ ↦ norm_nonneg _) fun i _ ↦ harg i
  have hconst : ∏ i : Fin m, (2 : ℝ) ^ j = (2 : ℝ) ^ (j * m) := by
    calc
      ∏ _i : Fin m, (2 : ℝ) ^ j = ((2 : ℝ) ^ j) ^ m := by
        simp [prod_const, Fintype.card_fin]
      _ = (2 : ℝ) ^ (j * m) := (pow_mul (2 : ℝ) j m).symm
  calc
    |a| * ‖M (fun i ↦ seeleyNode j • u i + v i)‖
        ≤ |a| * (‖M‖ * ∏ i : Fin m, ‖seeleyNode j • u i + v i‖) :=
          mul_le_mul_of_nonneg_left hop (abs_nonneg _)
    _ ≤ |a| * (‖M‖ * ((∏ i : Fin m, (2 : ℝ) ^ j) *
          ∏ i : Fin m, (‖u i‖ + ‖v i‖))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hprod (norm_nonneg _)) (abs_nonneg _)
    _ = |a| * (‖M‖ * ((2 : ℝ) ^ (j * m) *
          ∏ i : Fin m, (‖u i‖ + ‖v i‖))) := by
          rw [hconst]
    _ = |a| * ‖M‖ * (∏ i : Fin m, (‖u i‖ + ‖v i‖)) * (2 : ℝ) ^ (j * m) := by
          ring

/-- Infinite geometric reflection identity: the Seeley weights reproduce every
`m`-linear map after simultaneous scaling of the selected normal component. -/
lemma seeley_weighted_multilinear_tsum [CompleteSpace F] (m : ℕ)
    (M : E [×m]→L[ℝ] F) (u v : Fin m → E) :
    (∑' j : ℕ, seeleyCoeff j • M (fun i ↦ seeleyNode j • u i + v i)) =
      M (fun i ↦ u i + v i) := by
  let C : ℝ := ‖M‖ * ∏ i : Fin m, (‖u i‖ + ‖v i‖)
  have hC : 0 ≤ C :=
    mul_nonneg (norm_nonneg _)
      (prod_nonneg fun _ _ ↦ add_nonneg (norm_nonneg _) (norm_nonneg _))
  let bound : ℕ → ℝ := fun j ↦ C * seeleyMajorant m j
  have hsumB : Summable bound := (summable_seeleyMajorant m).mul_left C
  let f : ℕ → ℕ → F := fun N j ↦
    seeleyCoeffFiniteNat N j • M (fun i ↦ seeleyNode j • u i + v i)
  let g : ℕ → F := fun j ↦
    seeleyCoeff j • M (fun i ↦ seeleyNode j • u i + v i)
  have hab : ∀ j : ℕ, Tendsto (fun N ↦ f N j) atTop (𝓝 (g j)) := by
    intro j
    exact (tendsto_seeleyCoeffFiniteNat j).smul_const _
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ j, ‖f N j‖ ≤ bound j :=
    Eventually.of_forall fun N j ↦ by
      have hterm :=
        seeleyTerm_norm_le m M u v (seeleyCoeffFiniteNat N j) j
      have hmaj := abs_seeleyCoeffFiniteNat_le N j
      have hpow : 0 ≤ (2 : ℝ) ^ (j * m) := pow_nonneg (by norm_num) _
      have hexp : 0 ≤ Real.exp 4 := (Real.exp_pos _).le
      have hhead : 0 ≤ seeleyHeadBound j := (seeleyHeadBound_pos j).le
      calc
        ‖f N j‖
            ≤ |seeleyCoeffFiniteNat N j| * C * (2 : ℝ) ^ (j * m) := by
              simpa [C, bound, mul_assoc, mul_left_comm, mul_comm] using hterm
        _ ≤ (Real.exp 4 * seeleyHeadBound j) * C * (2 : ℝ) ^ (j * m) := by
              gcongr
        _ = bound j := by
              simp [bound, seeleyMajorant, C]
              ring
  have hT :=
    tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (f := f) (g := g)
      (bound := bound) hsumB hab hbound
  have h1 : Tendsto (fun N : ℕ ↦ ∑' j, f N j) atTop
      (𝓝 (M (fun i ↦ u i + v i))) := by
    have hev : ∀ᶠ N : ℕ in atTop,
        ∑' j, f N j = M (fun i ↦ u i + v i) := by
      filter_upwards [eventually_gt_atTop m] with N hN
      have hzero : ∀ j ∉ range N, f N j = 0 := by
        intro j hj
        have : ¬ j < N := by simpa [Finset.mem_range] using hj
        simp [f, seeleyCoeffFiniteNat, this]
      rw [tsum_eq_sum hzero]
      exact seeley_weighted_multilinear_finiteNat N m hN M u v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with N hN
    exact hN.symm
  exact tendsto_nhds_unique hT h1

#print axioms summable_abs_seeleyCoeff_mul_pow
#print axioms tsum_seeleyCoeff_mul_seeleyNode_pow
#print axioms seeley_weighted_multilinear_tsum

end LeeSmooth.SeeleyExtension
