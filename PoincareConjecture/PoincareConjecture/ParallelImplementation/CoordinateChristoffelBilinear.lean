import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateChristoffelBilinear
open scoped BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_coordinate_christoffel_bilinear
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) :
    ∃ Γ : (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ]
        (E3 →L[ℝ] E3 →L[ℝ] E3), ‖Γ‖ ≤ 27*‖E‖ ∧
      (∀ a d u v k, (Γ a d u v) k = (1/2:ℝ) *
        ∑ l : Fin 3, (a (EuclideanSpace.single l 1)) k *
          (inner ℝ (E (d u) v) (EuclideanSpace.single l 1) +
           inner ℝ (E (d v) u) (EuclideanSpace.single l 1) -
           inner ℝ (E (d (EuclideanSpace.single l 1)) u) v)) ∧
      ((∀ q u v, inner ℝ (E q u) v = inner ℝ (E q v) u) →
        ∀ a d u v, Γ a d u v = Γ a d v u) :=
/- SWARM_PROOF_BEGIN -/
by
  let coeff (d : E3 →L[ℝ] E6) (u v : E3) (l : Fin 3) : ℝ :=
    inner ℝ (E (d u) v) (EuclideanSpace.single l 1) +
      inner ℝ (E (d v) u) (EuclideanSpace.single l 1) -
      inner ℝ (E (d (EuclideanSpace.single l 1)) u) v
  let formula (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) (u v : E3) : E3 :=
    (1 / 2 : ℝ) • ∑ l : Fin 3, coeff d u v l • a (EuclideanSpace.single l 1)
  have h_inner (q : E6) (x y : E3) :
      |inner ℝ (E q x) y| ≤ ‖E‖ * ‖q‖ * ‖x‖ * ‖y‖ := by
    calc
      |inner ℝ (E q x) y| ≤ ‖E q x‖ * ‖y‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖E q‖ * ‖x‖) * ‖y‖ := by
        gcongr
        exact (E q).le_opNorm x
      _ ≤ (‖E‖ * ‖q‖ * ‖x‖) * ‖y‖ := by
        gcongr
        exact E.le_opNorm q
  have h_coeff (d : E3 →L[ℝ] E6) (u v : E3) (l : Fin 3) :
      |coeff d u v l| ≤ 3 * (‖E‖ * ‖d‖ * ‖u‖ * ‖v‖) := by
    let e : E3 := EuclideanSpace.single l 1
    have he : ‖e‖ = 1 := by simp [e]
    have hdu : ‖d u‖ ≤ ‖d‖ * ‖u‖ := d.le_opNorm u
    have hdv : ‖d v‖ ≤ ‖d‖ * ‖v‖ := d.le_opNorm v
    have hde : ‖d e‖ ≤ ‖d‖ := by
      calc
        ‖d e‖ ≤ ‖d‖ * ‖e‖ := d.le_opNorm e
        _ = ‖d‖ := by rw [he]; ring
    have h₁ : |inner ℝ (E (d u) v) e| ≤ ‖E‖ * ‖d‖ * ‖u‖ * ‖v‖ := by
      calc
        |inner ℝ (E (d u) v) e| ≤ ‖E‖ * ‖d u‖ * ‖v‖ * ‖e‖ := h_inner (d u) v e
        _ = ‖E‖ * ‖d u‖ * ‖v‖ := by rw [he]; ring
        _ ≤ ‖E‖ * (‖d‖ * ‖u‖) * ‖v‖ := by gcongr
        _ = ‖E‖ * ‖d‖ * ‖u‖ * ‖v‖ := by ring
    have h₂ : |inner ℝ (E (d v) u) e| ≤ ‖E‖ * ‖d‖ * ‖u‖ * ‖v‖ := by
      calc
        |inner ℝ (E (d v) u) e| ≤ ‖E‖ * ‖d v‖ * ‖u‖ * ‖e‖ := h_inner (d v) u e
        _ = ‖E‖ * ‖d v‖ * ‖u‖ := by rw [he]; ring
        _ ≤ ‖E‖ * (‖d‖ * ‖v‖) * ‖u‖ := by gcongr
        _ = ‖E‖ * ‖d‖ * ‖u‖ * ‖v‖ := by ring
    have h₃ : |inner ℝ (E (d e) u) v| ≤ ‖E‖ * ‖d‖ * ‖u‖ * ‖v‖ := by
      calc
        |inner ℝ (E (d e) u) v| ≤ ‖E‖ * ‖d e‖ * ‖u‖ * ‖v‖ := h_inner (d e) u v
        _ ≤ ‖E‖ * ‖d‖ * ‖u‖ * ‖v‖ := by gcongr
    dsimp [coeff]
    calc
      |inner ℝ (E (d u) v) (EuclideanSpace.single l 1) +
          inner ℝ (E (d v) u) (EuclideanSpace.single l 1) -
          inner ℝ (E (d (EuclideanSpace.single l 1)) u) v|
          ≤ |inner ℝ (E (d u) v) e| + |inner ℝ (E (d v) u) e| +
            |inner ℝ (E (d e) u) v| := by
        have heq : e = EuclideanSpace.single l 1 := rfl
        rw [heq]
        calc
          |(inner ℝ (E (d u) v) e + inner ℝ (E (d v) u) e) -
              inner ℝ (E (d e) u) v|
              ≤ |inner ℝ (E (d u) v) e + inner ℝ (E (d v) u) e| +
                |inner ℝ (E (d e) u) v| := abs_sub _ _
          _ ≤ |inner ℝ (E (d u) v) e| + |inner ℝ (E (d v) u) e| +
                |inner ℝ (E (d e) u) v| := by
            gcongr
            exact abs_add_le _ _
      _ ≤ (‖E‖ * ‖d‖ * ‖u‖ * ‖v‖) +
          (‖E‖ * ‖d‖ * ‖u‖ * ‖v‖) +
          (‖E‖ * ‖d‖ * ‖u‖ * ‖v‖) := by gcongr
      _ = 3 * (‖E‖ * ‖d‖ * ‖u‖ * ‖v‖) := by ring
  have h_formula (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) (u v : E3) :
      ‖formula a d u v‖ ≤ 27 * ‖E‖ * ‖a‖ * ‖d‖ * ‖u‖ * ‖v‖ := by
    calc
      ‖formula a d u v‖ = ‖(1 / 2 : ℝ)‖ *
          ‖∑ l : Fin 3, coeff d u v l • a (EuclideanSpace.single l 1)‖ := norm_smul _ _
      _ ≤ (1 / 2 : ℝ) *
          ∑ l : Fin 3, ‖coeff d u v l • a (EuclideanSpace.single l 1)‖ := by
        rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)
      _ ≤ (1 / 2 : ℝ) *
          ∑ l : Fin 3, (3 * (‖E‖ * ‖d‖ * ‖u‖ * ‖v‖)) * ‖a‖ := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro l hl
        calc
          ‖coeff d u v l • a (EuclideanSpace.single l 1)‖ =
              |coeff d u v l| * ‖a (EuclideanSpace.single l 1)‖ := norm_smul _ _
          _ ≤ (3 * (‖E‖ * ‖d‖ * ‖u‖ * ‖v‖)) *
              ‖a (EuclideanSpace.single l 1)‖ :=
                mul_le_mul_of_nonneg_right (h_coeff d u v l) (norm_nonneg _)
          _ ≤ (3 * (‖E‖ * ‖d‖ * ‖u‖ * ‖v‖)) * ‖a‖ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc
              ‖a (EuclideanSpace.single l 1)‖ ≤ ‖a‖ * ‖EuclideanSpace.single l 1‖ :=
                a.le_opNorm _
              _ = ‖a‖ := by simp
      _ = (9 / 2 : ℝ) * (‖E‖ * ‖a‖ * ‖d‖ * ‖u‖ * ‖v‖) := by
        simp [Finset.sum_const, Fintype.card_fin]
        ring
      _ ≤ 27 * ‖E‖ * ‖a‖ * ‖d‖ * ‖u‖ * ‖v‖ := by
        have hp : 0 ≤ ‖E‖ * ‖a‖ * ‖d‖ * ‖u‖ * ‖v‖ := by positivity
        nlinarith
  have hc_add_d (d₁ d₂ : E3 →L[ℝ] E6) (u v : E3) (l : Fin 3) :
      coeff (d₁ + d₂) u v l = coeff d₁ u v l + coeff d₂ u v l := by
    simp only [coeff, add_apply, map_add, inner_add_left]
    abel
  have hc_smul_d (c : ℝ) (d : E3 →L[ℝ] E6) (u v : E3) (l : Fin 3) :
      coeff (c • d) u v l = c * coeff d u v l := by
    simp only [coeff, smul_apply, map_smul, inner_smul_left_eq_smul, smul_eq_mul]
    ring
  have hc_add_u (d : E3 →L[ℝ] E6) (u₁ u₂ v : E3) (l : Fin 3) :
      coeff d (u₁ + u₂) v l = coeff d u₁ v l + coeff d u₂ v l := by
    simp only [coeff, map_add, add_apply, inner_add_left]
    abel
  have hc_smul_u (c : ℝ) (d : E3 →L[ℝ] E6) (u v : E3) (l : Fin 3) :
      coeff d (c • u) v l = c * coeff d u v l := by
    simp only [coeff, map_smul, smul_apply, inner_smul_left_eq_smul, smul_eq_mul]
    ring
  have hc_add_v (d : E3 →L[ℝ] E6) (u v₁ v₂ : E3) (l : Fin 3) :
      coeff d u (v₁ + v₂) l = coeff d u v₁ l + coeff d u v₂ l := by
    simp only [coeff, map_add, add_apply, inner_add_left, inner_add_right]
    abel
  have hc_smul_v (c : ℝ) (d : E3 →L[ℝ] E6) (u v : E3) (l : Fin 3) :
      coeff d u (c • v) l = c * coeff d u v l := by
    simp only [coeff, map_smul, smul_apply, inner_smul_left_eq_smul,
      inner_smul_right_eq_smul, smul_eq_mul]
    ring
  have hf_add_a (a₁ a₂ : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) (u v : E3) :
      formula (a₁ + a₂) d u v = formula a₁ d u v + formula a₂ d u v := by
    simp only [formula, add_apply, smul_add, Finset.sum_add_distrib]
  have hf_smul_a (c : ℝ) (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) (u v : E3) :
      formula (c • a) d u v = c • formula a d u v := by
    dsimp [formula]
    simp only [smul_apply]
    calc
      (1 / 2 : ℝ) •
          ∑ l : Fin 3, coeff d u v l • (c • a (EuclideanSpace.single l 1)) =
          (1 / 2 : ℝ) •
            ∑ l : Fin 3, c • (coeff d u v l • a (EuclideanSpace.single l 1)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro l hl
        exact smul_comm (coeff d u v l) c (a (EuclideanSpace.single l 1))
      _ = c • ((1 / 2 : ℝ) •
          ∑ l : Fin 3, coeff d u v l • a (EuclideanSpace.single l 1)) := by
        rw [← Finset.smul_sum]
        exact smul_comm (1 / 2 : ℝ) c _
  have hf_add_d (a : E3 →L[ℝ] E3) (d₁ d₂ : E3 →L[ℝ] E6) (u v : E3) :
      formula a (d₁ + d₂) u v = formula a d₁ u v + formula a d₂ u v := by
    simp only [formula, hc_add_d, add_smul, Finset.sum_add_distrib, smul_add]
  have hf_smul_d (c : ℝ) (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) (u v : E3) :
      formula a (c • d) u v = c • formula a d u v := by
    dsimp [formula]
    simp only [hc_smul_d, mul_smul]
    rw [← Finset.smul_sum]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hf_add_u (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) (u₁ u₂ v : E3) :
      formula a d (u₁ + u₂) v = formula a d u₁ v + formula a d u₂ v := by
    simp only [formula, hc_add_u, add_smul, Finset.sum_add_distrib, smul_add]
  have hf_smul_u (c : ℝ) (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) (u v : E3) :
      formula a d (c • u) v = c • formula a d u v := by
    dsimp [formula]
    simp only [hc_smul_u, mul_smul]
    rw [← Finset.smul_sum]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  have hf_add_v (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) (u v₁ v₂ : E3) :
      formula a d u (v₁ + v₂) = formula a d u v₁ + formula a d u v₂ := by
    simp only [formula, hc_add_v, add_smul, Finset.sum_add_distrib, smul_add]
  have hf_smul_v (c : ℝ) (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) (u v : E3) :
      formula a d u (c • v) = c • formula a d u v := by
    dsimp [formula]
    simp only [hc_smul_v, mul_smul]
    rw [← Finset.smul_sum]
    rw [smul_smul, smul_smul]
    congr 1
    ring
  let bilinear (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) :
      E3 →ₗ[ℝ] E3 →ₗ[ℝ] E3 :=
    { toFun := fun u =>
        { toFun := fun v => formula a d u v
          map_add' := by
            intro v w
            exact hf_add_v a d u v w
          map_smul' := by
            intro c v
            exact hf_smul_v c a d u v }
      map_add' := by
        intro u w
        ext v k
        exact congrArg (fun x : E3 => x k) (hf_add_u a d u w v)
      map_smul' := by
        intro c u
        ext v k
        exact congrArg (fun x : E3 => x k) (hf_smul_u c a d u v) }
  let continuousBilinear (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) :
      E3 →L[ℝ] E3 →L[ℝ] E3 :=
    (bilinear a d).mkContinuous₂ (27 * ‖E‖ * ‖a‖ * ‖d‖) (by
      intro u v
      simpa [bilinear] using h_formula a d u v)
  let raw : (E3 →L[ℝ] E3) →ₗ[ℝ]
      (E3 →L[ℝ] E6) →ₗ[ℝ] (E3 →L[ℝ] E3 →L[ℝ] E3) :=
    { toFun := fun a =>
        { toFun := fun d => continuousBilinear a d
          map_add' := by
            intro d₁ d₂
            ext u v k
            exact congrArg (fun x : E3 => x k) (hf_add_d a d₁ d₂ u v)
          map_smul' := by
            intro c d
            ext u v k
            exact congrArg (fun x : E3 => x k) (hf_smul_d c a d u v) }
      map_add' := by
        intro a₁ a₂
        ext d u v k
        exact congrArg (fun x : E3 => x k) (hf_add_a a₁ a₂ d u v)
      map_smul' := by
        intro c a
        ext d u v k
        exact congrArg (fun x : E3 => x k) (hf_smul_a c a d u v) }
  have h_raw (a : E3 →L[ℝ] E3) (d : E3 →L[ℝ] E6) :
      ‖raw a d‖ ≤ (27 * ‖E‖) * ‖a‖ * ‖d‖ := by
    dsimp [raw, continuousBilinear]
    exact LinearMap.mkContinuous₂_norm_le _ (by positivity) (by
      intro u v
      simpa [bilinear] using h_formula a d u v)
  let Γ := raw.mkContinuous₂ (27 * ‖E‖) (by
    intro a d
    exact h_raw a d)
  refine ⟨Γ, ?_, ?_, ?_⟩
  · exact LinearMap.mkContinuous₂_norm_le _ (by positivity) (by
      intro a d
      exact h_raw a d)
  · intro a d u v k
    simp [Γ, raw, continuousBilinear, bilinear, formula, coeff,
      LinearMap.mkContinuous₂_apply, mul_comm, mul_left_comm]
  · intro hs a d u v
    have hcoeff_swap (l : Fin 3) : coeff d u v l = coeff d v u l := by
      dsimp [coeff]
      rw [hs (d (EuclideanSpace.single l 1)) u v]
      ring
    have hformula_swap : formula a d u v = formula a d v u := by
      simp only [formula]
      congr 1
      apply Finset.sum_congr rfl
      intro l hl
      rw [hcoeff_swap l]
    ext k
    change (formula a d u v) k = (formula a d v u) k
    exact congrArg (fun x : E3 => x k) hformula_swap
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateChristoffelBilinear
