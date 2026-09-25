import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateDeTurckFourlinear
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped BigOperators
theorem exists_coordinate_deturck_fourlinear :
    ∃ Q : Mat →L[ℝ] Mat →L[ℝ] First →L[ℝ] First →L[ℝ] Mat,
      ‖Q‖ ≤ 10000 ∧ ∀ (h k : Mat) (d e : First) (i j : Idx),
        Q h k d e i j=deturckQuadratic h k d e i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have deturck_bound (h k : Mat) (d e : First) :
      ‖deturckQuadratic h k d e‖ ≤ 2754 * (‖h‖ * ‖k‖ * ‖d‖ * ‖e‖) := by
    have mat_abs (u : Mat) (a b : Idx) : |u a b| ≤ ‖u‖ := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (u a) b).trans (norm_le_pi_norm u a)
    have first_abs (u : First) (a b c : Idx) : |u a b c| ≤ ‖u‖ := by
      rw [← Real.norm_eq_abs]
      exact ((norm_le_pi_norm (u a b) c).trans (norm_le_pi_norm (u a) b)).trans
        (norm_le_pi_norm u a)
    have sum_bound (f : Idx → ℝ) (C : ℝ) (hf : ∀ a, |f a| ≤ C) :
        |∑ a : Idx, f a| ≤ 3 * C := by
      calc
        |∑ a : Idx, f a| ≤ ∑ a : Idx, |f a| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a : Idx, C := Finset.sum_le_sum fun a _ => hf a
        _ = 3 * C := by norm_num [Idx]
    have abs_mul_bound (x y A B : ℝ) (hB : 0 ≤ B)
        (hx : |x| ≤ A) (hy : |y| ≤ B) : |x * y| ≤ A * B := by
      calc
        |x * y| = |x| * |y| := abs_mul _ _
        _ ≤ A * B := mul_le_mul hx hy (abs_nonneg y)
          (le_trans (abs_nonneg x) hx)
    have abs_mul3_bound (x y z A B C : ℝ) (hA : 0 ≤ A)
        (hB : 0 ≤ B) (hC : 0 ≤ C) (hx : |x| ≤ A) (hy : |y| ≤ B)
        (hz : |z| ≤ C) : |x * y * z| ≤ A * B * C := by
      have hxy := abs_mul_bound x y A B hB hx hy
      have hxyz := abs_mul_bound (x * y) z (A * B) C hC hxy hz
      simpa [mul_assoc] using hxyz
    have abs_mul4_bound (x y z w A B C D : ℝ) (hA : 0 ≤ A)
        (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) (hx : |x| ≤ A)
        (hy : |y| ≤ B) (hz : |z| ≤ C) (hw : |w| ≤ D) :
        |x * y * z * w| ≤ A * B * C * D := by
      have hxyz := abs_mul3_bound x y z A B C hA hB hC hx hy hz
      have hxyzw := abs_mul_bound (x * y * z) w (A * B * C) D hD hxyz hw
      simpa [mul_assoc] using hxyzw
    have lower_abs (v : First) (a i j : Idx) :
        |lowerChristoffel v a i j| ≤ 2 * ‖v‖ := by
      unfold lowerChristoffel
      rw [abs_mul]
      have htri : |v i j a + v j i a - v a i j| ≤
          |v i j a| + |v j i a| + |v a i j| := by
        calc
          |v i j a + v j i a - v a i j| ≤
              |v i j a + v j i a| + |v a i j| := by
            simpa [sub_eq_add_neg, abs_neg] using
              (abs_add_le (v i j a + v j i a) (-v a i j))
          _ ≤ |v i j a| + |v j i a| + |v a i j| := by
            nlinarith [abs_add_le (v i j a) (v j i a)]
      have hhalf : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
      rw [hhalf]
      calc
        (1 / 2 : ℝ) * |v i j a + v j i a - v a i j| ≤
            (1 / 2) * (|v i j a| + |v j i a| + |v a i j|) :=
          mul_le_mul_of_nonneg_left htri (by norm_num)
        _ ≤ (1 / 2) * (‖v‖ + ‖v‖ + ‖v‖) := by
          gcongr <;> exact first_abs v _ _ _
        _ ≤ 2 * ‖v‖ := by nlinarith [norm_nonneg v]
    have christoffel_abs (u : Mat) (v : First) (a i j : Idx) :
        |christoffel u v a i j| ≤ 6 * ‖u‖ * ‖v‖ := by
      unfold christoffel
      have hterm (l : Idx) :
          |u a l * lowerChristoffel v l i j| ≤ ‖u‖ * (2 * ‖v‖) := by
        exact abs_mul_bound _ _ _ _ (by positivity) (mat_abs u a l)
          (lower_abs v l i j)
      calc
        |∑ l : Idx, u a l * lowerChristoffel v l i j| ≤
            3 * (‖u‖ * (2 * ‖v‖)) := sum_bound _ _ hterm
        _ = 6 * ‖u‖ * ‖v‖ := by ring
    have inverse_abs (u v : Mat) (w : First) (a i j : Idx) :
        |inverseDerivativePolar u v w a i j| ≤ 9 * ‖u‖ * ‖v‖ * ‖w‖ := by
      let C := ‖u‖ * ‖w‖ * ‖v‖
      have hterm (r s : Idx) :
          |u i r * w a r s * v s j| ≤ C := by
        have h₁ : |u i r * w a r s| ≤ ‖u‖ * ‖w‖ :=
          abs_mul_bound _ _ _ _ (norm_nonneg _) (mat_abs u i r) (first_abs w a r s)
        have h₂ : |(u i r * w a r s) * v s j| ≤ (‖u‖ * ‖w‖) * ‖v‖ :=
          abs_mul_bound _ _ _ _ (norm_nonneg _) h₁ (mat_abs v s j)
        simpa [C, mul_assoc] using h₂
      have hinner (r : Idx) :
          |∑ s : Idx, u i r * w a r s * v s j| ≤ 3 * C :=
        sum_bound _ _ (fun s => hterm r s)
      have houter :
          |∑ r : Idx, ∑ s : Idx, u i r * w a r s * v s j| ≤ 3 * (3 * C) :=
        sum_bound _ _ hinner
      unfold inverseDerivativePolar
      rw [abs_neg]
      calc
        |∑ r : Idx, ∑ s : Idx, u i r * w a r s * v s j| ≤ 3 * (3 * C) := houter
        _ = 9 * ‖u‖ * ‖v‖ * ‖w‖ := by dsimp [C]; ring
    have gamma_abs (u v : Mat) (w x : First) (a r i j : Idx) :
        |gammaQuadratic u v w x a r i j| ≤
          54 * ‖u‖ * ‖v‖ * ‖w‖ * ‖x‖ := by
      let P := ‖u‖ * ‖v‖ * ‖w‖ * ‖x‖
      have hterm (l : Idx) :
          |inverseDerivativePolar u v w a r l * lowerChristoffel x l i j| ≤
            (9 * ‖u‖ * ‖v‖ * ‖w‖) * (2 * ‖x‖) :=
        abs_mul_bound _ _ _ _ (by positivity) (inverse_abs u v w a r l)
          (lower_abs x l i j)
      have hs :
          |∑ l : Idx, inverseDerivativePolar u v w a r l * lowerChristoffel x l i j| ≤
            3 * ((9 * ‖u‖ * ‖v‖ * ‖w‖) * (2 * ‖x‖)) := sum_bound _ _ hterm
      unfold gammaQuadratic
      calc
        |∑ l : Idx, inverseDerivativePolar u v w a r l * lowerChristoffel x l i j| ≤
            3 * ((9 * ‖u‖ * ‖v‖ * ‖w‖) * (2 * ‖x‖)) := hs
        _ = 54 * ‖u‖ * ‖v‖ * ‖w‖ * ‖x‖ := by ring
    let P : ℝ := ‖h‖ * ‖k‖ * ‖d‖ * ‖e‖
    have hP : 0 ≤ P := by positivity
    have ricci_abs (i j : Idx) : |ricciQuadratic h k d e i j| ≤ 972 * P := by
      let C := 54 * P
      have hfirstTerm (a : Idx) :
          |gammaQuadratic h k d e a a i j - gammaQuadratic h k d e j a i a| ≤ 108 * P := by
        calc
          |gammaQuadratic h k d e a a i j - gammaQuadratic h k d e j a i a| ≤
              |gammaQuadratic h k d e a a i j| + |gammaQuadratic h k d e j a i a| :=
                abs_sub _ _
          _ ≤ C + C := add_le_add
            (by simpa [C, P, mul_assoc] using gamma_abs h k d e a a i j)
            (by simpa [C, P, mul_assoc] using gamma_abs h k d e j a i a)
          _ = 108 * P := by dsimp [C]; ring
      have hfirst :
          |∑ a : Idx, (gammaQuadratic h k d e a a i j -
            gammaQuadratic h k d e j a i a)| ≤ 324 * P := by
        calc
          |∑ a : Idx, (gammaQuadratic h k d e a a i j -
              gammaQuadratic h k d e j a i a)| ≤ 3 * (108 * P) :=
            sum_bound _ _ hfirstTerm
          _ = 324 * P := by ring
      have hsecondTerm (a b : Idx) :
          |christoffel h d a a b * christoffel k e b i j -
            christoffel h d a j b * christoffel k e b i a| ≤ 72 * P := by
        have hp₁ : |christoffel h d a a b * christoffel k e b i j| ≤
            (6 * ‖h‖ * ‖d‖) * (6 * ‖k‖ * ‖e‖) :=
          abs_mul_bound _ _ _ _ (by positivity) (christoffel_abs h d a a b)
            (christoffel_abs k e b i j)
        have hp₂ : |christoffel h d a j b * christoffel k e b i a| ≤
            (6 * ‖h‖ * ‖d‖) * (6 * ‖k‖ * ‖e‖) :=
          abs_mul_bound _ _ _ _ (by positivity) (christoffel_abs h d a j b)
            (christoffel_abs k e b i a)
        calc
          _ ≤ |christoffel h d a a b * christoffel k e b i j| +
              |christoffel h d a j b * christoffel k e b i a| := abs_sub _ _
          _ ≤ ((6 * ‖h‖ * ‖d‖) * (6 * ‖k‖ * ‖e‖)) +
              ((6 * ‖h‖ * ‖d‖) * (6 * ‖k‖ * ‖e‖)) := add_le_add hp₁ hp₂
          _ = 72 * P := by dsimp [P]; ring
      have hinner (a : Idx) :
          |∑ b : Idx, (christoffel h d a a b * christoffel k e b i j -
            christoffel h d a j b * christoffel k e b i a)| ≤ 216 * P := by
        calc
          _ ≤ 3 * (72 * P) := sum_bound _ _ (hsecondTerm a)
          _ = 216 * P := by ring
      have hsecond :
          |∑ a : Idx, ∑ b : Idx,
            (christoffel h d a a b * christoffel k e b i j -
              christoffel h d a j b * christoffel k e b i a)| ≤ 648 * P := by
        calc
          _ ≤ 3 * (216 * P) := sum_bound _ _ hinner
          _ = 648 * P := by ring
      unfold ricciQuadratic
      calc
        |(∑ a : Idx, (gammaQuadratic h k d e a a i j -
            gammaQuadratic h k d e j a i a)) +
          ∑ a : Idx, ∑ b : Idx,
            (christoffel h d a a b * christoffel k e b i j -
              christoffel h d a j b * christoffel k e b i a)| ≤
            |∑ a : Idx, (gammaQuadratic h k d e a a i j -
              gammaQuadratic h k d e j a i a)| +
            |∑ a : Idx, ∑ b : Idx,
              (christoffel h d a a b * christoffel k e b i j -
                christoffel h d a j b * christoffel k e b i a)| := abs_add_le _ _
        _ ≤ 324 * P + 648 * P := add_le_add hfirst hsecond
        _ = 972 * P := by ring
    have lie_abs (i j : Idx) : |lieQuadratic h k d e i j| ≤ 810 * P := by
      have hterm₁ (r a b l : Idx) :
          |h a b * k r l * lowerChristoffel d l a b * e r i j| ≤
            ‖h‖ * ‖k‖ * (2 * ‖d‖) * ‖e‖ := by
        exact abs_mul4_bound _ _ _ _ _ _ _ _
          (norm_nonneg _) (norm_nonneg _) (by positivity) (norm_nonneg _)
          (mat_abs h a b) (mat_abs k r l) (lower_abs d l a b) (first_abs e r i j)
      have hsumL (r a b : Idx) :
          |∑ l : Idx, h a b * k r l * lowerChristoffel d l a b * e r i j| ≤
            6 * P := by
        calc
          _ ≤ 3 * (‖h‖ * ‖k‖ * (2 * ‖d‖) * ‖e‖) :=
            sum_bound _ _ (hterm₁ r a b)
          _ = 6 * P := by dsimp [P]; ring
      have hsumB (r a : Idx) :
          |∑ b : Idx, ∑ l : Idx,
            h a b * k r l * lowerChristoffel d l a b * e r i j| ≤ 18 * P := by
        calc
          _ ≤ 3 * (6 * P) := sum_bound _ _ (hsumL r a)
          _ = 18 * P := by ring
      have hsumA (r : Idx) :
          |∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
            h a b * k r l * lowerChristoffel d l a b * e r i j| ≤ 54 * P := by
        calc
          _ ≤ 3 * (18 * P) := sum_bound _ _ (hsumB r)
          _ = 54 * P := by ring
      have hsumR :
          |∑ r : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
            h a b * k r l * lowerChristoffel d l a b * e r i j| ≤ 162 * P := by
        calc
          _ ≤ 3 * (54 * P) := sum_bound _ _ hsumA
          _ = 162 * P := by ring
      have hterm₂ (a b : Idx) :
          |inverseDerivativePolar h k d i a b * lowerChristoffel e j a b +
            inverseDerivativePolar h k d j a b * lowerChristoffel e i a b| ≤ 36 * P := by
        have hp₁ : |inverseDerivativePolar h k d i a b * lowerChristoffel e j a b| ≤
            (9 * ‖h‖ * ‖k‖ * ‖d‖) * (2 * ‖e‖) :=
          abs_mul_bound _ _ _ _ (by positivity) (inverse_abs h k d i a b)
            (lower_abs e j a b)
        have hp₂ : |inverseDerivativePolar h k d j a b * lowerChristoffel e i a b| ≤
            (9 * ‖h‖ * ‖k‖ * ‖d‖) * (2 * ‖e‖) :=
          abs_mul_bound _ _ _ _ (by positivity) (inverse_abs h k d j a b)
            (lower_abs e i a b)
        calc
          _ ≤ |inverseDerivativePolar h k d i a b * lowerChristoffel e j a b| +
              |inverseDerivativePolar h k d j a b * lowerChristoffel e i a b| := abs_add_le _ _
          _ ≤ ((9 * ‖h‖ * ‖k‖ * ‖d‖) * (2 * ‖e‖)) +
              ((9 * ‖h‖ * ‖k‖ * ‖d‖) * (2 * ‖e‖)) := add_le_add hp₁ hp₂
          _ = 36 * P := by dsimp [P]; ring
      have hsumB₂ (a : Idx) :
          |∑ b : Idx, (inverseDerivativePolar h k d i a b * lowerChristoffel e j a b +
            inverseDerivativePolar h k d j a b * lowerChristoffel e i a b)| ≤ 108 * P := by
        calc
          _ ≤ 3 * (36 * P) := sum_bound _ _ (hterm₂ a)
          _ = 108 * P := by ring
      have hsumA₂ :
          |∑ a : Idx, ∑ b : Idx,
            (inverseDerivativePolar h k d i a b * lowerChristoffel e j a b +
              inverseDerivativePolar h k d j a b * lowerChristoffel e i a b)| ≤ 324 * P := by
        calc
          _ ≤ 3 * (108 * P) := sum_bound _ _ hsumB₂
          _ = 324 * P := by ring
      have hterm₃ (i' j' a b r l : Idx) :
          |h a b * d i' j' r * k r l * lowerChristoffel e l a b| ≤
            ‖h‖ * ‖d‖ * ‖k‖ * (2 * ‖e‖) := by
        exact abs_mul4_bound _ _ _ _ _ _ _ _
          (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (by positivity)
          (mat_abs h a b) (first_abs d i' j' r) (mat_abs k r l) (lower_abs e l a b)
      have hsumL₃ (i' j' a b r : Idx) :
          |∑ l : Idx, h a b * d i' j' r * k r l * lowerChristoffel e l a b| ≤ 6 * P := by
        calc
          _ ≤ 3 * (‖h‖ * ‖d‖ * ‖k‖ * (2 * ‖e‖)) := sum_bound _ _ (hterm₃ i' j' a b r)
          _ = 6 * P := by dsimp [P]; ring
      have hsumR₃ (i' j' a b : Idx) :
          |∑ r : Idx, ∑ l : Idx,
            h a b * d i' j' r * k r l * lowerChristoffel e l a b| ≤ 18 * P := by
        calc
          _ ≤ 3 * (6 * P) := sum_bound _ _ (hsumL₃ i' j' a b)
          _ = 18 * P := by ring
      have hsumB₃ (i' j' a : Idx) :
          |∑ b : Idx, ∑ r : Idx, ∑ l : Idx,
            h a b * d i' j' r * k r l * lowerChristoffel e l a b| ≤ 54 * P := by
        calc
          _ ≤ 3 * (18 * P) := sum_bound _ _ (hsumR₃ i' j' a)
          _ = 54 * P := by ring
      have hsumA₃ (i' j' : Idx) :
          |∑ a : Idx, ∑ b : Idx, ∑ r : Idx, ∑ l : Idx,
            h a b * d i' j' r * k r l * lowerChristoffel e l a b| ≤ 162 * P := by
        calc
          _ ≤ 3 * (54 * P) := sum_bound _ _ (hsumB₃ i' j')
          _ = 162 * P := by ring
      have htri : |lieQuadratic h k d e i j| ≤
          |(∑ r : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
              h a b * k r l * lowerChristoffel d l a b * e r i j)| +
          |(∑ a : Idx, ∑ b : Idx,
              (inverseDerivativePolar h k d i a b * lowerChristoffel e j a b +
                inverseDerivativePolar h k d j a b * lowerChristoffel e i a b))| +
          |(∑ a : Idx, ∑ b : Idx, ∑ r : Idx, ∑ l : Idx,
              h a b * d i j r * k r l * lowerChristoffel e l a b)| +
          |(∑ a : Idx, ∑ b : Idx, ∑ r : Idx, ∑ l : Idx,
              h a b * d j i r * k r l * lowerChristoffel e l a b)| := by
        unfold lieQuadratic
        let A := ∑ r : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
          h a b * k r l * lowerChristoffel d l a b * e r i j
        let B := ∑ a : Idx, ∑ b : Idx,
          (inverseDerivativePolar h k d i a b * lowerChristoffel e j a b +
            inverseDerivativePolar h k d j a b * lowerChristoffel e i a b)
        let C := ∑ a : Idx, ∑ b : Idx, ∑ r : Idx, ∑ l : Idx,
          h a b * d i j r * k r l * lowerChristoffel e l a b
        let D := ∑ a : Idx, ∑ b : Idx, ∑ r : Idx, ∑ l : Idx,
          h a b * d j i r * k r l * lowerChristoffel e l a b
        change |A + B - C - D| ≤ |A| + |B| + |C| + |D|
        have hab : |A + B| ≤ |A| + |B| := abs_add_le _ _
        have habc : |A + B - C| ≤ |A| + |B| + |C| := by
          calc
            |A + B - C| ≤ |A + B| + |C| := abs_sub _ _
            _ = |C| + |A + B| := by ring
            _ ≤ |C| + (|A| + |B|) := add_le_add_right hab _
            _ = |A| + |B| + |C| := by ring
        calc
          |A + B - C - D| ≤ |A + B - C| + |D| := abs_sub _ _
          _ = |D| + |A + B - C| := by ring
          _ ≤ |D| + (|A| + |B| + |C|) := add_le_add_right habc _
          _ = |A| + |B| + |C| + |D| := by ring
      calc
        |lieQuadratic h k d e i j| ≤ _ := htri
        _ ≤ 162 * P + 324 * P + 162 * P + 162 * P := by
          nlinarith [hsumR, hsumA₂, hsumA₃ i j, hsumA₃ j i]
        _ = 810 * P := by ring
    have hdet (i j : Idx) : |deturckQuadratic h k d e i j| ≤ 2754 * P := by
      unfold deturckQuadratic
      calc
        |-2 * ricciQuadratic h k d e i j + lieQuadratic h k d e i j| ≤
            |-2 * ricciQuadratic h k d e i j| + |lieQuadratic h k d e i j| := abs_add_le _ _
        _ ≤ 2 * (972 * P) + 810 * P := by
          have hmul : |(-2 : ℝ) * ricciQuadratic h k d e i j| ≤ 2 * (972 * P) := by
            calc
              |(-2 : ℝ) * ricciQuadratic h k d e i j| =
                  2 * |ricciQuadratic h k d e i j| := by simp
              _ ≤ 2 * (972 * P) :=
                mul_le_mul_of_nonneg_left (ricci_abs i j) (by norm_num)
          exact add_le_add hmul (lie_abs i j)
        _ = 2754 * P := by ring
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    simpa [Real.norm_eq_abs, P] using hdet i j
  have lowerChristoffel_add0 (d : First) (a : Idx) (i : Idx) (j : Idx) (d' : First) :
      lowerChristoffel (d + d') a i j = lowerChristoffel d a i j + lowerChristoffel d' a i j := by
    simp only [lowerChristoffel, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have lowerChristoffel_smul0 (d : First) (a : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      lowerChristoffel (c • d) a i j = c * (lowerChristoffel d a i j) := by
    simp only [lowerChristoffel, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have christoffel_add0 (h : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (h' : Mat) :
      christoffel (h + h') d a i j = christoffel h d a i j + christoffel h' d a i j := by
    simp only [christoffel, lowerChristoffel_add0, lowerChristoffel_smul0, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have christoffel_smul0 (h : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      christoffel (c • h) d a i j = c * (christoffel h d a i j) := by
    simp only [christoffel, lowerChristoffel_add0, lowerChristoffel_smul0, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have christoffel_add1 (h : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (d' : First) :
      christoffel h (d + d') a i j = christoffel h d a i j + christoffel h d' a i j := by
    simp only [christoffel, lowerChristoffel_add0, lowerChristoffel_smul0, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have christoffel_smul1 (h : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      christoffel h (c • d) a i j = c * (christoffel h d a i j) := by
    simp only [christoffel, lowerChristoffel_add0, lowerChristoffel_smul0, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have inverseDerivativePolar_add0 (h : Mat) (k : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (h' : Mat) :
      inverseDerivativePolar (h + h') k d a i j = inverseDerivativePolar h k d a i j + inverseDerivativePolar h' k d a i j := by
    simp only [inverseDerivativePolar, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have inverseDerivativePolar_smul0 (h : Mat) (k : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      inverseDerivativePolar (c • h) k d a i j = c * (inverseDerivativePolar h k d a i j) := by
    simp only [inverseDerivativePolar, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have inverseDerivativePolar_add1 (h : Mat) (k : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (k' : Mat) :
      inverseDerivativePolar h (k + k') d a i j = inverseDerivativePolar h k d a i j + inverseDerivativePolar h k' d a i j := by
    simp only [inverseDerivativePolar, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have inverseDerivativePolar_smul1 (h : Mat) (k : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      inverseDerivativePolar h (c • k) d a i j = c * (inverseDerivativePolar h k d a i j) := by
    simp only [inverseDerivativePolar, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have inverseDerivativePolar_add2 (h : Mat) (k : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (d' : First) :
      inverseDerivativePolar h k (d + d') a i j = inverseDerivativePolar h k d a i j + inverseDerivativePolar h k d' a i j := by
    simp only [inverseDerivativePolar, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have inverseDerivativePolar_smul2 (h : Mat) (k : Mat) (d : First) (a : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      inverseDerivativePolar h k (c • d) a i j = c * (inverseDerivativePolar h k d a i j) := by
    simp only [inverseDerivativePolar, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have gammaQuadratic_add0 (h : Mat) (k : Mat) (d : First) (e : First) (a : Idx) (r : Idx) (i : Idx) (j : Idx) (h' : Mat) :
      gammaQuadratic (h + h') k d e a r i j = gammaQuadratic h k d e a r i j + gammaQuadratic h' k d e a r i j := by
    simp only [gammaQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have gammaQuadratic_smul0 (h : Mat) (k : Mat) (d : First) (e : First) (a : Idx) (r : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      gammaQuadratic (c • h) k d e a r i j = c * (gammaQuadratic h k d e a r i j) := by
    simp only [gammaQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have gammaQuadratic_add1 (h : Mat) (k : Mat) (d : First) (e : First) (a : Idx) (r : Idx) (i : Idx) (j : Idx) (k' : Mat) :
      gammaQuadratic h (k + k') d e a r i j = gammaQuadratic h k d e a r i j + gammaQuadratic h k' d e a r i j := by
    simp only [gammaQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have gammaQuadratic_smul1 (h : Mat) (k : Mat) (d : First) (e : First) (a : Idx) (r : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      gammaQuadratic h (c • k) d e a r i j = c * (gammaQuadratic h k d e a r i j) := by
    simp only [gammaQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have gammaQuadratic_add2 (h : Mat) (k : Mat) (d : First) (e : First) (a : Idx) (r : Idx) (i : Idx) (j : Idx) (d' : First) :
      gammaQuadratic h k (d + d') e a r i j = gammaQuadratic h k d e a r i j + gammaQuadratic h k d' e a r i j := by
    simp only [gammaQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have gammaQuadratic_smul2 (h : Mat) (k : Mat) (d : First) (e : First) (a : Idx) (r : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      gammaQuadratic h k (c • d) e a r i j = c * (gammaQuadratic h k d e a r i j) := by
    simp only [gammaQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have gammaQuadratic_add3 (h : Mat) (k : Mat) (d : First) (e : First) (a : Idx) (r : Idx) (i : Idx) (j : Idx) (e' : First) :
      gammaQuadratic h k d (e + e') a r i j = gammaQuadratic h k d e a r i j + gammaQuadratic h k d e' a r i j := by
    simp only [gammaQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have gammaQuadratic_smul3 (h : Mat) (k : Mat) (d : First) (e : First) (a : Idx) (r : Idx) (i : Idx) (j : Idx) (c : ℝ) :
      gammaQuadratic h k d (c • e) a r i j = c * (gammaQuadratic h k d e a r i j) := by
    simp only [gammaQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have ricciQuadratic_add0 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (h' : Mat) :
      ricciQuadratic (h + h') k d e i j = ricciQuadratic h k d e i j + ricciQuadratic h' k d e i j := by
    simp only [ricciQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have ricciQuadratic_smul0 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      ricciQuadratic (c • h) k d e i j = c * (ricciQuadratic h k d e i j) := by
    simp only [ricciQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have ricciQuadratic_add1 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (k' : Mat) :
      ricciQuadratic h (k + k') d e i j = ricciQuadratic h k d e i j + ricciQuadratic h k' d e i j := by
    simp only [ricciQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have ricciQuadratic_smul1 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      ricciQuadratic h (c • k) d e i j = c * (ricciQuadratic h k d e i j) := by
    simp only [ricciQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have ricciQuadratic_add2 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (d' : First) :
      ricciQuadratic h k (d + d') e i j = ricciQuadratic h k d e i j + ricciQuadratic h k d' e i j := by
    simp only [ricciQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have ricciQuadratic_smul2 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      ricciQuadratic h k (c • d) e i j = c * (ricciQuadratic h k d e i j) := by
    simp only [ricciQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have ricciQuadratic_add3 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (e' : First) :
      ricciQuadratic h k d (e + e') i j = ricciQuadratic h k d e i j + ricciQuadratic h k d e' i j := by
    simp only [ricciQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have ricciQuadratic_smul3 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      ricciQuadratic h k d (c • e) i j = c * (ricciQuadratic h k d e i j) := by
    simp only [ricciQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have lieQuadratic_add0 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (h' : Mat) :
      lieQuadratic (h + h') k d e i j = lieQuadratic h k d e i j + lieQuadratic h' k d e i j := by
    simp only [lieQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have lieQuadratic_smul0 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      lieQuadratic (c • h) k d e i j = c * (lieQuadratic h k d e i j) := by
    simp only [lieQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have lieQuadratic_add1 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (k' : Mat) :
      lieQuadratic h (k + k') d e i j = lieQuadratic h k d e i j + lieQuadratic h k' d e i j := by
    simp only [lieQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have lieQuadratic_smul1 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      lieQuadratic h (c • k) d e i j = c * (lieQuadratic h k d e i j) := by
    simp only [lieQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have lieQuadratic_add2 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (d' : First) :
      lieQuadratic h k (d + d') e i j = lieQuadratic h k d e i j + lieQuadratic h k d' e i j := by
    simp only [lieQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have lieQuadratic_smul2 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      lieQuadratic h k (c • d) e i j = c * (lieQuadratic h k d e i j) := by
    simp only [lieQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have lieQuadratic_add3 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (e' : First) :
      lieQuadratic h k d (e + e') i j = lieQuadratic h k d e i j + lieQuadratic h k d e' i j := by
    simp only [lieQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have lieQuadratic_smul3 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      lieQuadratic h k d (c • e) i j = c * (lieQuadratic h k d e i j) := by
    simp only [lieQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have deturckQuadratic_add0 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (h' : Mat) :
      deturckQuadratic (h + h') k d e i j = deturckQuadratic h k d e i j + deturckQuadratic h' k d e i j := by
    simp only [deturckQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, lieQuadratic_add0, lieQuadratic_smul0, lieQuadratic_add1, lieQuadratic_smul1, lieQuadratic_add2, lieQuadratic_smul2, lieQuadratic_add3, lieQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have deturckQuadratic_smul0 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      deturckQuadratic (c • h) k d e i j = c * (deturckQuadratic h k d e i j) := by
    simp only [deturckQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, lieQuadratic_add0, lieQuadratic_smul0, lieQuadratic_add1, lieQuadratic_smul1, lieQuadratic_add2, lieQuadratic_smul2, lieQuadratic_add3, lieQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have deturckQuadratic_add1 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (k' : Mat) :
      deturckQuadratic h (k + k') d e i j = deturckQuadratic h k d e i j + deturckQuadratic h k' d e i j := by
    simp only [deturckQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, lieQuadratic_add0, lieQuadratic_smul0, lieQuadratic_add1, lieQuadratic_smul1, lieQuadratic_add2, lieQuadratic_smul2, lieQuadratic_add3, lieQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have deturckQuadratic_smul1 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      deturckQuadratic h (c • k) d e i j = c * (deturckQuadratic h k d e i j) := by
    simp only [deturckQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, lieQuadratic_add0, lieQuadratic_smul0, lieQuadratic_add1, lieQuadratic_smul1, lieQuadratic_add2, lieQuadratic_smul2, lieQuadratic_add3, lieQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have deturckQuadratic_add2 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (d' : First) :
      deturckQuadratic h k (d + d') e i j = deturckQuadratic h k d e i j + deturckQuadratic h k d' e i j := by
    simp only [deturckQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, lieQuadratic_add0, lieQuadratic_smul0, lieQuadratic_add1, lieQuadratic_smul1, lieQuadratic_add2, lieQuadratic_smul2, lieQuadratic_add3, lieQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have deturckQuadratic_smul2 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      deturckQuadratic h k (c • d) e i j = c * (deturckQuadratic h k d e i j) := by
    simp only [deturckQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, lieQuadratic_add0, lieQuadratic_smul0, lieQuadratic_add1, lieQuadratic_smul1, lieQuadratic_add2, lieQuadratic_smul2, lieQuadratic_add3, lieQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have deturckQuadratic_add3 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (e' : First) :
      deturckQuadratic h k d (e + e') i j = deturckQuadratic h k d e i j + deturckQuadratic h k d e' i j := by
    simp only [deturckQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, lieQuadratic_add0, lieQuadratic_smul0, lieQuadratic_add1, lieQuadratic_smul1, lieQuadratic_add2, lieQuadratic_smul2, lieQuadratic_add3, lieQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have deturckQuadratic_smul3 (h : Mat) (k : Mat) (d : First) (e : First) (i : Idx) (j : Idx) (c : ℝ) :
      deturckQuadratic h k d (c • e) i j = c * (deturckQuadratic h k d e i j) := by
    simp only [deturckQuadratic, lowerChristoffel_add0, lowerChristoffel_smul0, christoffel_add0, christoffel_smul0, christoffel_add1, christoffel_smul1, inverseDerivativePolar_add0, inverseDerivativePolar_smul0, inverseDerivativePolar_add1, inverseDerivativePolar_smul1, inverseDerivativePolar_add2, inverseDerivativePolar_smul2, gammaQuadratic_add0, gammaQuadratic_smul0, gammaQuadratic_add1, gammaQuadratic_smul1, gammaQuadratic_add2, gammaQuadratic_smul2, gammaQuadratic_add3, gammaQuadratic_smul3, ricciQuadratic_add0, ricciQuadratic_smul0, ricciQuadratic_add1, ricciQuadratic_smul1, ricciQuadratic_add2, ricciQuadratic_smul2, ricciQuadratic_add3, ricciQuadratic_smul3, lieQuadratic_add0, lieQuadratic_smul0, lieQuadratic_add1, lieQuadratic_smul1, lieQuadratic_add2, lieQuadratic_smul2, lieQuadratic_add3, lieQuadratic_smul3, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum, Finset.sum_mul] <;> ring_nf <;> simp only [mul_assoc, mul_left_comm, mul_comm] <;> ring
  have assemble (f : Mat → Mat → First → First → Mat) (C : ℝ) (hC : 0 ≤ C)
      (a0 : ∀ h h' k d e, f (h+h') k d e = f h k d e + f h' k d e)
      (s0 : ∀ (c : ℝ) h k d e, f (c • h) k d e = c • f h k d e)
      (a1 : ∀ h k k' d e, f h (k+k') d e = f h k d e + f h k' d e)
      (s1 : ∀ (c : ℝ) h k d e, f h (c • k) d e = c • f h k d e)
      (a2 : ∀ h k d d' e, f h k (d+d') e = f h k d e + f h k d' e)
      (s2 : ∀ (c : ℝ) h k d e, f h k (c • d) e = c • f h k d e)
      (a3 : ∀ h k d e e', f h k d (e+e') = f h k d e + f h k d e')
      (s3 : ∀ (c : ℝ) h k d e, f h k d (c • e) = c • f h k d e)
      (bound : ∀ h k d e, ‖f h k d e‖ ≤ C*‖h‖*‖k‖*‖d‖*‖e‖) :
      ∃ Q : Mat →L[ℝ] Mat →L[ℝ] First →L[ℝ] First →L[ℝ] Mat,
        ‖Q‖ ≤ C ∧ ∀ h k d e, Q h k d e = f h k d e := by
    let L4 (h k : Mat) (d : First) : First →L[ℝ] Mat :=
      LinearMap.toContinuousLinearMap
        { toFun := f h k d
          map_add' := a3 h k d
          map_smul' := fun c e => s3 c h k d e }
    let L3 (h k : Mat) : First →L[ℝ] First →L[ℝ] Mat :=
      LinearMap.toContinuousLinearMap
        { toFun := L4 h k
          map_add' := by intro d d'; apply ContinuousLinearMap.ext; intro e; exact a2 h k d d' e
          map_smul' := by intro c d; apply ContinuousLinearMap.ext; intro e; exact s2 c h k d e }
    let L2 (h : Mat) : Mat →L[ℝ] First →L[ℝ] First →L[ℝ] Mat :=
      LinearMap.toContinuousLinearMap
        { toFun := L3 h
          map_add' := by
            intro k k'; apply ContinuousLinearMap.ext; intro d
            apply ContinuousLinearMap.ext; intro e; exact a1 h k k' d e
          map_smul' := by
            intro c k; apply ContinuousLinearMap.ext; intro d
            apply ContinuousLinearMap.ext; intro e; exact s1 c h k d e }
    let Q : Mat →L[ℝ] Mat →L[ℝ] First →L[ℝ] First →L[ℝ] Mat :=
      LinearMap.toContinuousLinearMap
        { toFun := L2
          map_add' := by
            intro h h'; apply ContinuousLinearMap.ext; intro k
            apply ContinuousLinearMap.ext; intro d
            apply ContinuousLinearMap.ext; intro e; exact a0 h h' k d e
          map_smul' := by
            intro c h; apply ContinuousLinearMap.ext; intro k
            apply ContinuousLinearMap.ext; intro d
            apply ContinuousLinearMap.ext; intro e; exact s0 c h k d e }
    have b4 (h k : Mat) (d : First) : ‖L4 h k d‖ ≤ C*‖h‖*‖k‖*‖d‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun e => bound h k d e)
    have b3 (h k : Mat) : ‖L3 h k‖ ≤ C*‖h‖*‖k‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun d => b4 h k d)
    have b2 (h : Mat) : ‖L2 h‖ ≤ C*‖h‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun k => b3 h k)
    exact ⟨Q, ContinuousLinearMap.opNorm_le_bound _ hC b2, fun h k d e => rfl⟩
  have a0 (h : Mat) (h' : Mat) (k : Mat) (d : First) (e : First) : deturckQuadratic (h+h') k d e = deturckQuadratic h k d e + deturckQuadratic h' k d e := by
    funext i j
    exact deturckQuadratic_add0 h k d e i j h'
  have s0 (c : ℝ) (h k : Mat) (d e : First) : deturckQuadratic (c • h) k d e = c • (deturckQuadratic h k d e) := by
    funext i j
    exact deturckQuadratic_smul0 h k d e i j c
  have a1 (h : Mat) (k : Mat) (k' : Mat) (d : First) (e : First) : deturckQuadratic h (k+k') d e = deturckQuadratic h k d e + deturckQuadratic h k' d e := by
    funext i j
    exact deturckQuadratic_add1 h k d e i j k'
  have s1 (c : ℝ) (h k : Mat) (d e : First) : deturckQuadratic h (c • k) d e = c • (deturckQuadratic h k d e) := by
    funext i j
    exact deturckQuadratic_smul1 h k d e i j c
  have a2 (h : Mat) (k : Mat) (d : First) (d' : First) (e : First) : deturckQuadratic h k (d+d') e = deturckQuadratic h k d e + deturckQuadratic h k d' e := by
    funext i j
    exact deturckQuadratic_add2 h k d e i j d'
  have s2 (c : ℝ) (h k : Mat) (d e : First) : deturckQuadratic h k (c • d) e = c • (deturckQuadratic h k d e) := by
    funext i j
    exact deturckQuadratic_smul2 h k d e i j c
  have a3 (h : Mat) (k : Mat) (d : First) (e : First) (e' : First) : deturckQuadratic h k d (e+e') = deturckQuadratic h k d e + deturckQuadratic h k d e' := by
    funext i j
    exact deturckQuadratic_add3 h k d e i j e'
  have s3 (c : ℝ) (h k : Mat) (d e : First) : deturckQuadratic h k d (c • e) = c • (deturckQuadratic h k d e) := by
    funext i j
    exact deturckQuadratic_smul3 h k d e i j c
  have bnd (h k : Mat) (d e : First) :
      ‖deturckQuadratic h k d e‖ ≤ (2754:ℝ)*‖h‖*‖k‖*‖d‖*‖e‖ := by
    simpa only [mul_assoc] using deturck_bound h k d e
  obtain ⟨Q, hQ, hvalue⟩ := assemble deturckQuadratic 2754 (by norm_num)
    a0 s0 a1 s1 a2 s2 a3 s3 bnd
  refine ⟨Q, hQ.trans (by norm_num), ?_⟩
  intro h k d e i j
  exact congrArg (fun m : Mat => m i j) (hvalue h k d e)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateDeTurckFourlinear
