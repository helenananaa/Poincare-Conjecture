import PoincareConjecture.ParallelMath
set_option autoImplicit false
noncomputable section
open Set
open PoincareConjecture.ParallelMath
/-- A zero scalar coefficient recovers the actual linear comparison solution. -/
example (k a s t : ℝ) : comparisonSolution (fun _ => 0) k a s t = a-k*(t-s) := by
  simp [comparisonSolution, rateIntegral]
/-- An actual three-dimensional identity matrix satisfies the positive quadratic-form criterion. -/
example (v : Fin 3 → ℝ) (hv : v ≠ 0) :
    0 < quadraticForm (fun i j : Fin 3 => if i=j then 1 else 0) v := by
  apply positive_quadraticForm_of_small_frobenius_error
    (fun i j : Fin 3 => if i=j then 1 else 0) 0 (by norm_num) (by norm_num) ?_ v hv
  simp
/-- Zero-edge metric chains are included, rather than silently excluded. -/
example {X : Type*} [PseudoMetricSpace X] (x : X) : dist x x ≤ (0 : ℝ) := by
  exact finite_chain_dist_le 0 (fun _ => x)
/-- Gram-area discriminant is jointly continuous in the three entries. -/
example : Continuous fun p : ℝ × ℝ × ℝ => Real.sqrt (p.1 * p.2.1 - p.2.2 ^ 2) :=
  PoincareConjecture.ParallelMath.Transfer.continuous_sqrt_gram_det
/-- The Euclidean identity on `ℝ³` has Gram determinant 1, inside the ε=0 distortion interval. -/
example :
    let G := fun i j : Fin 3 => if i = j then (1 : ℝ) else 0
    (1 - (0 : ℝ)) ^ 3 ≤ (Matrix.of G).det ∧ (Matrix.of G).det ≤ (1 + (0 : ℝ)) ^ 3 := by
  refine volume_form_det_distortion (fun i j : Fin 3 => if i = j then (1 : ℝ) else 0)
    0 (by norm_num) (by norm_num) (fun i j => by simp [eq_comm]) ?_
  intro v
  have hsum :
      quadraticForm (fun i j : Fin 3 => if i = j then (1 : ℝ) else 0) v =
        ∑ i, (v i) ^ 2 := by
    unfold quadraticForm
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Finset.sum_ite_eq, pow_two]
  simp [hsum]
/-- A trivial free product has trivial factors. -/
example {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    (h : ∀ x : Monoid.CoprodI G, x = 1) (i : ι) (g : G i) : g = 1 :=
  coprodI_trivial_implies_factor_trivial h i g
