import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateRicciQuadraticSymmetry
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem ricci_quadratic_symmetric
    (h : Mat) (d : First) (hh : ∀ i j, h i j = h j i)
    (hd : ∀ a i j, d a i j = d a j i) :

    ∀ i j : Idx, ricciQuadratic h h d d i j = ricciQuadratic h h d d j i :=
/- SWARM_PROOF_BEGIN -/
by
  intro i j
  have hlower : ∀ k p q, lowerChristoffel d k p q = lowerChristoffel d k q p := by
    intro k p q
    unfold lowerChristoffel
    rw [hd k p q]
    ring
  have hchrist : ∀ k p q, christoffel h d k p q = christoffel h d k q p := by
    intro k p q
    unfold christoffel
    apply Finset.sum_congr rfl
    intro l hl
    exact congrArg (fun x : ℝ => h k l * x) (hlower l p q)

  let H : Matrix Idx Idx ℝ := h
  let D : Idx → Matrix Idx Idx ℝ := fun a u v => d a u v
  let K : Idx → Matrix Idx Idx ℝ := fun a => H * D a * H
  have hHt : Matrix.transpose H = H := by
    ext a b
    exact hh b a
  have hDt (a : Idx) : Matrix.transpose (D a) = D a := by
    ext u v
    exact hd a v u
  have hKt (a : Idx) : Matrix.transpose (K a) = K a := by
    dsimp [K]
    simp [Matrix.transpose_mul, hHt, hDt a]
    rw [← Matrix.mul_assoc]
  have hKsym (a r l : Idx) : K a r l = K a l r := by
    have he := congrArg (fun M : Matrix Idx Idx ℝ => M r l) (hKt a)
    simpa only [Matrix.transpose_apply] using he.symm
  have hKentry (a r l : Idx) :
      (∑ u : Idx, ∑ v : Idx, h r u * d a u v * h v l) = K a r l := by
    dsimp [K, H, D]
    simp only [Matrix.mul_apply]
    have hmul (x : Idx) :
        (∑ j : Idx, h r j * d a j x) * h x l =
          (∑ j : Idx, h r j * d a j x * h x l) := by
      simpa using
        (Finset.sum_mul (Finset.univ : Finset Idx)
          (fun j : Idx => h r j * d a j x) (h x l))
    calc
      (∑ u : Idx, ∑ v : Idx, h r u * d a u v * h v l) =
          ∑ x : Idx, ∑ j : Idx, h r j * d a j x * h x l := by
        rw [Finset.sum_comm]
      _ = ∑ x : Idx, (∑ j : Idx, h r j * d a j x) * h x l := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (hmul x).symm

  have hgammaFormula (a r p q : Idx) :
      gammaQuadratic h h d d a r p q =
        -(∑ l : Idx, K a r l * lowerChristoffel d l p q) := by
    calc
      gammaQuadratic h h d d a r p q =
          -(∑ l : Idx,
            (∑ u : Idx, ∑ v : Idx, h r u * d a u v * h v l) *
              lowerChristoffel d l p q) := by
        simp [gammaQuadratic, inverseDerivativePolar, neg_mul, Finset.sum_neg_distrib]
      _ = -(∑ l : Idx, K a r l * lowerChristoffel d l p q) := by
        congr 1
        apply Finset.sum_congr rfl
        intro l hl
        rw [hKentry a r l]
  have hgammaPair (a r p q : Idx) :
      gammaQuadratic h h d d a r p q = gammaQuadratic h h d d a r q p := by
    unfold gammaQuadratic
    apply Finset.sum_congr rfl
    intro l hl
    exact congrArg (fun x : ℝ => inverseDerivativePolar h h d a r l * x)
      (hlower l p q)

  have hgammaDiag (p q : Idx) :
      (∑ a : Idx, gammaQuadratic h h d d a a p q) =
        (∑ a : Idx, gammaQuadratic h h d d a a q p) := by
    apply Finset.sum_congr rfl
    intro a ha
    exact hgammaPair a a p q

  have hQsum (p q : Idx) :
      (∑ a : Idx, gammaQuadratic h h d d q a p a) =
        -(∑ a : Idx, ∑ l : Idx,
          K q a l * lowerChristoffel d l p a) := by
    calc
      (∑ a : Idx, gammaQuadratic h h d d q a p a) =
          ∑ a : Idx, -(∑ l : Idx, K q a l * lowerChristoffel d l p a) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hgammaFormula q a p a
      _ = -(∑ a : Idx, ∑ l : Idx, K q a l * lowerChristoffel d l p a) := by
        rw [Finset.sum_neg_distrib]

  have hYZ (p q : Idx) :
      (∑ a : Idx, ∑ l : Idx, K q a l * d a p l) =
        (∑ a : Idx, ∑ l : Idx, K q a l * d l p a) := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    let f : Idx × Idx → ℝ := fun x => K q x.1 x.2 * d x.2 p x.1
    change (∑ x : Idx × Idx, K q x.1 x.2 * d x.1 p x.2) =
      (∑ x : Idx × Idx, f x)
    have hreindex :
        (∑ x : Idx × Idx, f x) = (∑ x : Idx × Idx, f (Equiv.prodComm Idx Idx x)) := by
      exact (Equiv.sum_comp (Equiv.prodComm Idx Idx) f).symm
    calc
      (∑ x : Idx × Idx, K q x.1 x.2 * d x.1 p x.2) =
          ∑ x : Idx × Idx, f (Equiv.prodComm Idx Idx x) := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [f]
        rw [hKsym q x.1 x.2]
      _ = ∑ x : Idx × Idx, f x := hreindex.symm

  have hcontract (p q : Idx) :
      (∑ a : Idx, ∑ l : Idx, K q a l * lowerChristoffel d l p a) =
        (1 / 2 : ℝ) * (∑ a : Idx, ∑ l : Idx, K q a l * d p a l) := by
    calc
      (∑ a : Idx, ∑ l : Idx, K q a l * lowerChristoffel d l p a) =
          ∑ a : Idx, ∑ l : Idx,
            (1 / 2 : ℝ) *
              (K q a l * d p a l + K q a l * d a p l - K q a l * d l p a) := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro l hl
        simp only [lowerChristoffel]
        ring
      _ = (1 / 2 : ℝ) *
          ((∑ a : Idx, ∑ l : Idx, K q a l * d p a l) +
           (∑ a : Idx, ∑ l : Idx, K q a l * d a p l) -
           (∑ a : Idx, ∑ l : Idx, K q a l * d l p a)) := by
        simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        simp only [← Finset.mul_sum]
      _ = (1 / 2 : ℝ) * (∑ a : Idx, ∑ l : Idx, K q a l * d p a l) := by
        rw [hYZ p q]
        ring

  have hXtrace (p q : Idx) :
      (∑ a : Idx, ∑ l : Idx, K q a l * d p a l) =
        Matrix.trace (K q * D p) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, D]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro l hl
    exact congrArg (fun x : ℝ => K q a l * x) (hd p a l)

  have htraceSym (p q : Idx) :
      Matrix.trace (K q * D p) = Matrix.trace (K p * D q) := by
    calc
      Matrix.trace (K q * D p) = Matrix.trace (Matrix.transpose (K q * D p)) := by
        rw [← Matrix.trace_transpose]
      _ = Matrix.trace (D p * H * D q * H) := by
        congr 1
        dsimp [K]
        simp [Matrix.transpose_mul, hHt, hDt p, hDt q, Matrix.mul_assoc]
      _ = Matrix.trace (K p * D q) := by
        rw [Matrix.trace_mul_cycle]
        congr 1
        dsimp [K]
        rw [← Matrix.mul_assoc]

  have hQsym (p q : Idx) :
      (∑ a : Idx, gammaQuadratic h h d d q a p a) =
        (∑ a : Idx, gammaQuadratic h h d d p a q a) := by
    calc
      (∑ a : Idx, gammaQuadratic h h d d q a p a) =
          -((1 / 2 : ℝ) * (∑ a : Idx, ∑ l : Idx, K q a l * d p a l)) := by
        rw [hQsum p q, hcontract p q]
      _ = -((1 / 2 : ℝ) * (∑ a : Idx, ∑ l : Idx, K p a l * d q a l)) := by
        rw [hXtrace p q, hXtrace q p, htraceSym p q]
      _ = (∑ a : Idx, gammaQuadratic h h d d p a q a) := by
        rw [hQsum q p, hcontract q p]

  have hprodTrace (p q : Idx) :
      (∑ a : Idx, ∑ b : Idx,
        christoffel h d a a b * christoffel h d b p q) =
        (∑ a : Idx, ∑ b : Idx,
        christoffel h d a a b * christoffel h d b q p) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    exact congrArg (fun x : ℝ => christoffel h d a a b * x) (hchrist b p q)

  have hprodCross (p q : Idx) :
      (∑ a : Idx, ∑ b : Idx,
        christoffel h d a q b * christoffel h d b p a) =
        (∑ a : Idx, ∑ b : Idx,
        christoffel h d a p b * christoffel h d b q a) := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    let f : Idx × Idx → ℝ := fun x =>
      christoffel h d x.1 q x.2 * christoffel h d x.2 p x.1
    change (∑ x : Idx × Idx, f x) =
      (∑ x : Idx × Idx, christoffel h d x.1 p x.2 * christoffel h d x.2 q x.1)
    have hreindex :
        (∑ x : Idx × Idx, f x) =
          (∑ x : Idx × Idx, f (Equiv.prodComm Idx Idx x)) := by
      exact (Equiv.sum_comp (Equiv.prodComm Idx Idx) f).symm
    calc
      (∑ x : Idx × Idx, f x) =
          ∑ x : Idx × Idx, f (Equiv.prodComm Idx Idx x) := hreindex
      _ = ∑ x : Idx × Idx,
          christoffel h d x.1 p x.2 * christoffel h d x.2 q x.1 := by
        apply Finset.sum_congr rfl
        intro x hx
        dsimp [f]
        ring

  have hgammaAll (p q : Idx) :
      (∑ a : Idx,
        (gammaQuadratic h h d d a a p q - gammaQuadratic h h d d q a p a)) =
      (∑ a : Idx,
        (gammaQuadratic h h d d a a q p - gammaQuadratic h h d d p a q a)) := by
    calc
      _ = (∑ a : Idx, gammaQuadratic h h d d a a p q) -
            (∑ a : Idx, gammaQuadratic h h d d q a p a) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ a : Idx, gammaQuadratic h h d d a a q p) -
            (∑ a : Idx, gammaQuadratic h h d d p a q a) := by
        rw [hgammaDiag p q, hQsym p q]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]

  have hprodAll (p q : Idx) :
      (∑ a : Idx, ∑ b : Idx,
        (christoffel h d a a b * christoffel h d b p q -
         christoffel h d a q b * christoffel h d b p a)) =
      (∑ a : Idx, ∑ b : Idx,
        (christoffel h d a a b * christoffel h d b q p -
         christoffel h d a p b * christoffel h d b q a)) := by
    calc
      _ = (∑ a : Idx, ∑ b : Idx,
            christoffel h d a a b * christoffel h d b p q) -
          (∑ a : Idx, ∑ b : Idx,
            christoffel h d a q b * christoffel h d b p a) := by
        simp only [Finset.sum_sub_distrib]
      _ = (∑ a : Idx, ∑ b : Idx,
            christoffel h d a a b * christoffel h d b q p) -
          (∑ a : Idx, ∑ b : Idx,
            christoffel h d a p b * christoffel h d b q a) := by
        rw [hprodTrace p q, hprodCross p q]
      _ = _ := by
        simp only [← Finset.sum_sub_distrib]

  change
    (∑ a : Idx,
      (gammaQuadratic h h d d a a i j - gammaQuadratic h h d d j a i a)) +
      ∑ a : Idx, ∑ b : Idx,
        (christoffel h d a a b * christoffel h d b i j -
         christoffel h d a j b * christoffel h d b i a) =
    (∑ a : Idx,
      (gammaQuadratic h h d d a a j i - gammaQuadratic h h d d i a j a)) +
      ∑ a : Idx, ∑ b : Idx,
        (christoffel h d a a b * christoffel h d b j i -
         christoffel h d a i b * christoffel h d b j a)
  rw [hgammaAll i j, hprodAll i j]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateRicciQuadraticSymmetry
