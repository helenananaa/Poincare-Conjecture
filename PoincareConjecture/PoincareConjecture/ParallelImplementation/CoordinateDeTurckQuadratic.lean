import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateDeTurckQuadratic
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped BigOperators
theorem coordinate_deturck_quadratic
    (g h : Mat) (d : First)
    (hg : ∀ i j : Idx, g i j=g j i)
    (hgh : ∀ i j : Idx, (∑ k : Idx, g i k*h k j) = if i=j then 1 else 0) :
    ∀ i j : Idx, lieQuadraticRaw g h d i j = lieQuadratic h h d d i j :=
/- SWARM_PROOF_BEGIN -/
by
  intro i j
  have hcontract (j : Idx) (C : Idx → ℝ) :
      (∑ k : Idx, g k j * (∑ l : Idx, h k l * C l)) = C j := by
    have hsymmetric (l : Idx) :
        (∑ k : Idx, g k j * h k l) = if j = l then 1 else 0 := by
      calc
        (∑ k : Idx, g k j * h k l) = ∑ k : Idx, g j k * h k l := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [hg k j]
        _ = if j = l then 1 else 0 := hgh j l
    calc
      (∑ k : Idx, g k j * (∑ l : Idx, h k l * C l)) =
          ∑ l : Idx, (∑ k : Idx, g k j * h k l) * C l := by
        calc
          (∑ k : Idx, g k j * (∑ l : Idx, h k l * C l)) =
              ∑ k : Idx, ∑ l : Idx, g k j * (h k l * C l) := by
            simp only [Finset.mul_sum]
          _ = ∑ l : Idx, ∑ k : Idx, g k j * (h k l * C l) := by
            rw [Finset.sum_comm]
          _ = ∑ l : Idx, ∑ k : Idx, (g k j * h k l) * C l := by
            apply Finset.sum_congr rfl
            intro l hl
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = ∑ l : Idx, (∑ k : Idx, g k j * h k l) * C l := by
            simp only [Finset.sum_mul]
      _ = ∑ l : Idx, (if j = l then 1 else 0) * C l := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [hsymmetric l]
      _ = C j := by simp
  have hinverseExpand (a k l : Idx) :
      inverseDerivativePolar h h d a k l =
        -(∑ r : Idx, h k r * (∑ s : Idx, d a r s * h s l)) := by
    unfold inverseDerivativePolar
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro r hr
    calc
      (∑ s : Idx, h k r * d a r s * h s l) =
          ∑ s : Idx, h k r * (d a r s * h s l) := by
        apply Finset.sum_congr rfl
        intro s hs
        ring
      _ = h k r * (∑ s : Idx, d a r s * h s l) := by
        rw [Finset.mul_sum]
  have hinverseContract (a j l : Idx) :
      (∑ k : Idx, g k j * inverseDerivativePolar h h d a k l) =
        -(∑ s : Idx, d a j s * h s l) := by
    calc
      (∑ k : Idx, g k j * inverseDerivativePolar h h d a k l) =
          ∑ k : Idx, g k j *
            (-(∑ r : Idx, h k r * (∑ s : Idx, d a r s * h s l))) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hinverseExpand]
      _ = -(∑ k : Idx, g k j *
            (∑ r : Idx, h k r * (∑ s : Idx, d a r s * h s l))) := by
        simp only [mul_neg, Finset.sum_neg_distrib]
      _ = -(∑ s : Idx, d a j s * h s l) := by
        congr 1
        exact hcontract j (fun r => ∑ s : Idx, d a r s * h s l)
  have hsumFactor (j : Idx) (F : Idx → Idx → ℝ) (C : Idx → ℝ) :
      (∑ k : Idx, g k j * (∑ l : Idx, F k l * C l)) =
        ∑ l : Idx, (∑ k : Idx, g k j * F k l) * C l := by
    calc
      (∑ k : Idx, g k j * (∑ l : Idx, F k l * C l)) =
          ∑ k : Idx, ∑ l : Idx, g k j * (F k l * C l) := by
        simp only [Finset.mul_sum]
      _ = ∑ l : Idx, ∑ k : Idx, g k j * (F k l * C l) := by
        rw [Finset.sum_comm]
      _ = ∑ l : Idx, ∑ k : Idx, (g k j * F k l) * C l := by
        apply Finset.sum_congr rfl
        intro l hl
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = ∑ l : Idx, (∑ k : Idx, g k j * F k l) * C l := by
        simp only [Finset.sum_mul]
  have hchristoffelContract (a b j : Idx) :
      (∑ k : Idx, g k j * christoffel h d k a b) = lowerChristoffel d j a b := by
    unfold christoffel
    exact hcontract j (fun l => lowerChristoffel d l a b)
  have hgammaContract (a b c j : Idx) :
      (∑ k : Idx, g k j * gammaQuadratic h h d d a k b c) =
        -(∑ r : Idx, ∑ l : Idx,
          d a j r * h r l * lowerChristoffel d l b c) := by
    unfold gammaQuadratic
    rw [hsumFactor j (fun k l => inverseDerivativePolar h h d a k l)
      (fun l => lowerChristoffel d l b c)]
    simp_rw [hinverseContract]
    rw [show (∑ l : Idx,
        (-(∑ r : Idx, d a j r * h r l)) * lowerChristoffel d l b c) =
        -(∑ r : Idx, ∑ l : Idx,
        d a j r * h r l * lowerChristoffel d l b c) by
        simp only [neg_mul, Finset.sum_neg_distrib, Finset.sum_mul]
        rw [Finset.sum_comm]]
  have hvectorContract (a j : Idx) :
      (∑ k : Idx, g k j * vectorQuadratic h d a k) =
        (∑ p : Idx, ∑ q : Idx,
          inverseDerivativePolar h h d a p q * lowerChristoffel d j p q) +
        (∑ p : Idx, ∑ q : Idx,
          h p q * (-(∑ r : Idx, ∑ l : Idx,
            d a j r * h r l * lowerChristoffel d l p q))) := by
    unfold vectorQuadratic
    have hswap :
        (∑ k : Idx, g k j *
          (∑ p : Idx, ∑ q : Idx,
            (inverseDerivativePolar h h d a p q * christoffel h d k p q +
              h p q * gammaQuadratic h h d d a k p q))) =
        ∑ p : Idx, ∑ q : Idx, ∑ k : Idx,
          g k j * (inverseDerivativePolar h h d a p q * christoffel h d k p q +
            h p q * gammaQuadratic h h d d a k p q) := by
      calc
        _ = ∑ k : Idx, ∑ p : Idx, ∑ q : Idx,
              g k j * (inverseDerivativePolar h h d a p q * christoffel h d k p q +
                h p q * gammaQuadratic h h d d a k p q) := by
            simp only [Finset.mul_sum]
        _ = ∑ p : Idx, ∑ k : Idx, ∑ q : Idx,
              g k j * (inverseDerivativePolar h h d a p q * christoffel h d k p q +
                h p q * gammaQuadratic h h d d a k p q) := by
            rw [Finset.sum_comm]
        _ = ∑ p : Idx, ∑ q : Idx, ∑ k : Idx,
              g k j * (inverseDerivativePolar h h d a p q * christoffel h d k p q +
                h p q * gammaQuadratic h h d d a k p q) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [Finset.sum_comm]
    have hinner (p q : Idx) :
        (∑ k : Idx, g k j *
          (inverseDerivativePolar h h d a p q * christoffel h d k p q +
            h p q * gammaQuadratic h h d d a k p q)) =
          inverseDerivativePolar h h d a p q *
              (∑ k : Idx, g k j * christoffel h d k p q) +
            h p q * (∑ k : Idx, g k j * gammaQuadratic h h d d a k p q) := by
      calc
        _ = ∑ k : Idx,
              (inverseDerivativePolar h h d a p q *
                  (g k j * christoffel h d k p q) +
                h p q * (g k j * gammaQuadratic h h d d a k p q)) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
        _ = (∑ k : Idx, inverseDerivativePolar h h d a p q *
              (g k j * christoffel h d k p q)) +
            ∑ k : Idx, h p q * (g k j * gammaQuadratic h h d d a k p q) := by
            rw [Finset.sum_add_distrib]
        _ = _ := by rw [Finset.mul_sum, Finset.mul_sum]
    rw [hswap]
    simp_rw [hinner, hchristoffelContract, hgammaContract]
    simp only [Finset.sum_add_distrib]
  have hgammaVector (a j : Idx) :
      (∑ p : Idx, ∑ q : Idx,
        h p q * (-(∑ r : Idx, ∑ l : Idx,
          d a j r * h r l * lowerChristoffel d l p q))) =
        -(∑ p : Idx, ∑ q : Idx, ∑ r : Idx, ∑ l : Idx,
          h p q * d a j r * h r l * lowerChristoffel d l p q) := by
    simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hdrift (i j : Idx) :
      (∑ k : Idx, deturckVector h d k * d k i j) =
        ∑ r : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
          h a b * h r l * lowerChristoffel d l a b * d r i j := by
    unfold deturckVector christoffel
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro l hl
    ring
  have hmetricSym (i : Idx) :
      (∑ k : Idx, g i k * vectorQuadratic h d j k) =
        ∑ k : Idx, g k i * vectorQuadratic h d j k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hg i k]
  unfold lieQuadraticRaw
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hdrift i j, hvectorContract i j, hmetricSym i, hvectorContract j i]
  rw [hgammaVector i j, hgammaVector j i]
  simp only [lieQuadratic, Finset.sum_add_distrib]
  ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CoordinateDeTurckQuadratic
