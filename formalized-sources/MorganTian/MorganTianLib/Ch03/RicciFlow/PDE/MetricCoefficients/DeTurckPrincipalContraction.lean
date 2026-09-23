import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Symmetric contraction combines the two half principal terms of the Lie derivative. -/
theorem deturck_principal_contraction (C : Matrix (Fin 3) (Fin 3) ℝ)
    (Q : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hC : ∀ p q : Fin 3, C p q = C q p)
    (hQ : ∀ a b m n : Fin 3, Q a b m n = Q b a m n) (i j : Fin 3) :
    (1 / 2 : ℝ) * (∑ p : Fin 3, ∑ q : Fin 3,
      C p q * (Q i p j q + Q i q j p - Q i j p q)) +
    (1 / 2 : ℝ) * (∑ p : Fin 3, ∑ q : Fin 3,
      C p q * (Q j p i q + Q j q i p - Q j i p q)) =
    ∑ p : Fin 3, ∑ q : Fin 3,
      C p q * (Q i p j q + Q j p i q - Q i j p q) :=
/- SWARM_PROOF_BEGIN -/
by
  have hswap_i :
      (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i q j p) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i p j q := by
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun p q : Fin 3 => C p q * Q i q j p)]
    simpa only [hC]
  have hswap_j :
      (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j q i p) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j p i q := by
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
      (f := fun p q : Fin 3 => C p q * Q j q i p)]
    simpa only [hC]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_add, mul_sub]
  have hneg :
      (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j i p q) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i j p q := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    simpa only [hQ]
  rw [hswap_i, hswap_j, hneg]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
