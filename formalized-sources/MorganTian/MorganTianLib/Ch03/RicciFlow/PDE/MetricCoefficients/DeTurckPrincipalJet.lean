import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateMetricCompatibility
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricInverseBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Principal derivative of the actual Christoffel coordinate expression. -/
def principalConnectionJet (C : Matrix (Fin 3) (Fin 3) ℝ)
    (Q : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) ℝ) (r k i j : Fin 3) : ℝ :=
  (1/2:ℝ)*∑ l : Fin 3, C k l*(Q r i j l+Q r j i l-Q r l i j)
/-- Frozen-coefficient Ricci-DeTurck cancellation for arbitrary symmetric second jets. -/
theorem deturck_principal_jet_cancellation (C : Matrix (Fin 3) (Fin 3) ℝ)
    (hC : ∀ k l : Fin 3, C k l=C l k)
    (Q : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) ℝ)
    (hderiv : ∀ r s i j : Fin 3, Q r s i j=Q s r i j)
    (hmetric : ∀ r s i j : Fin 3, Q r s i j=Q r s j i) (i j : Fin 3) :
    -2*(∑ k : Fin 3, (principalConnectionJet C Q k k i j-principalConnectionJet C Q j k i k)) +
      (∑ p : Fin 3, ∑ q : Fin 3, C p q*(Q i p j q+Q j p i q-Q i j p q)) =
      ∑ p : Fin 3, ∑ q : Fin 3, C p q*Q p q i j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hswap (f : Fin 3 → Fin 3 → ℝ) :
      (∑ p : Fin 3, ∑ q : Fin 3, C p q * f p q) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * f q p := by
    calc
      (∑ p : Fin 3, ∑ q : Fin 3, C p q * f p q) =
          ∑ q : Fin 3, ∑ p : Fin 3, C p q * f p q := Finset.sum_comm
      _ = ∑ q : Fin 3, ∑ p : Fin 3, C q p * f p q := by
        apply Finset.sum_congr rfl
        intro q hq
        apply Finset.sum_congr rfl
        intro p hp
        rw [hC]
      _ = ∑ p : Fin 3, ∑ q : Fin 3, C p q * f q p := rfl
  have hA1 :
      (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q p i j q) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i p j q := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hmetric p i j q, hderiv p i q j, hmetric i p q j]
  have hA2 :
      (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q p j i q) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j p i q := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hmetric p j i q, hderiv p j q i, hmetric j p q i]
  have hB1 :
      (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j i p q) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i j p q := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hmetric j i p q, hderiv j i q p, hmetric i j q p]
  have hB3 :
      (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j q i p) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j p i q := by
    exact (hswap (fun p q => Q j p i q)).symm
  have hA :
      (∑ p : Fin 3, ∑ q : Fin 3,
        C p q * (Q p i j q + Q p j i q - Q p q i j)) =
        ∑ p : Fin 3, ∑ q : Fin 3,
          C p q * (Q i p j q + Q j p i q - Q p q i j) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hmetric p i j q, hderiv p i q j, hmetric i p q j,
      hmetric p j i q, hderiv p j q i, hmetric j p q i]
  have hB :
      (∑ p : Fin 3, ∑ q : Fin 3,
        C p q * (Q j i p q + Q j p i q - Q j q i p)) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i j p q := by
    calc
      (∑ p : Fin 3, ∑ q : Fin 3,
          C p q * (Q j i p q + Q j p i q - Q j q i p)) =
          (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j i p q) +
            (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j p i q) -
            (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j q i p) := by
              simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
                mul_add, mul_sub]
      _ = ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i j p q := by
        rw [hB1, hB3]
        ring
  have hsplit (f g h : Fin 3 → Fin 3 → ℝ) :
      (∑ p : Fin 3, ∑ q : Fin 3, (f p q + g p q - h p q)) =
        (∑ p : Fin 3, ∑ q : Fin 3, f p q) +
          (∑ p : Fin 3, ∑ q : Fin 3, g p q) -
          (∑ p : Fin 3, ∑ q : Fin 3, h p q) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hAdist :
      (∑ p : Fin 3, ∑ q : Fin 3,
        (C p q * Q p i j q + C p q * Q p j i q - C p q * Q p q i j)) =
        ∑ p : Fin 3, ∑ q : Fin 3,
          (C p q * Q i p j q + C p q * Q j p i q - C p q * Q p q i j) := by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hmetric p i j q, hderiv p i q j, hmetric i p q j,
      hmetric p j i q, hderiv p j q i, hmetric j p q i]
  have hBdist :
      (∑ p : Fin 3, ∑ q : Fin 3,
        (C p q * Q j i p q + C p q * Q j p i q - C p q * Q j q i p)) =
        ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i j p q := by
    calc
      (∑ p : Fin 3, ∑ q : Fin 3,
          (C p q * Q j i p q + C p q * Q j p i q - C p q * Q j q i p)) =
          (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j i p q) +
            (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j p i q) -
            (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j q i p) := by
              exact hsplit _ _ _
      _ = ∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i j p q := by
        rw [hB1, hB3]
        ring
  have hAdist_scaled :
      (∑ p : Fin 3, (∑ q : Fin 3,
        (C p q * Q p i j q + C p q * Q p j i q - C p q * Q p q i j)) * (1 / 2)) =
        ∑ p : Fin 3, (∑ q : Fin 3,
          (C p q * Q i p j q + C p q * Q j p i q - C p q * Q p q i j)) * (1 / 2) := by
    calc
      (∑ p : Fin 3, (∑ q : Fin 3,
          (C p q * Q p i j q + C p q * Q p j i q - C p q * Q p q i j)) * (1 / 2)) =
          (∑ p : Fin 3, ∑ q : Fin 3,
            (C p q * Q p i j q + C p q * Q p j i q - C p q * Q p q i j)) * (1 / 2) := by
              rw [Finset.sum_mul]
      _ = (∑ p : Fin 3, ∑ q : Fin 3,
          (C p q * Q i p j q + C p q * Q j p i q - C p q * Q p q i j)) * (1 / 2) := by
            rw [hAdist]
      _ = ∑ p : Fin 3, (∑ q : Fin 3,
          (C p q * Q i p j q + C p q * Q j p i q - C p q * Q p q i j)) * (1 / 2) := by
            rw [Finset.sum_mul]
  have hBdist_scaled :
      (∑ p : Fin 3, (∑ q : Fin 3,
        (C p q * Q j i p q + C p q * Q j p i q - C p q * Q j q i p)) * (1 / 2)) =
        ∑ p : Fin 3, (∑ q : Fin 3, C p q * Q i j p q) * (1 / 2) := by
    calc
      (∑ p : Fin 3, (∑ q : Fin 3,
          (C p q * Q j i p q + C p q * Q j p i q - C p q * Q j q i p)) * (1 / 2)) =
          (∑ p : Fin 3, ∑ q : Fin 3,
            (C p q * Q j i p q + C p q * Q j p i q - C p q * Q j q i p)) * (1 / 2) := by
              rw [Finset.sum_mul]
      _ = (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i j p q) * (1 / 2) := by
            rw [hBdist]
      _ = ∑ p : Fin 3, (∑ q : Fin 3, C p q * Q i j p q) * (1 / 2) := by
            rw [Finset.sum_mul]
  have hsplitA :
      (∑ p : Fin 3, ∑ q : Fin 3,
        (C p q * Q i p j q + C p q * Q j p i q - C p q * Q p q i j)) =
        (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i p j q) +
          (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j p i q) -
          (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q p q i j) := by
    exact hsplit _ _ _
  have hsplitLie :
      (∑ p : Fin 3, ∑ q : Fin 3,
        (C p q * Q i p j q + C p q * Q j p i q - C p q * Q i j p q)) =
        (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i p j q) +
          (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q j p i q) -
          (∑ p : Fin 3, ∑ q : Fin 3, C p q * Q i j p q) := by
    exact hsplit _ _ _
  unfold principalConnectionJet
  simp only [Finset.sum_sub_distrib]
  ring_nf
  rw [hAdist_scaled, hBdist_scaled]
  ring_nf
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  ring_nf
  rw [hsplitA]
  rw [hsplitLie]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
