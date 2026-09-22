import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LowerConnectionJet
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.QuadraticRicciProduct
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Explicit Ricci lower-order expression involving only the metric and its first derivatives. -/
def ricciLowerOrder (A : E3 →L[ℝ] E3) (P : Fin 3 → E3 →L[ℝ] E3) (i j : Fin 3) : ℝ :=
    (∑ k : Fin 3, (lowerConnectionJet A P k k i j-lowerConnectionJet A P j k i k))+
      quadraticRicciProduct A P i j
/-- The total actual coordinate lower-order term is quadratic in first derivatives. -/
theorem ricci_lower_order_bound (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v) (i j : Fin 3) :
    |ricciLowerOrder A P i j| ≤ (400/c^2)*(∑ l : Fin 3, ‖P l‖)^2 :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let S : ℝ := ∑ l : Fin 3, ‖P l‖
  have hS : 0 ≤ S := by
    dsimp [S]
    positivity
  have hP : ∀ r : Fin 3, ‖P r‖ ≤ S := by
    intro r
    dsimp [S]
    exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
      (f := fun l : Fin 3 => ‖P l‖) (fun l _ => norm_nonneg _) (Finset.mem_univ r)
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc
  have ha : 0 ≤ 5 / c ^ 2 := by positivity
  have hjet : ∀ r k a b : Fin 3,
      |lowerConnectionJet A P r k a b| ≤ (5 / c ^ 2) * ‖P r‖ * S := by
    intro r k a b
    simpa [S] using lower_connection_jet_bound A P c hc hA r k a b
  have hfirst : ∑ k : Fin 3, |lowerConnectionJet A P k k i j| ≤
      (5 / c ^ 2) * S ^ 2 := by
    calc
      ∑ k : Fin 3, |lowerConnectionJet A P k k i j| ≤
          ∑ k : Fin 3, (5 / c ^ 2) * ‖P k‖ * S := by
        exact Finset.sum_le_sum (fun k hk => hjet k k i j)
      _ = (5 / c ^ 2) * S ^ 2 := by
        rw [← Finset.sum_mul, ← Finset.mul_sum]
        dsimp [S]
        ring
  have hsecond : ∑ k : Fin 3, |lowerConnectionJet A P j k i k| ≤
      (15 / c ^ 2) * S ^ 2 := by
    calc
      ∑ k : Fin 3, |lowerConnectionJet A P j k i k| ≤
          ∑ k : Fin 3, (5 / c ^ 2) * ‖P j‖ * S := by
        exact Finset.sum_le_sum (fun k hk => hjet j k i k)
      _ = 3 * ((5 / c ^ 2) * ‖P j‖ * S) := by norm_num
      _ ≤ 3 * ((5 / c ^ 2) * S * S) := by
        gcongr
        exact hP j
      _ = (15 / c ^ 2) * S ^ 2 := by ring
  have hsum : |∑ k : Fin 3,
      (lowerConnectionJet A P k k i j - lowerConnectionJet A P j k i k)| ≤
      (20 / c ^ 2) * S ^ 2 := by
    calc
      |∑ k : Fin 3,
          (lowerConnectionJet A P k k i j - lowerConnectionJet A P j k i k)| ≤
          ∑ k : Fin 3,
            |lowerConnectionJet A P k k i j - lowerConnectionJet A P j k i k| := by
        simpa [Real.norm_eq_abs] using
          (norm_sum_le (Finset.univ : Finset (Fin 3)) (fun k : Fin 3 =>
            lowerConnectionJet A P k k i j - lowerConnectionJet A P j k i k))
      _ ≤ ∑ k : Fin 3,
          (|lowerConnectionJet A P k k i j| +
            |lowerConnectionJet A P j k i k|) := by
        gcongr with k hk
        simpa using (abs_sub_le
          (lowerConnectionJet A P k k i j) (0 : ℝ)
          (lowerConnectionJet A P j k i k))
      _ = (∑ k : Fin 3, |lowerConnectionJet A P k k i j|) +
          (∑ k : Fin 3, |lowerConnectionJet A P j k i k|) := by
        rw [Finset.sum_add_distrib]
      _ ≤ (5 / c ^ 2) * S ^ 2 + (15 / c ^ 2) * S ^ 2 :=
        add_le_add hfirst hsecond
      _ = (20 / c ^ 2) * S ^ 2 := by ring
  have hprod := quadratic_ricci_product_bound A P c hc hA i j
  rw [ricciLowerOrder]
  calc
    |(∑ k : Fin 3,
        (lowerConnectionJet A P k k i j - lowerConnectionJet A P j k i k)) +
        quadraticRicciProduct A P i j| ≤
        |∑ k : Fin 3,
          (lowerConnectionJet A P k k i j - lowerConnectionJet A P j k i k)| +
          |quadraticRicciProduct A P i j| := abs_add_le _ _
    _ ≤ (20 / c ^ 2) * S ^ 2 + (300 / c ^ 2) * S ^ 2 :=
      add_le_add hsum (by simpa using hprod)
    _ = (320 / c ^ 2) * S ^ 2 := by ring
    _ ≤ (400 / c ^ 2) * S ^ 2 := by
      have hcoef : (320 : ℝ) / c ^ 2 ≤ 400 / c ^ 2 := by
        exact (div_le_div_iff_of_pos_right hc2).2 (by norm_num)
      gcongr
    _ = (400 / c ^ 2) * (∑ l : Fin 3, ‖P l‖) ^ 2 := by
      dsimp [S]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
