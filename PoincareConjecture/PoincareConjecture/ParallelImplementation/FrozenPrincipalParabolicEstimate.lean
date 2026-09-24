import PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.FrozenPrincipalDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FrozenPrincipalParabolicEstimate
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped Topology BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Actual inverse-metric principal error has small amplitude and controlled parabolic increments. -/
theorem frozen_principal_parabolic_estimate
    (T alpha c delta H M N : ℝ) (hc : 0 < c) (hd : 0 ≤ delta) (hdc : delta ≤ c/2)
    (hH : 0 ≤ H) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (A0 : E3 →L[ℝ] E3) (A : Slab T → E3 →L[ℝ] E3)
    (Q : Slab T → Fin 3 → Fin 3 → E6)
    (hA0 : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A0 v) v)
    (hclose : ∀ p, ‖A p-A0‖ ≤ delta)
    (hAH : ∀ p q, ‖A p-A q‖ ≤ H*(‖p.2-q.2‖+Real.sqrt |(p.1:ℝ)-(q.1:ℝ)|)^alpha)
    (hQ : ∀ p i j, ‖Q p i j‖ ≤ M)
    (hQH : ∀ p q i j, ‖Q p i j-Q q i j‖ ≤ N*(‖p.2-q.2‖+Real.sqrt |(p.1:ℝ)-(q.1:ℝ)|)^alpha) :
    let F : Slab T → E6 := fun p => ∑ i : Fin 3, ∑ j : Fin 3,
      (((A p).inverse-A0.inverse) (EuclideanSpace.single j 1)) i • Q p i j
    (∀ p, ‖F p‖ ≤ (36/c^2)*delta*M) ∧
      ∀ p q, ‖F p-F q‖ ≤ (36/c^2)*(delta*N+H*M)*
        (‖p.2-q.2‖+Real.sqrt |(p.1:ℝ)-(q.1:ℝ)|)^alpha :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  have sum_bound (f : Fin 3 → Fin 3 → ℝ) (K : ℝ)
      (hf : ∀ i j, f i j ≤ K) :
      (∑ i : Fin 3, ∑ j : Fin 3, f i j) ≤ 9 * K := by
    calc
      (∑ i : Fin 3, ∑ j : Fin 3, f i j) ≤
          ∑ i : Fin 3, ∑ j : Fin 3, K := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact hf i j
      _ = 9 * K := by simp [Finset.sum_const]; ring
  constructor
  · intro p
    have hpclose := hclose p
    have hAp : ‖A p - A0‖ ≤ c / 2 := hpclose.trans hdc
    have hA0close : ‖A0 - A0‖ ≤ c / 2 := by
      simp only [sub_self, norm_zero]
      linarith [hc]
    have hQsum : (∑ i : Fin 3, ∑ j : Fin 3, ‖Q p i j‖) ≤ 9 * M :=
      sum_bound (fun i j => ‖Q p i j‖) M (fun i j => hQ p i j)
    have hprincipal := MorganTianLib.MetricCoefficient.frozen_principal_difference
      A0 (A p) A0 c hc hA0 hAp hA0close (Q p) (fun _ _ => 0)
    have hraw : ‖∑ i : Fin 3, ∑ j : Fin 3,
          (((A p).inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q p i j‖ ≤
        4 / c ^ 2 * ‖A p - A0‖ *
          (∑ i : Fin 3, ∑ j : Fin 3, ‖Q p i j‖) := by
      simpa using hprincipal
    have hk : 0 ≤ 4 / c ^ 2 := by positivity
    have h9M : 0 ≤ 9 * M := by positivity
    calc
      ‖∑ i : Fin 3, ∑ j : Fin 3,
          (((A p).inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q p i j‖
          ≤ 4 / c ^ 2 * ‖A p - A0‖ *
              (∑ i : Fin 3, ∑ j : Fin 3, ‖Q p i j‖) := hraw
      _
          ≤ 4 / c ^ 2 * ‖A p - A0‖ * (9 * M) := by
            exact mul_le_mul_of_nonneg_left hQsum
              (mul_nonneg hk (norm_nonneg (A p - A0)))
      _ ≤ 4 / c ^ 2 * delta * (9 * M) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpclose hk) h9M
      _ = (36 / c ^ 2) * delta * M := by ring
  · intro p q
    let ρ : ℝ := ‖p.2 - q.2‖ + Real.sqrt |(p.1 : ℝ) - (q.1 : ℝ)|
    have hρ : 0 ≤ ρ := by
      dsimp [ρ]
      positivity
    have hρpow : 0 ≤ ρ ^ alpha := Real.rpow_nonneg hρ _
    have hpclose : ‖A p - A0‖ ≤ c / 2 := (hclose p).trans hdc
    have hqclose : ‖A q - A0‖ ≤ c / 2 := (hclose q).trans hdc
    have hsumDiff :
        (∑ i : Fin 3, ∑ j : Fin 3, ‖Q p i j - Q q i j‖) ≤
          9 * (N * ρ ^ alpha) :=
      sum_bound (fun i j => ‖Q p i j - Q q i j‖) (N * ρ ^ alpha)
        (fun i j => by simpa [ρ] using hQH p q i j)
    have hsumQ : (∑ i : Fin 3, ∑ j : Fin 3, ‖Q q i j‖) ≤ 9 * M :=
      sum_bound (fun i j => ‖Q q i j‖) M (fun i j => hQ q i j)
    have hAinc : ‖A p - A q‖ ≤ H * ρ ^ alpha := by
      simpa [ρ] using hAH p q
    have hprincipal := MorganTianLib.MetricCoefficient.frozen_principal_difference
      A0 (A p) (A q) c hc hA0 hpclose hqclose (Q p) (Q q)
    have hraw :
        ‖(∑ i : Fin 3, ∑ j : Fin 3,
          (((A p).inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q p i j) -
          (∑ i : Fin 3, ∑ j : Fin 3,
          (((A q).inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q q i j)‖ ≤
          4 / c ^ 2 * ‖A p - A0‖ *
            (∑ i : Fin 3, ∑ j : Fin 3, ‖Q p i j - Q q i j‖) +
          4 / c ^ 2 * ‖A p - A q‖ *
            (∑ i : Fin 3, ∑ j : Fin 3, ‖Q q i j‖) := by
      simpa using hprincipal
    have hk : 0 ≤ 4 / c ^ 2 := by positivity
    have h9M : 0 ≤ 9 * M := by positivity
    have hterm1 :
        4 / c ^ 2 * ‖A p - A0‖ *
            (∑ i : Fin 3, ∑ j : Fin 3, ‖Q p i j - Q q i j‖) ≤
          (36 / c ^ 2) * delta * N * ρ ^ alpha := by
      calc
        _ ≤ 4 / c ^ 2 * ‖A p - A0‖ * (9 * (N * ρ ^ alpha)) :=
          mul_le_mul_of_nonneg_left hsumDiff
            (mul_nonneg hk (norm_nonneg (A p - A0)))
        _ ≤ 4 / c ^ 2 * delta * (9 * (N * ρ ^ alpha)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hclose p) hk)
            (by positivity : 0 ≤ 9 * (N * ρ ^ alpha))
        _ = (36 / c ^ 2) * delta * N * ρ ^ alpha := by ring
    have hterm2 :
        4 / c ^ 2 * ‖A p - A q‖ *
            (∑ i : Fin 3, ∑ j : Fin 3, ‖Q q i j‖) ≤
          (36 / c ^ 2) * H * M * ρ ^ alpha := by
      calc
        _ ≤ 4 / c ^ 2 * ‖A p - A q‖ * (9 * M) :=
          mul_le_mul_of_nonneg_left hsumQ
            (mul_nonneg hk (norm_nonneg (A p - A q)))
        _ ≤ 4 / c ^ 2 * (H * ρ ^ alpha) * (9 * M) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hAinc hk) h9M
        _ = (36 / c ^ 2) * H * M * ρ ^ alpha := by ring
    calc
      ‖(∑ i : Fin 3, ∑ j : Fin 3,
          (((A p).inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q p i j) -
          (∑ i : Fin 3, ∑ j : Fin 3,
          (((A q).inverse - A0.inverse) (EuclideanSpace.single j 1)) i • Q q i j)‖
          ≤ 4 / c ^ 2 * ‖A p - A0‖ *
              (∑ i : Fin 3, ∑ j : Fin 3, ‖Q p i j - Q q i j‖) +
            4 / c ^ 2 * ‖A p - A q‖ *
              (∑ i : Fin 3, ∑ j : Fin 3, ‖Q q i j‖) := hraw
      _ ≤ (36 / c ^ 2) * delta * N * ρ ^ alpha +
            (36 / c ^ 2) * H * M * ρ ^ alpha := add_le_add hterm1 hterm2
      _ = (36 / c ^ 2) * (delta * N + H * M) * ρ ^ alpha := by ring
      _ = (36 / c ^ 2) * (delta * N + H * M) *
            (‖p.2 - q.2‖ + Real.sqrt |(p.1 : ℝ) - (q.1 : ℝ)|) ^ alpha := by
              simp [ρ]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FrozenPrincipalParabolicEstimate
