import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CompactCutoffC3ProductBound
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance stdGroup0 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance stdSpace0 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance stdGroup1 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace1 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdGroup2 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace2 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
theorem compact_cutoff_c3_product_bound
    (χ : E3 → ℝ) (hχ : ContDiff ℝ 3 χ) (f : E3 → E6) (hf : ContDiff ℝ 3 f)
    (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hχbound : ∀ (k : ℕ), k ≤ 3 → ∀ x : E3, ‖iteratedFDeriv ℝ k χ x‖ ≤ M)
    (hfbound : ∀ (k : ℕ), k ≤ 3 → ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ k f x‖ ≤ N) :

    ∀ (k : ℕ), k ≤ 3 → ∀ x : E3,
      ‖iteratedFDeriv ℝ k (fun y : E3 => χ y • f y) x‖ ≤ 8*M*N :=
/- SWARM_PROOF_BEGIN -/
by
  intro k hk x
  by_cases hx : x ∈ tsupport χ
  · have hprod := norm_iteratedFDeriv_smul_le hχ hf x (n := k) (by exact_mod_cast hk)
    have hsum :
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) ≤ 8 := by
      calc
        (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) = (2 : ℝ) ^ k := by
          exact_mod_cast Nat.sum_range_choose k
        _ ≤ 8 := by
          calc
            (2 : ℝ) ^ k ≤ 2 ^ 3 := by
              exact pow_le_pow_right₀ (by norm_num) hk
            _ = 8 := by norm_num
    calc
      ‖iteratedFDeriv ℝ k (fun y : E3 => χ y • f y) x‖ ≤
          ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i χ x‖ * ‖iteratedFDeriv ℝ (k - i) f x‖ := hprod
      _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * M * N := by
          apply Finset.sum_le_sum
          intro i hi
          have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          have hχi := hχbound i (by omega) x
          have hfi := hfbound (k - i) (by omega) x hx
          have hci : 0 ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
          calc
            (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i χ x‖ *
                ‖iteratedFDeriv ℝ (k - i) f x‖ ≤
                ((k.choose i : ℝ) * M) * ‖iteratedFDeriv ℝ (k - i) f x‖ := by
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hχi hci) (norm_nonneg _)
            _ ≤ ((k.choose i : ℝ) * M) * N := by
                  exact mul_le_mul_of_nonneg_left hfi (mul_nonneg hci hM)
            _ = (k.choose i : ℝ) * M * N := by ring
      _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) * (M * N) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          ring
      _ ≤ 8 * (M * N) := mul_le_mul_of_nonneg_right hsum (mul_nonneg hM hN)
      _ = 8 * M * N := by ring
  · have hout : x ∉ tsupport (fun y : E3 => χ y • f y) := by
      intro h
      exact hx ((tsupport_smul_subset_left χ f) h)
    have hzero : iteratedFDeriv ℝ k (fun y : E3 => χ y • f y) x = 0 := by
      by_contra hne
      have hsupp : x ∈ Function.support (iteratedFDeriv ℝ k (fun y : E3 => χ y • f y)) := by
        exact hne
      exact hout ((support_iteratedFDeriv_subset (𝕜 := ℝ) k) hsupp)
    simpa [hzero] using
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hM) hN)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CompactCutoffC3ProductBound
