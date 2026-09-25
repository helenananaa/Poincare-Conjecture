import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CompactC3RescalingSmallness
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance stdGroup0 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance stdSpace0 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance stdGroup1 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace1 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdGroup2 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace2 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
theorem compact_c3_rescaling_smallness
    (u : E3 → E6) (hu : ContDiff ℝ 3 u) (p : E3) (hp : u p=0)
    (S : Set E3) (hS : IsCompact S) (epsilon : ℝ) (heps : 0 < epsilon) :

    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ r : ℝ, |r| ≤ delta →
      ∀ (k : ℕ), k ≤ 3 → ∀ x ∈ S,
        ‖iteratedFDeriv ℝ k (fun y : E3 => u (p+r • y)) x‖ ≤ epsilon :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨B, hBpos, hB⟩ := hS.isBounded.exists_pos_norm_le
  have hK : IsCompact (Metric.closedBall p B) := isCompact_closedBall p B
  have hcont1 : Continuous fun z : E3 => iteratedFDeriv ℝ 1 u z :=
    hu.continuous_iteratedFDeriv (by norm_num)
  have hcont2 : Continuous fun z : E3 => iteratedFDeriv ℝ 2 u z :=
    hu.continuous_iteratedFDeriv (by norm_num)
  have hcont3 : Continuous fun z : E3 => iteratedFDeriv ℝ 3 u z :=
    hu.continuous_iteratedFDeriv (by norm_num)
  obtain ⟨M1, hM1⟩ := hK.exists_bound_of_continuousOn hcont1.continuousOn
  obtain ⟨M2, hM2⟩ := hK.exists_bound_of_continuousOn hcont2.continuousOn
  obtain ⟨M3, hM3⟩ := hK.exists_bound_of_continuousOn hcont3.continuousOn
  let C := max 1 (max M1 (max M2 M3))
  have hCpos : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM1C : M1 ≤ C := by
    dsimp [C]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hM2C : M2 ≤ C := by
    dsimp [C]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hM3C : M3 ≤ C := by
    dsimp [C]
    exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hcontU : ContinuousAt (fun z : E3 => ‖u z‖) p :=
    hu.continuous.continuousAt.norm
  obtain ⟨η, hηpos, hη⟩ := Metric.continuousAt_iff.mp hcontU epsilon heps
  have hu_small : ∀ z : E3, dist z p < η → ‖u z‖ < epsilon := by
    intro z hz
    have hz' := hη hz
    simpa [hp] using hz'
  let delta := min 1 (min (η / (B + 1)) (epsilon / (C + 1)))
  have hdeltaPos : 0 < delta := by
    dsimp [delta]
    positivity
  have hdeltaOne : delta ≤ 1 := by
    dsimp [delta]
    exact min_le_left _ _
  have hdeltaEta : delta ≤ η / (B + 1) := by
    dsimp [delta]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hdeltaEps : delta ≤ epsilon / (C + 1) := by
    dsimp [delta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hdeltaB : delta * B < η := by
    calc
      delta * B ≤ (η / (B + 1)) * B :=
        mul_le_mul_of_nonneg_right hdeltaEta (le_of_lt hBpos)
      _ < η := by
        have hden : 0 < B + 1 := by linarith
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hden).2
        nlinarith [mul_pos hηpos hBpos]
  have hdeltaC : delta * C < epsilon := by
    calc
      delta * C ≤ (epsilon / (C + 1)) * C :=
        mul_le_mul_of_nonneg_right hdeltaEps (le_of_lt hCpos)
      _ < epsilon := by
        have hden : 0 < C + 1 := by linarith
        rw [div_mul_eq_mul_div]
        apply (div_lt_iff₀ hden).2
        nlinarith [mul_pos heps hCpos]
  have hg : ContDiff ℝ 3 (fun z : E3 => u (p + z)) := by fun_prop
  refine ⟨delta, hdeltaPos, hdeltaOne, ?_⟩
  intro r hr k hk x hx
  have hdist : dist (p + r • x) p ≤ delta * B := by
    calc
      dist (p + r • x) p = ‖r • x‖ := by simp [dist_eq_norm]
      _ = |r| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ delta * ‖x‖ := mul_le_mul_of_nonneg_right hr (norm_nonneg x)
      _ ≤ delta * B := mul_le_mul_of_nonneg_left (hB x hx) (le_of_lt hdeltaPos)
  have hzK : p + r • x ∈ Metric.closedBall p B := by
    rw [Metric.mem_closedBall]
    exact hdist.trans (by
      calc
        delta * B ≤ 1 * B := mul_le_mul_of_nonneg_right hdeltaOne (le_of_lt hBpos)
        _ = B := one_mul B)
  have hscale : iteratedFDeriv ℝ k (fun y : E3 => u (p + r • y)) x =
      r ^ k • iteratedFDeriv ℝ k u (p + r • x) := by
    calc
      iteratedFDeriv ℝ k (fun y : E3 => u (p + r • y)) x =
          iteratedFDeriv ℝ k (fun y : E3 => (fun z : E3 => u (p + z)) (r • y)) x := rfl
      _ = r ^ k • iteratedFDeriv ℝ k (fun z : E3 => u (p + z)) (r • x) := by
        simpa using congrFun
          (iteratedFDeriv_comp_const_smul r
            (hg.of_le (m := k) (by exact_mod_cast hk))) x
      _ = r ^ k • iteratedFDeriv ℝ k u (p + r • x) := by
        rw [iteratedFDeriv_comp_add_left k p (r • x)]
  by_cases hk0 : k = 0
  · subst k
    rw [norm_iteratedFDeriv_zero]
    have hsmall := hu_small (p + r • x) (lt_of_le_of_lt hdist hdeltaB)
    exact le_of_lt hsmall
  · have hpow : |r| ^ k ≤ delta := by
      exact (pow_le_of_le_one (abs_nonneg r) (le_trans hr hdeltaOne) hk0).trans hr
    have hnormscale :
        ‖iteratedFDeriv ℝ k (fun y : E3 => u (p + r • y)) x‖ =
          |r| ^ k * ‖iteratedFDeriv ℝ k u (p + r • x)‖ := by
      rw [hscale, norm_smul]
      simp [Real.norm_eq_abs]
    rw [hnormscale]
    have hbound : ‖iteratedFDeriv ℝ k u (p + r • x)‖ ≤ C := by
      interval_cases k
      · omega
      · exact (hM1 (p + r • x) hzK).trans hM1C
      · exact (hM2 (p + r • x) hzK).trans hM2C
      · exact (hM3 (p + r • x) hzK).trans hM3C
    calc
      |r| ^ k * ‖iteratedFDeriv ℝ k u (p + r • x)‖ ≤ delta *
          ‖iteratedFDeriv ℝ k u (p + r • x)‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ delta * C := mul_le_mul_of_nonneg_left hbound (le_of_lt hdeltaPos)
      _ ≤ epsilon := le_of_lt hdeltaC
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CompactC3RescalingSmallness
