import PoincareConjecture.ParallelImplementation.ZeroTraceValueHessianNonlinearity
import PoincareConjecture.ParallelImplementation.ProjectedForcingQuadratic
import PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint
import PoincareConjecture.ParallelImplementation.ParabolicSmallTimeConstants
import PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse
import PoincareConjecture.ParallelImplementation.ZeroTraceGradientProjection
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.MixedValueGradientHeatSolution
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Actual zero-trace solutions for a fixed mixed value-Hessian and gradient-quadratic system. -/
theorem exists_mixed_value_gradient_heat_solution
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (B : E6 →L[ℝ] (E3 →L[ℝ] E3 →L[ℝ] E6) →L[ℝ] E6)
    (G : (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ (T : ℝ) (hT : 0 < T), T ≤ delta →
      ∀ F : ForcingJet E6 T, F ∈ forcingGraph E6 T alpha → ‖F‖ ≤ 1 →
      ∃ z : FullJet T, z ∈ fullParabolicJetSet T alpha hT.le ∧ ‖z‖ ≤ C ∧
        ∀ p : Slab T, z.1.2 p - (∑ i : Fin 3, z.1.1.1.2.2 p
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
          F.1 p + B (z.1.1.1.1 p) (z.1.1.1.2.2 p) +
            G (z.1.1.1.2.1 p) (z.1.1.1.2.1 p) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C₀, hC₀, hheat⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse.exists_parabolic_heat_right_inverse
      alpha ha ha1
  let A : ℝ := max (2 * ‖B‖) (2 * ‖G‖)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  let eps : ℝ := 1 / (16 * C₀ ^ 2)
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  obtain ⟨delta, hdelta, hdelta1, hsmall⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicSmallTimeConstants.exists_small_time_projection_bounds
      alpha A eps ha ha1 hA heps
  refine ⟨2 * C₀, delta, by positivity, hdelta, hdelta1, ?_⟩
  intro T hT hTdelta F hF hFnorm
  letI : NormedAddCommGroup (FullJet T) := inferInstance
  letI : NormedSpace ℝ (FullJet T) := inferInstance
  letI : NormedAddCommGroup (ForcingJet E6 T) := inferInstance
  letI : NormedSpace ℝ (ForcingJet E6 T) := inferInstance
  have hT1 : T ≤ 1 := le_trans hTdelta hdelta1
  obtain ⟨X, Y, hX, hY, hXcomplete, hYcomplete, L, D, hLnorm, hDnorm, hLD, hLvalue⟩ :=
    hheat T hT hT1
  letI : NormedAddCommGroup X := inferInstance
  letI : NormedSpace ℝ X := inferInstance
  letI : NormedAddCommGroup Y := inferInstance
  letI : NormedSpace ℝ Y := inferInstance
  letI : CompleteSpace X := hXcomplete
  letI : CompleteSpace Y := hYcomplete
  obtain ⟨N_B, hN_B_zero, hN_B_value, hN_B_lip⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceValueHessianNonlinearity.exists_zero_trace_value_hessian_nonlinearity
      T alpha hT ha ha1 X Y hX hY B
  obtain ⟨P, hPnorm, hPvalue, hPgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceGradientProjection.exists_zero_trace_gradient_projection
      T alpha hT ha ha1 Y hY
  obtain ⟨N_G, hN_G_zero, hN_G_value, hN_G_lip⟩ :=
    PoincareConjecture.ParallelImplementation.ProjectedForcingQuadratic.exists_projected_forcing_quadratic
      (Y := Y) (V := E3 →L[ℝ] E6) (Z := E6) T alpha G X hX P hPgraph
  let N : Y → X := fun z => N_B z + N_G z
  have hN_zero : N 0 = 0 := by
    dsimp [N]
    rw [hN_B_zero, hN_G_zero, add_zero]
  let K : ℝ :=
    2 * ‖B‖ * (T + 8 * T ^ (1 - alpha / 2)) +
      2 * ‖G‖ * (3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)) ^ 2
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hKsmall : K ≤ 2 * eps := by
    have hfirst := (hsmall T hT hTdelta).1
    have hsecond := (hsmall T hT hTdelta).2
    have hval_nonneg : 0 ≤ T + 8 * T ^ (1 - alpha / 2) := by
      positivity
    have hgrad_nonneg : 0 ≤ (3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)) ^ 2 :=
      sq_nonneg _
    have hB : 2 * ‖B‖ ≤ A := by
      dsimp [A]
      exact le_max_left _ _
    have hG : 2 * ‖G‖ ≤ A := by
      dsimp [A]
      exact le_max_right _ _
    have hfirst' : 2 * ‖B‖ * (T + 8 * T ^ (1 - alpha / 2)) ≤ eps := by
      calc
        2 * ‖B‖ * (T + 8 * T ^ (1 - alpha / 2)) ≤
            A * (T + 8 * T ^ (1 - alpha / 2)) :=
          mul_le_mul_of_nonneg_right hB hval_nonneg
        _ ≤ eps := hfirst
    have hsecond' :
        2 * ‖G‖ * (3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)) ^ 2 ≤ eps := by
      calc
        2 * ‖G‖ * (3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)) ^ 2 ≤
            A * (3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_right hG hgrad_nonneg
        _ ≤ eps := hsecond
    dsimp [K]
    linarith
  have heps_identity : 2 * eps = 1 / (8 * C₀ ^ 2) := by
    dsimp [eps]
    field_simp [ne_of_gt hC₀]
    <;> ring
  have hKbound : K ≤ 1 / (8 * C₀ ^ 2) := heps_identity ▸ hKsmall
  have hRpos : 0 < 2 * C₀ := by positivity
  have hR_sq : (2 * C₀) ^ 2 = 4 * C₀ ^ 2 := by ring
  have hK_R : K * (2 * C₀) ^ 2 ≤ 1 / 2 := by
    rw [hR_sq]
    calc
      K * (4 * C₀ ^ 2) ≤ (1 / (8 * C₀ ^ 2)) * (4 * C₀ ^ 2) :=
        mul_le_mul_of_nonneg_right hKbound (by positivity)
      _ = 1 / 2 := by
        field_simp [ne_of_gt (sq_pos_of_pos hC₀)]
        <;> ring
  have hK_R_nonneg : 0 ≤ K * (2 * C₀) ^ 2 := mul_nonneg hK_nonneg (sq_nonneg _)
  let f : X := ⟨F, by
    change F ∈ (X : Set (ForcingJet E6 T))
    rw [hX]
    exact hF⟩
  have hf_norm : ‖f‖ ≤ 1 := by
    simpa [f] using hFnorm
  have hN_lip : ∀ z w : Y, ‖z‖ ≤ 2 * C₀ → ‖w‖ ≤ 2 * C₀ →
      ‖N z - N w‖ ≤ K * (‖z‖ + ‖w‖) * ‖z - w‖ := by
    intro z w _ _
    have hdiff : N z - N w = (N_B z - N_B w) + (N_G z - N_G w) := by
      dsimp [N]
      abel
    rw [hdiff]
    calc
      ‖(N_B z - N_B w) + (N_G z - N_G w)‖ ≤
          ‖N_B z - N_B w‖ + ‖N_G z - N_G w‖ := norm_add_le _ _
      _ ≤ 2 * ‖B‖ * (T + 8 * T ^ (1 - alpha / 2)) *
            (‖z‖ + ‖w‖) * ‖z - w‖ +
          (2 * ‖G‖ * ‖P‖ ^ 2) * (‖z‖ + ‖w‖) * ‖z - w‖ :=
        add_le_add (hN_B_lip z w) (hN_G_lip z w)
      _ ≤ K * (‖z‖ + ‖w‖) * ‖z - w‖ := by
        have hPbound : ‖P‖ ^ 2 ≤
            (3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)) ^ 2 := by
          exact pow_le_pow_left₀ (norm_nonneg P) hPnorm 2
        have hcoef : 2 * ‖G‖ * ‖P‖ ^ 2 ≤
            2 * ‖G‖ * (3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hPbound (by positivity)
        have hsum_nonneg : 0 ≤ (‖z‖ + ‖w‖) * ‖z - w‖ :=
          mul_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg w)) (norm_nonneg _)
        have hcoefsum :
            2 * ‖B‖ * (T + 8 * T ^ (1 - alpha / 2)) + 2 * ‖G‖ * ‖P‖ ^ 2 ≤ K := by
          dsimp [K]
          nlinarith
        calc
          _ = (2 * ‖B‖ * (T + 8 * T ^ (1 - alpha / 2)) +
              2 * ‖G‖ * ‖P‖ ^ 2) * ((‖z‖ + ‖w‖) * ‖z - w‖) := by ring
          _ ≤ K * ((‖z‖ + ‖w‖) * ‖z - w‖) :=
            mul_le_mul_of_nonneg_right hcoefsum hsum_nonneg
          _ = K * (‖z‖ + ‖w‖) * ‖z - w‖ := by ring
  have hself : ‖D‖ * (‖f‖ + K * (2 * C₀) ^ 2) ≤ 2 * C₀ := by
    calc
      ‖D‖ * (‖f‖ + K * (2 * C₀) ^ 2) ≤
          ‖D‖ * (1 + K * (2 * C₀) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hf_norm (show K * (2 * C₀) ^ 2 ≤ K * (2 * C₀) ^ 2 from le_rfl))
          (norm_nonneg D)
      _ = ‖D‖ + ‖D‖ * (K * (2 * C₀) ^ 2) := by ring
      _ ≤ C₀ + C₀ * (1 / 2) := by
        apply add_le_add hDnorm
        calc
          ‖D‖ * (K * (2 * C₀) ^ 2) ≤ C₀ * (K * (2 * C₀) ^ 2) :=
            mul_le_mul_of_nonneg_right hDnorm hK_R_nonneg
          _ ≤ C₀ * (1 / 2) :=
            mul_le_mul_of_nonneg_left hK_R (le_of_lt hC₀)
      _ ≤ 2 * C₀ := by nlinarith [hC₀]
  have hcontract : 2 * ‖D‖ * K * (2 * C₀) < 1 := by
    calc
      2 * ‖D‖ * K * (2 * C₀) = (2 * ‖D‖) * (K * (2 * C₀)) := by ring
      _ ≤ (2 * C₀) * (K * (2 * C₀)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDnorm (by norm_num))
          (mul_nonneg hK_nonneg hRpos.le)
      _ = 4 * C₀ ^ 2 * K := by ring
      _ ≤ 4 * C₀ ^ 2 * (1 / (8 * C₀ ^ 2)) :=
        mul_le_mul_of_nonneg_left hKbound (by positivity)
      _ = 1 / 2 := by
        field_simp [ne_of_gt (sq_pos_of_pos hC₀)]
        <;> ring
      _ < 1 := by norm_num
  obtain ⟨z, hz, _, hLz, _⟩ :=
    PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint.quadratic_right_inverse_fixed_point
      L D hLD N hN_zero f K (2 * C₀) hK_nonneg hRpos hN_lip hself hcontract
  have hmembership : z.1 ∈ fullParabolicJetSet T alpha hT.le := by
    rw [← hY]
    exact z.2
  have hbound : ‖z.1‖ ≤ 2 * C₀ := by
    simpa using hz
  have hsource (p : Slab T) :
      (f + N z).1.1 p =
        F.1 p + B ((z : FullJet T).1.1.1.1 p) ((z : FullJet T).1.1.1.2.2 p) +
          G ((z : FullJet T).1.1.1.2.1 p) ((z : FullJet T).1.1.1.2.1 p) := by
    dsimp [N]
    change f.1.1 p + ((N_B z).1.1 p + (N_G z).1.1 p) = _
    rw [hN_B_value z p, hN_G_value z p]
    simp [f, hPvalue z p]
    abel
  refine ⟨z.1, hmembership, ?_, ?_⟩
  · simpa using hbound
  · intro p
    calc
      z.1.1.2 p - (∑ i : Fin 3, z.1.1.1.1.2.2 p
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
          (L z).1.1 p := (hLvalue z p).symm
      _ = (f + N z).1.1 p := by
        exact congrArg (fun u : X => u.1.1 p) hLz
      _ = F.1 p + B ((z : FullJet T).1.1.1.1 p) ((z : FullJet T).1.1.1.2.2 p) +
            G ((z : FullJet T).1.1.1.2.1 p) ((z : FullJet T).1.1.1.2.1 p) := hsource p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.MixedValueGradientHeatSolution
