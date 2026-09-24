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
namespace PoincareConjecture.ParallelImplementation.QuadraticGradientHeatSolution
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Actual zero-trace solutions for a fixed gradient-quadratic heat system on a short slab. -/
theorem exists_quadratic_gradient_heat_solution
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (B : (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ (T : ℝ) (hT : 0 < T), T ≤ delta →
      ∀ F : ForcingJet E6 T, F ∈ forcingGraph E6 T alpha → ‖F‖ ≤ 1 →
      ∃ z : FullJet T, z ∈ fullParabolicJetSet T alpha hT.le ∧ ‖z‖ ≤ C ∧
        ∀ p : Slab T, z.1.2 p - (∑ i : Fin 3, z.1.1.1.2.2 p
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
          F.1 p + B (z.1.1.1.2.1 p) (z.1.1.1.2.1 p) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hHeat :=
    PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse.exists_parabolic_heat_right_inverse
      alpha ha ha1
  obtain ⟨C₀, hC₀, hHeat⟩ := hHeat
  let R : ℝ := 2 * C₀
  let A : ℝ := 2 * ‖B‖
  let eps : ℝ := 1 / (4 * C₀ * R)
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have heps : 0 < eps := by
    dsimp [eps]
    positivity
  obtain ⟨delta, hdelta, hdelta1, hsmall⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicSmallTimeConstants.exists_small_time_projection_bounds
      alpha A eps ha ha1 hA heps
  refine ⟨R, delta, ?_, hdelta, hdelta1, ?_⟩
  · dsimp [R]
    positivity
  · intro T hT hTdelta F hFgraph hFnorm
    have hT1 : T ≤ 1 := le_trans hTdelta hdelta1
    obtain ⟨X, Y, hX, hY, hXcomplete, hYcomplete, L, D, hLnorm, hDnorm, hLD, hLvalue⟩ :=
      hHeat T hT hT1
    letI : NormedAddCommGroup (FullJet T) := inferInstance
    letI : NormedSpace ℝ (FullJet T) := inferInstance
    letI : NormedAddCommGroup (ForcingJet E6 T) := inferInstance
    letI : NormedSpace ℝ (ForcingJet E6 T) := inferInstance
    letI : NormedAddCommGroup Y := inferInstance
    letI : NormedSpace ℝ Y := inferInstance
    letI : NormedAddCommGroup X := inferInstance
    letI : NormedSpace ℝ X := inferInstance
    letI : CompleteSpace Y := hYcomplete
    let f : X := ⟨F, (congrArg (fun s : Set (ForcingJet E6 T) => F ∈ s) hX).mpr hFgraph⟩
    have hfnorm : ‖f‖ ≤ 1 := by
      simpa [f] using hFnorm
    obtain ⟨P, hPnorm, hPvalue, hPgraph⟩ :=
      PoincareConjecture.ParallelImplementation.ZeroTraceGradientProjection.exists_zero_trace_gradient_projection
        T alpha hT ha ha1 Y hY
    obtain ⟨N, hNzero, hNvalue, hNlip⟩ :=
      PoincareConjecture.ParallelImplementation.ProjectedForcingQuadratic.exists_projected_forcing_quadratic
        T alpha B X hX P hPgraph
    let g : ℝ := 3 * Real.sqrt T + 16 * T ^ ((1 - alpha) / 2)
    let K : ℝ := 2 * ‖B‖ * ‖P‖ ^ 2
    have hg : 0 ≤ g := by
      dsimp [g]
      positivity
    have hPnormsq : ‖P‖ ^ 2 ≤ g ^ 2 := by
      rw [pow_two, pow_two]
      exact mul_le_mul hPnorm hPnorm (norm_nonneg P) hg
    have hK : 0 ≤ K := by
      dsimp [K]
      positivity
    have hKle : K ≤ eps := by
      have hsmallT := hsmall T hT hTdelta
      have hA_g : A * g ^ 2 ≤ eps := by
        simpa [A, g] using hsmallT.2
      calc
        K = A * ‖P‖ ^ 2 := by rfl
        _ ≤ A * g ^ 2 := mul_le_mul_of_nonneg_left hPnormsq hA
        _ ≤ eps := hA_g
    have hRpos : 0 < R := by
      dsimp [R]
      positivity
    have hC0nonneg : 0 ≤ C₀ := le_of_lt hC₀
    have hprod : C₀ * eps * R = 1 / 4 := by
      dsimp [eps]
      have hden : 4 * C₀ * R ≠ 0 := by positivity
      field_simp
    have hselfval : C₀ * (1 + eps * R ^ 2) ≤ R := by
      rw [show C₀ * (1 + eps * R ^ 2) = C₀ + (C₀ * eps * R) * R by ring, hprod]
      dsimp [R]
      nlinarith [hC₀]
    have hself : ‖D‖ * (‖f‖ + K * R ^ 2) ≤ R := by
      calc
        ‖D‖ * (‖f‖ + K * R ^ 2) ≤ C₀ * (‖f‖ + K * R ^ 2) :=
          mul_le_mul_of_nonneg_right hDnorm
            (add_nonneg (norm_nonneg f) (mul_nonneg hK (sq_nonneg R)))
        _ ≤ C₀ * (1 + eps * R ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ hC0nonneg
          have hquad : K * R ^ 2 ≤ eps * R ^ 2 :=
            mul_le_mul_of_nonneg_right hKle (sq_nonneg R)
          exact add_le_add hfnorm hquad
        _ ≤ R := hselfval
    have hcontract : 2 * ‖D‖ * K * R < 1 := by
      have hmul : ‖D‖ * K ≤ C₀ * eps :=
        mul_le_mul hDnorm hKle hK hC0nonneg
      calc
        2 * ‖D‖ * K * R ≤ 2 * (C₀ * eps) * R := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hRpos)
          calc
            2 * ‖D‖ * K = 2 * (‖D‖ * K) := by ring
            _ ≤ 2 * (C₀ * eps) := mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 1 / 2 := by
          calc
            2 * (C₀ * eps) * R = 2 * (C₀ * eps * R) := by ring
            _ = 2 * (1 / 4) := by rw [hprod]
            _ = 1 / 2 := by norm_num
        _ < 1 := by norm_num
    obtain ⟨y, hy, _hyfixed, hLy, _hyunique⟩ :=
      PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint.quadratic_right_inverse_fixed_point
        L D hLD N hNzero f K R hK hRpos
        (by intro z w _ _; exact hNlip z w) hself hcontract
    have hLvalueEq (p : Slab T) :
        (L y).1.1 p = F.1 p + B ((P y).1 p) ((P y).1 p) := by
      have hh := congrArg (fun x : X => x.1.1 p) hLy
      simpa [f, hNvalue] using hh
    have hmem : y.1 ∈ fullParabolicJetSet T alpha hT.le := by
      rw [← hY]
      exact y.2
    have hybound : ‖y.1‖ ≤ R := by
      simpa using hy
    refine ⟨y.1, hmem, hybound, ?_⟩
    intro p
    have hheatValue := hLvalue y p
    rw [hLvalueEq p, hPvalue y p] at hheatValue
    exact hheatValue.symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.QuadraticGradientHeatSolution
