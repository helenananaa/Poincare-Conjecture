import PoincareConjecture.ParallelImplementation.InverseMetricHessianNonlinearity
import PoincareConjecture.ParallelImplementation.InverseMetricSmallTimeConstants
import PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse
import PoincareConjecture.ParallelImplementation.ProjectedForcingQuadratic
import PoincareConjecture.ParallelImplementation.ZeroTraceGradientProjection
import PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint
import PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.InverseMetricGradientHeatSolution
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
open MorganTianLib.MetricCoefficient
/-- A genuine inverse-metric principal coefficient, with a fixed quadratic gradient term. -/
theorem exists_inverse_metric_gradient_heat_solution
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (G : (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) :
    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Fin 3),
        (E q v) i = ∑ j : Fin 3, symmetricSixMatrix q i j * v j) ∧
      ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ delta →
        ∀ F : ForcingJet E6 T, F ∈ forcingGraph E6 T alpha → ‖F‖ ≤ 1 →
        ∃ z : FullJet T, z ∈ fullParabolicJetSet T alpha hT.le ∧ ‖z‖ ≤ C ∧
          ∃ b : ForcingJet (E3 →L[ℝ] E3) T,
            b ∈ forcingGraph (E3 →L[ℝ] E3) T alpha ∧ ∀ p : Slab T,
              ((1+E (z.1.1.1.1 p))*b.1 p=1 ∧ b.1 p*(1+E (z.1.1.1.1 p))=1) ∧
              (∀ v : E3, (1/2:ℝ)*‖v‖^2 ≤ inner ℝ ((1+E (z.1.1.1.1 p)) v) v) ∧
              z.1.2 p - (∑ i : Fin 3, z.1.1.1.2.2 p
                (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) =
                F.1 p + (∑ i : Fin 3, ∑ j : Fin 3,
                  ((b.1 p-1) (EuclideanSpace.single j 1)) i •
                    z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
                  G (z.1.1.1.2.1 p) (z.1.1.1.2.1 p) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨E, hEinj, hEnorm, hEaction, _hEpositive⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceMetricPositivity.zero_trace_metric_positivity
  obtain ⟨C₀, hC₀, hHeat⟩ :=
    PoincareConjecture.ParallelImplementation.ParabolicHeatRightInverse.exists_parabolic_heat_right_inverse
      alpha ha ha1
  let R : ℝ := 2 * C₀
  let W : ℝ := ‖G‖
  have hR : 0 < R := by
    dsimp [R]
    positivity
  obtain ⟨delta, hdelta, hdelta1, hsmall⟩ :=
    PoincareConjecture.ParallelImplementation.InverseMetricSmallTimeConstants.exists_inverse_metric_small_time
      alpha C₀ R W ha ha1 (le_of_lt hC₀) hR (norm_nonneg G)
  refine ⟨E, hEinj, hEnorm, hEaction, R, delta, hR, hdelta, hdelta1, ?_⟩
  intro T hT hTdelta F hFgraph hFnorm
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
  have hf_norm : ‖f‖ ≤ 1 := by
    simpa [f] using hFnorm
  obtain ⟨P, hPnorm, hPvalue, hPgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceGradientProjection.exists_zero_trace_gradient_projection
      T alpha hT ha ha1 Y hY
  let g : ℝ := 3 * Real.sqrt T + 16 * T ^ ((1-alpha)/2)
  have hg : 0 ≤ g := by
    dsimp [g]
    positivity
  have hPnormsq : ‖P‖ ^ 2 ≤ g ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul hPnorm hPnorm (norm_nonneg P) hg
  have hsmallT := hsmall T hT hTdelta
  obtain ⟨N_H, hN_Hzero, hN_Hspec, hN_Hlip⟩ :=
    PoincareConjecture.ParallelImplementation.InverseMetricHessianNonlinearity.exists_inverse_metric_hessian_nonlinearity
      T alpha R hT ha ha1 hR E hEnorm hsmallT.1 X Y hX hY
  obtain ⟨N_G, hN_Gzero, hN_Gvalue, hN_Glip⟩ :=
    PoincareConjecture.ParallelImplementation.ProjectedForcingQuadratic.exists_projected_forcing_quadratic
      (Y := Y) (V := E3 →L[ℝ] E6) (Z := E6) T alpha G X hX P hPgraph
  let N : Y → X := fun z => N_H z + N_G z
  have hNzero : N 0 = 0 := by
    dsimp [N]
    rw [hN_Hzero, hN_Gzero, add_zero]
  let τ : ℝ := T + 8 * T ^ (1-alpha/2)
  let K : ℝ := 648 * τ + 2 * ‖G‖ * g ^ 2
  have hK : 0 ≤ K := by
    dsimp [K, τ, g]
    positivity
  have hKsmall : 2 * C₀ * K * R ≤ 1/2 := by
    simpa [K, τ, g, W] using hsmallT.2
  have hNlip : ∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R →
      ‖N z-N w‖ ≤ K*(‖z‖+‖w‖)*‖z-w‖ := by
    intro z w hz hw
    have hdiff : N z - N w = (N_H z - N_H w) + (N_G z - N_G w) := by
      dsimp [N]
      abel
    have hGcoef : 2 * ‖G‖ * ‖P‖ ^ 2 ≤ 2 * ‖G‖ * g ^ 2 :=
      mul_le_mul_of_nonneg_left hPnormsq (by positivity)
    have hcoef : 648 * τ + 2 * ‖G‖ * ‖P‖ ^ 2 ≤ K := by
      dsimp [K]
      nlinarith [hGcoef]
    have hsum_nonneg : 0 ≤ (‖z‖ + ‖w‖) * ‖z-w‖ :=
      mul_nonneg (add_nonneg (norm_nonneg z) (norm_nonneg w)) (norm_nonneg _)
    calc
      ‖N z-N w‖ = ‖(N_H z-N_H w) + (N_G z-N_G w)‖ := by rw [hdiff]
      _ ≤ ‖N_H z-N_H w‖ + ‖N_G z-N_G w‖ := norm_add_le _ _
      _ ≤ (648 * τ) * (‖z‖+‖w‖) * ‖z-w‖ +
            (2 * ‖G‖ * ‖P‖ ^ 2) * (‖z‖+‖w‖) * ‖z-w‖ := by
        exact add_le_add (by simpa [τ] using hN_Hlip z w hz hw) (hN_Glip z w)
      _ = (648 * τ + 2 * ‖G‖ * ‖P‖ ^ 2) *
            ((‖z‖+‖w‖) * ‖z-w‖) := by ring
      _ ≤ K * ((‖z‖+‖w‖) * ‖z-w‖) :=
        mul_le_mul_of_nonneg_right hcoef hsum_nonneg
      _ = K * (‖z‖+‖w‖) * ‖z-w‖ := by ring
  have hC₀KR : C₀ * K * R ≤ 1/4 := by
    calc
      C₀ * K * R = (2 * C₀ * K * R) / 2 := by ring
      _ ≤ (1/2) / 2 := by linarith [hKsmall]
      _ = 1/4 := by norm_num
  have hself : ‖D‖ * (‖f‖ + K * R ^ 2) ≤ R := by
    calc
      ‖D‖ * (‖f‖ + K * R ^ 2) ≤ C₀ * (‖f‖ + K * R ^ 2) :=
        mul_le_mul_of_nonneg_right hDnorm (by positivity)
      _ ≤ C₀ * (1 + K * R ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hf_norm le_rfl) (le_of_lt hC₀)
      _ = C₀ + (C₀ * K * R) * R := by ring
      _ ≤ C₀ + (1/4) * R :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hC₀KR hR.le)
      _ ≤ R := by dsimp [R]; nlinarith [hC₀]
  have hcontract : 2 * ‖D‖ * K * R < 1 := by
    calc
      2 * ‖D‖ * K * R ≤ 2 * C₀ * K * R := by
        calc
          2 * ‖D‖ * K * R = (2 * ‖D‖) * (K * R) := by ring
          _ ≤ (2 * C₀) * (K * R) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hDnorm (by norm_num))
              (mul_nonneg hK hR.le)
          _ = 2 * C₀ * K * R := by ring
      _ ≤ 1/2 := hKsmall
      _ < 1 := by norm_num
  obtain ⟨y, hy, _hyfixed, hLy, _hyunique⟩ :=
    PoincareConjecture.ParallelImplementation.QuadraticRightInverseFixedPoint.quadratic_right_inverse_fixed_point
      L D hLD N hNzero f K R hK hR (by
        intro z w hz hw
        exact hNlip z w hz hw) hself hcontract
  let z : FullJet T := y.val
  have hyfull : y.1 ∈ fullParabolicJetSet T alpha hT.le := by
    rw [← hY]
    exact y.2
  have hybound : ‖y.1‖ ≤ R := by
    simpa using hy
  have hzfull : z ∈ fullParabolicJetSet T alpha hT.le := by
    simpa [z] using hyfull
  have hzbound : ‖z‖ ≤ R := by
    simpa [z] using hybound
  obtain ⟨b, hbgraph, hbinverse, hN_Hvalue⟩ := hN_Hspec y hy
  have hzeroTrace :=
    PoincareConjecture.ParallelImplementation.ZeroTraceValueSmallness.zero_trace_value_smallness
      T alpha hT.le z hzfull
  have hytime : ‖z.1.2‖ ≤ ‖z‖ :=
    (norm_snd_le z.1).trans (norm_fst_le z)
  have hqbound (p : Slab T) : ‖z.1.1.1.1 p‖ ≤ T * R := by
    calc
      ‖z.1.1.1.1 p‖ ≤ ‖z.1.1.1.1‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ T * ‖z.1.2‖ := hzeroTrace.2
      _ ≤ T * ‖z‖ := mul_le_mul_of_nonneg_left hytime hT.le
      _ ≤ T * R := mul_le_mul_of_nonneg_left hzbound hT.le
  have hTleτ : T ≤ T + 8 * T ^ (1-alpha/2) := by
    have hpow : 0 ≤ T ^ (1-alpha/2) := by positivity
    linarith
  have hEsmall (p : Slab T) : ‖E (z.1.1.1.1 p)‖ ≤ (1/2:ℝ) := by
    calc
      ‖E (z.1.1.1.1 p)‖ ≤ ‖E‖ * ‖z.1.1.1.1 p‖ := E.le_opNorm _
      _ ≤ 3 * (T * R) := by
        calc
          ‖E‖ * ‖z.1.1.1.1 p‖ ≤ 3 * ‖z.1.1.1.1 p‖ :=
            mul_le_mul_of_nonneg_right hEnorm (norm_nonneg _)
          _ ≤ 3 * (T * R) := mul_le_mul_of_nonneg_left (hqbound p) (by norm_num)
      _ = 3 * T * R := by ring
      _ ≤ 3 * (T + 8 * T ^ (1-alpha/2)) * R := by
        calc
          3 * T * R = T * (3 * R) := by ring
          _ ≤ (T + 8 * T ^ (1-alpha/2)) * (3 * R) :=
            mul_le_mul_of_nonneg_right hTleτ (by positivity)
          _ = 3 * (T + 8 * T ^ (1-alpha/2)) * R := by ring
      _ ≤ 1/2 := hsmallT.1
  have hcoercive (p : Slab T) (v : E3) :
      (1/2:ℝ) * ‖v‖^2 ≤ inner ℝ ((1 + E (z.1.1.1.1 p)) v) v := by
    let A := E (z.1.1.1.1 p)
    have hAv : ‖A v‖ ≤ (1/2:ℝ) * ‖v‖ := by
      calc
        ‖A v‖ ≤ ‖A‖ * ‖v‖ := A.le_opNorm v
        _ ≤ (1/2:ℝ) * ‖v‖ := mul_le_mul_of_nonneg_right (by simpa [A] using hEsmall p) (norm_nonneg v)
    have habs : |inner ℝ (A v) v| ≤ (1/2:ℝ) * ‖v‖^2 := by
      calc
        |inner ℝ (A v) v| ≤ ‖A v‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ ((1/2:ℝ) * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right hAv (norm_nonneg v)
        _ = (1/2:ℝ) * ‖v‖^2 := by ring
    have hmetric : inner ℝ ((1 + A) v) v = ‖v‖^2 + inner ℝ (A v) v := by
      rw [show (1 + A) v = v + A v by simp, inner_add_left, real_inner_self_eq_norm_sq]
    have hperturb : -(1/2:ℝ) * ‖v‖^2 ≤ inner ℝ (A v) v := by
      calc
        -(1/2:ℝ) * ‖v‖^2 = -((1/2:ℝ) * ‖v‖^2) := by ring
        _ ≤ inner ℝ (A v) v := neg_le_of_abs_le habs
    rw [show E (z.1.1.1.1 p) = A by rfl, hmetric]
    nlinarith
  have hsource (p : Slab T) :
      (f + N y).1.1 p = F.1 p +
        (∑ i : Fin 3, ∑ j : Fin 3,
          ((b.1 p-1) (EuclideanSpace.single j 1)) i •
            y.1.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
          G (y.1.1.1.1.2.1 p) (y.1.1.1.1.2.1 p) := by
    change F.1 p + ((N_H y).1.1 p + (N_G y).1.1 p) = _
    rw [hN_Hvalue p, hN_Gvalue y p, hPvalue y p]
    abel
  refine ⟨z, hzfull, hzbound, b, hbgraph, ?_⟩
  intro p
  refine ⟨?_, ?_, ?_⟩
  · simpa [z] using hbinverse p
  · intro v
    exact hcoercive p v
  · calc
      z.1.2 p - (∑ i : Fin 3, z.1.1.1.2.2 p
          (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) = (L y).1.1 p :=
        (hLvalue y p).symm
      _ = (f + N y).1.1 p := congrArg (fun u : X => u.1.1 p) hLy
      _ = F.1 p +
          (∑ i : Fin 3, ∑ j : Fin 3,
            ((b.1 p-1) (EuclideanSpace.single j 1)) i •
              z.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) +
            G (z.1.1.1.2.1 p) (z.1.1.1.2.1 p) := by
        simpa [z] using hsource p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.InverseMetricGradientHeatSolution
