import PoincareConjecture.ParallelImplementation.ZeroTraceOperatorValueProjection
import PoincareConjecture.ParallelImplementation.ProjectedInverseCorrectionBall
import PoincareConjecture.ParallelImplementation.NonlinearForcingHessianProduct
import PoincareConjecture.ParallelImplementation.OperatorHessianContraction
import PoincareConjecture.ParallelImplementation.FullJetHessianProjection
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.InverseMetricHessianNonlinearity
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology BigOperators BoundedContinuousFunction
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_inverse_metric_hessian_nonlinearity
    (T alpha R : ℝ) (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha < 1)
    (hR : 0 < R) (E : E6 →L[ℝ] (E3 →L[ℝ] E3)) (hE : ‖E‖ ≤ 3)
    (hsmall : 3*(T+8*T^(1-alpha/2))*R ≤ 1/2)
    (X : Submodule ℝ (ForcingJet E6 T)) (Y : Submodule ℝ (FullJet T))
    (hX : (X : Set (ForcingJet E6 T)) = forcingGraph E6 T alpha)
    (hY : (Y : Set (FullJet T)) = fullParabolicJetSet T alpha hT.le) :
    ∃ N : Y → X, N 0=0 ∧
      (∀ z : Y, ‖z‖ ≤ R →
        ∃ b : ForcingJet (E3 →L[ℝ] E3) T, b ∈ forcingGraph (E3 →L[ℝ] E3) T alpha ∧
          (∀ p : Slab T,
            (1+E (z.1.1.1.1.1 p))*b.1 p=1 ∧ b.1 p*(1+E (z.1.1.1.1.1 p))=1) ∧
          (∀ p : Slab T, (N z).1.1 p =
            ∑ i : Fin 3, ∑ j : Fin 3,
              ((b.1 p-1) (EuclideanSpace.single j 1)) i •
                z.1.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))) ∧
      (∀ z w : Y, ‖z‖ ≤ R → ‖w‖ ≤ R →
        ‖N z-N w‖ ≤ (648*(T+8*T^(1-alpha/2)))*(‖z‖+‖w‖)*‖z-w‖) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : NormedAddCommGroup Y := inferInstance
  letI : NormedSpace ℝ Y := inferInstance
  let C : ℝ := T + 8*T^(1-alpha/2)
  obtain ⟨P, hPnorm, hPvalue, hPgraph⟩ :=
    PoincareConjecture.ParallelImplementation.ZeroTraceOperatorValueProjection.exists_zero_trace_operator_value_projection
      T alpha hT ha ha1 Y hY E
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hPnorm3 : ‖P‖ ≤ 3*C := by
    calc
      ‖P‖ ≤ ‖E‖*C := hPnorm
      _ ≤ 3*C := mul_le_mul_of_nonneg_right hE hCnonneg
  have hPsmall : ‖P‖*R ≤ 1/2 := by
    calc
      ‖P‖*R ≤ (3*C)*R := mul_le_mul_of_nonneg_right hPnorm3 hR.le
      _ ≤ 1/2 := by simpa [C] using hsmall
  obtain ⟨J, hJ0, hJspec, hJL⟩ :=
    PoincareConjecture.ParallelImplementation.ProjectedInverseCorrectionBall.exists_projected_inverse_correction_ball
      T alpha R hR P hPgraph hPsmall
  obtain ⟨B, hBnorm, hBvalue⟩ :=
    PoincareConjecture.ParallelImplementation.OperatorHessianContraction.exists_operator_hessian_contraction
      (V := E6)
  obtain ⟨H, hHnorm, hHvalue, _, hHgraph⟩ :=
    PoincareConjecture.ParallelImplementation.FullJetHessianProjection.exists_full_jet_hessian_projection
      T alpha hT.le
  let i : Y →L[ℝ] FullJet T := Y.subtypeL
  let Q : Y →L[ℝ] ForcingJet (E3 →L[ℝ] E3 →L[ℝ] E6) T := H.comp i
  have hQnorm : ‖Q‖ ≤ 1 := by
    have hi : ‖i‖ ≤ 1 := Submodule.norm_subtypeL_le Y
    calc
      ‖Q‖ ≤ ‖H‖*‖i‖ := H.opNorm_comp_le i
      _ ≤ 1*1 := mul_le_mul hHnorm hi (norm_nonneg i) (by norm_num)
      _ = 1 := by norm_num
  have hzY (z : Y) : z.1 ∈ fullParabolicJetSet T alpha hT.le := by
    rw [← hY]
    exact z.2
  have hQgraph (z : Y) : Q z ∈ forcingGraph (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha := by
    change H z.1 ∈ forcingGraph (E3 →L[ℝ] E3 →L[ℝ] E6) T alpha
    exact hHgraph z.1 (hzY z)
  have hQvalue (z : Y) (p : Slab T) :
      (Q z).1 p = z.1.1.1.1.2.2 p := by
    change (H z.1).1 p = _
    exact hHvalue z.1 p
  let oneJet : ForcingJet (E3 →L[ℝ] E3) T :=
    ((1 : Slab T →ᵇ (E3 →L[ℝ] E3)), (0 : Pair T →ᵇ (E3 →L[ℝ] E3)))
  let b (z : Y) : ForcingJet (E3 →L[ℝ] E3) T := oneJet + J z
  have hbvalue (z : Y) (p : Slab T) : (b z).1 p = 1 + (J z).1 p := by
    simp [b, oneJet]
  have hbgraph (z : Y) (hz : ‖z‖ ≤ R) :
      b z ∈ forcingGraph (E3 →L[ℝ] E3) T alpha := by
    intro p
    change (0 : E3 →L[ℝ] E3) + (J z).2 p =
      (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
        ((1 : E3 →L[ℝ] E3) + (J z).1 p.1.1 -
          ((1 : E3 →L[ℝ] E3) + (J z).1 p.1.2))
    rw [zero_add, (hJspec z hz).1 p]
    congr 1
    abel
  have hJvalue (z : Y) (hz : ‖z‖ ≤ R) (p : Slab T) :
      (b z).1 p - 1 = (J z).1 p := by
    rw [hbvalue z p]
    abel
  let K : ℝ := 12*‖P‖
  have hJL' (z w : Y) (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
      ‖J z - J w‖ ≤ K*‖z-w‖ := by
    simpa [K] using hJL z w hz hw
  obtain ⟨N, hN0, hNvalue, hNlip⟩ :=
    PoincareConjecture.ParallelImplementation.NonlinearForcingHessianProduct.exists_nonlinear_forcing_hessian_product
      (Y := Y) (V := E3 →L[ℝ] E3) (W := E3 →L[ℝ] E3 →L[ℝ] E6) (Z := E6)
      T alpha R K hR (by positivity) X hX B J hJ0
      (fun z hz => (hJspec z hz).1) hJL' Q hQgraph
  have hcoeff : 2*‖B‖*K*‖Q‖ ≤ 648*C := by
    dsimp [K]
    calc
      2*‖B‖*(12*‖P‖)*‖Q‖ ≤ (2*9)*(12*(3*C))*1 := by
        gcongr
      _ = 648*C := by ring
  refine ⟨N, hN0, ?_, ?_⟩
  · intro z hz
    refine ⟨b z, hbgraph z hz, ?_, ?_⟩
    · intro p
      have hid := (hJspec z hz).2 p
      constructor
      · simpa [hPvalue z p, hbvalue z p] using hid.1
      · simpa [hPvalue z p, hbvalue z p] using hid.2
    · intro p
      calc
        (N z).1.1 p = B ((J z).1 p) ((Q z).1 p) := hNvalue z hz p
        _ = ∑ i : Fin 3, ∑ j : Fin 3,
            (((b z).1 p - 1) (EuclideanSpace.single j 1)) i •
              z.1.1.1.1.2.2 p (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
          rw [hBvalue]
          simp only [hJvalue z hz p, hQvalue z p]
  · intro z w hz hw
    calc
      ‖N z-N w‖ ≤ (2*‖B‖*K*‖Q‖)*(‖z‖+‖w‖)*‖z-w‖ :=
        hNlip z w hz hw
      _ ≤ (648*C)*(‖z‖+‖w‖)*‖z-w‖ := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hcoeff
            (add_nonneg (norm_nonneg z) (norm_nonneg w))
        · exact norm_nonneg (z-w)
      _ = (648*(T+8*T^(1-alpha/2)))*(‖z‖+‖w‖)*‖z-w‖ := by
        simp [C]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.InverseMetricHessianNonlinearity
