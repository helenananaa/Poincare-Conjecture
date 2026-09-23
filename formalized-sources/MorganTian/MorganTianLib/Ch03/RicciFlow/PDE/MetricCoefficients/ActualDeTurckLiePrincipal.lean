import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualGaugeDifferentiable
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualGaugeLoweringNeighborhood
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckPrincipalContraction
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeLowering
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LoweredGaugeFieldDerivative
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateLieMetricLowering
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckLieLowerOrder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricJetSymmetry
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricSecondJetSymmetry
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricInverseBounds
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PositivePerturbation
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The complete coordinate Lie expression of the actual DeTurck vector has the expected principal term. -/
theorem actual_deturck_lie_principal_split (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w=inner ℝ v (G y w))
    (x : E3) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (i j : Fin 3) :
    let P := fun a : Fin 3 => fderiv ℝ G x (EuclideanSpace.single a 1);
    let C : Matrix (Fin 3) (Fin 3) ℝ := fun a b => ((G x).inverse (EuclideanSpace.single b 1)) a;
    let Q := fun a b m n : Fin 3 =>
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single b 1)) x
        (EuclideanSpace.single a 1) (EuclideanSpace.single n 1)) m;
    let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
      coordinateDeTurckGauge (G y) (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k);
    coordinateLieMetricExpr G W x i j =
      (∑ p : Fin 3, ∑ q : Fin 3, C p q*(Q i p j q+Q j p i q-Q i j p q))+
        deturckLieLowerOrder (G x) P i j :=
/- SWARM_PROOF_BEGIN -/
by
  let P : Fin 3 → E3 →L[ℝ] E3 := fun a =>
    fderiv ℝ G x (EuclideanSpace.single a 1)
  let C : Matrix (Fin 3) (Fin 3) ℝ := fun a b =>
    ((G x).inverse (EuclideanSpace.single b 1)) a
  let Q : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b m n =>
    (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single b 1)) x
      (EuclideanSpace.single a 1) (EuclideanSpace.single n 1)) m
  let W : E3 → E3 := fun y => WithLp.toLp 2 (fun k : Fin 3 =>
    coordinateDeTurckGauge (G y)
      (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k)
  change coordinateLieMetricExpr G W x i j =
    (∑ p : Fin 3, ∑ q : Fin 3,
      C p q * (Q i p j q + Q j p i q - Q i j p q)) +
        deturckLieLowerOrder (G x) P i j
  have hGx : DifferentiableAt ℝ G x :=
    hG.contDiffAt.differentiableAt (by norm_num)
  have hWx : DifferentiableAt ℝ W x := by
    dsimp [W]
    exact actual_deturck_gauge_differentiable G hG x c hc hpos
  have hLie := coordinate_lie_metric_lowering G W x hGx hWx i j
  have hLowerDeriv (r k : Fin 3) :
      fderiv ℝ (fun y : E3 => (G y (W y)) k) x
          (EuclideanSpace.single r 1) =
        fderiv ℝ (fun y : E3 => loweredDeTurckGauge (G y)
          (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k) x
          (EuclideanSpace.single r 1) := by
    have h := actual_gauge_lowering_eventually G hG hsym x c hc hpos k
    have hfd :
        fderiv ℝ (fun y : E3 => (G y (W y)) k) x =
          fderiv ℝ (fun y : E3 => loweredDeTurckGauge (G y)
            (fun a : Fin 3 => fderiv ℝ G y (EuclideanSpace.single a 1)) k) x := by
      exact Filter.EventuallyEq.fderiv_eq h
    exact congrArg (fun L : E3 →L[ℝ] ℝ => L (EuclideanSpace.single r 1)) hfd
  have hJetI := lowered_gauge_field_derivative G hG x c hc hpos i j
  have hJetJ := lowered_gauge_field_derivative G hG x c hc hpos j i
  have hInvSym := (symmetric_inverse_bounds (G x) c hc hpos (hsym x)).1
  have hCsym : ∀ p q : Fin 3, C p q = C q p := by
    intro p q
    dsimp [C]
    simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
      hInvSym (EuclideanSpace.single q 1) (EuclideanSpace.single p 1)
  obtain ⟨hQderiv, _⟩ := metric_second_jets_symmetric G hG hsym x
  have hQsym : ∀ a b m n : Fin 3, Q a b m n = Q b a m n := by
    intro a b m n
    dsimp [Q]
    exact congrArg (fun L : E3 →L[ℝ] E3 => L (EuclideanSpace.single n 1) m)
      (hQderiv a b)
  calc
    coordinateLieMetricExpr G W x i j =
        fderiv ℝ (fun y : E3 => (G y (W y)) j) x (EuclideanSpace.single i 1) +
          fderiv ℝ (fun y : E3 => (G y (W y)) i) x (EuclideanSpace.single j 1) +
          (∑ k : Fin 3, W x k *
            ((fderiv ℝ G x (EuclideanSpace.single k 1)
                (EuclideanSpace.single j 1)) i -
              (fderiv ℝ G x (EuclideanSpace.single i 1)
                (EuclideanSpace.single k 1)) j -
              (fderiv ℝ G x (EuclideanSpace.single j 1)
                (EuclideanSpace.single k 1)) i)) := hLie
    _ = ((1 / 2 : ℝ) * (∑ p : Fin 3, ∑ q : Fin 3,
            C p q * (Q i p j q + Q i q j p - Q i j p q)) +
          loweredGaugeJet (G x) P i j) +
        ((1 / 2 : ℝ) * (∑ p : Fin 3, ∑ q : Fin 3,
            C p q * (Q j p i q + Q j q i p - Q j i p q)) +
          loweredGaugeJet (G x) P j i) +
        (∑ k : Fin 3, coordinateDeTurckGauge (G x) P k *
          ((P k (EuclideanSpace.single j 1)) i -
            (P i (EuclideanSpace.single k 1)) j -
            (P j (EuclideanSpace.single k 1)) i)) := by
      rw [hLowerDeriv i j, hLowerDeriv j i, hJetI, hJetJ]
    _ = ((1 / 2 : ℝ) * (∑ p : Fin 3, ∑ q : Fin 3,
            C p q * (Q i p j q + Q i q j p - Q i j p q)) +
          (1 / 2 : ℝ) * (∑ p : Fin 3, ∑ q : Fin 3,
            C p q * (Q j p i q + Q j q i p - Q j i p q))) +
        loweredGaugeJet (G x) P i j + loweredGaugeJet (G x) P j i +
        (∑ k : Fin 3, coordinateDeTurckGauge (G x) P k *
          ((P k (EuclideanSpace.single j 1)) i -
            (P i (EuclideanSpace.single k 1)) j -
            (P j (EuclideanSpace.single k 1)) i)) := by ring
    _ = (∑ p : Fin 3, ∑ q : Fin 3,
          C p q * (Q i p j q + Q j p i q - Q i j p q)) +
        deturckLieLowerOrder (G x) P i j := by
      rw [deturck_principal_contraction C Q hCsym hQsym i j]
      rw [deturckLieLowerOrder]
      ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
