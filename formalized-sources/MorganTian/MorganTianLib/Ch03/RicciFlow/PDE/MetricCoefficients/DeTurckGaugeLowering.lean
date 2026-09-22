import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckGaugeVector
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LoweredDeTurckGauge
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Lowering the actual gauge vector gives the explicit first-jet expression. -/
theorem coordinate_deturck_gauge_lowering (A : E3 →L[ℝ] E3)
    (P : Fin 3 → E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hP : ∀ r : Fin 3, ∀ v w : E3, inner ℝ (P r v) w=inner ℝ v (P r w))
    (j : Fin 3) :
    (∑ k : Fin 3, (A (EuclideanSpace.single k 1)) j * coordinateDeTurckGauge A P k) =
      loweredDeTurckGauge A P j :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨e, he, _⟩ := coercive_operator_inverse A c hc hA
  have hAi : A.inverse = e.symm.toContinuousLinearMap := by
    rw [← he]
    exact ContinuousLinearMap.inverse_equiv e
  have hAinv (x : E3) : A (A.inverse x) = x := by
    simpa [hAi, ← he] using e.apply_symm_apply x
  have hdecomp (x : E3) :
      (∑ k : Fin 3, x k • EuclideanSpace.single k (1 : ℝ)) = x := by
    ext r
    change (∑ k : Fin 3,
      x.ofLp k * (EuclideanSpace.single k (1 : ℝ)).ofLp r) = x.ofLp r
    simp [PiLp.single_apply]
  have hsum_apply (f : Fin 3 → E3) (r : Fin 3) :
      (∑ k : Fin 3, f k) r = ∑ k : Fin 3, (f k) r := by
    change EuclideanSpace.projₗ r (∑ k : Fin 3, f k) = _
    rw [map_sum]
    change (∑ k : Fin 3, (f k).ofLp r) = _
    rfl
  have hcontract (l : Fin 3) :
      ∑ k : Fin 3,
          A (EuclideanSpace.single k 1) j *
            (A.inverse (EuclideanSpace.single l 1)) k =
        if l = j then 1 else 0 := by
    calc
      (∑ k : Fin 3,
          A (EuclideanSpace.single k 1) j *
            (A.inverse (EuclideanSpace.single l 1)) k) =
          ∑ k : Fin 3,
            (A.inverse (EuclideanSpace.single l 1)) k *
              A (EuclideanSpace.single k 1) j := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (A (∑ k : Fin 3,
          (A.inverse (EuclideanSpace.single l 1)) k •
            EuclideanSpace.single k (1 : ℝ))) j := by
        rw [map_sum, hsum_apply]
        simp [smul_eq_mul, mul_comm]
      _ = (A (A.inverse (EuclideanSpace.single l 1))) j := by
        rw [hdecomp]
      _ = (EuclideanSpace.single l (1 : ℝ)) j :=
        congrArg (fun x : E3 => x j) (hAinv _)
      _ = if l = j then 1 else 0 := by
        simp [PiLp.single_apply, eq_comm]
  have hgamma (p q : Fin 3) :
      ∑ k : Fin 3,
          A (EuclideanSpace.single k 1) j * coordinateChristoffel A P k p q =
        (1 / 2 : ℝ) *
          ((P p (EuclideanSpace.single j 1)) q +
            (P q (EuclideanSpace.single j 1)) p -
              (P j (EuclideanSpace.single q 1)) p) := by
    unfold coordinateChristoffel
    let B : Fin 3 → ℝ := fun l =>
      (P p (EuclideanSpace.single l 1)) q +
        (P q (EuclideanSpace.single l 1)) p -
          (P l (EuclideanSpace.single q 1)) p
    change
      (∑ k : Fin 3,
          A (EuclideanSpace.single k 1) j *
            ((1 / 2 : ℝ) * ∑ l : Fin 3,
              (A.inverse (EuclideanSpace.single l 1)) k * B l)) =
        (1 / 2 : ℝ) * B j
    calc
      _ = (1 / 2 : ℝ) * ∑ k : Fin 3,
          A (EuclideanSpace.single k 1) j *
            (∑ l : Fin 3,
              (A.inverse (EuclideanSpace.single l 1)) k * B l) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = (1 / 2 : ℝ) * ∑ k : Fin 3, ∑ l : Fin 3,
          (A (EuclideanSpace.single k 1) j *
            (A.inverse (EuclideanSpace.single l 1)) k) * B l := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l hl
        ring
      _ = (1 / 2 : ℝ) * ∑ l : Fin 3,
          (∑ k : Fin 3,
            A (EuclideanSpace.single k 1) j *
              (A.inverse (EuclideanSpace.single l 1)) k) * B l := by
        congr 1
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul]
      _ = (1 / 2 : ℝ) * B j := by
        simp_rw [hcontract]
        simp
  unfold coordinateDeTurckGauge loweredDeTurckGauge
  have hP1 (p q : Fin 3) :
      (P p (EuclideanSpace.single j 1)) q =
        (P p (EuclideanSpace.single q 1)) j := by
    calc
      (P p (EuclideanSpace.single j 1)) q =
          inner ℝ (EuclideanSpace.single q 1)
            (P p (EuclideanSpace.single j 1)) := by
        rw [EuclideanSpace.inner_single_left]
        simp
      _ = inner ℝ (P p (EuclideanSpace.single q 1))
            (EuclideanSpace.single j 1) :=
        (hP p (EuclideanSpace.single q 1)
          (EuclideanSpace.single j 1)).symm
      _ = (P p (EuclideanSpace.single q 1)) j := by
        rw [EuclideanSpace.inner_single_right]
        simp
  have hP2 (p q : Fin 3) :
      (P q (EuclideanSpace.single j 1)) p =
        (P q (EuclideanSpace.single p 1)) j := by
    calc
      (P q (EuclideanSpace.single j 1)) p =
          inner ℝ (EuclideanSpace.single p 1)
            (P q (EuclideanSpace.single j 1)) := by
        rw [EuclideanSpace.inner_single_left]
        simp
      _ = inner ℝ (P q (EuclideanSpace.single p 1))
            (EuclideanSpace.single j 1) :=
        (hP q (EuclideanSpace.single p 1)
          (EuclideanSpace.single j 1)).symm
      _ = (P q (EuclideanSpace.single p 1)) j := by
        rw [EuclideanSpace.inner_single_right]
        simp
  have hgamma' (p q : Fin 3) :
      ∑ k : Fin 3,
          A (EuclideanSpace.single k 1) j * coordinateChristoffel A P k p q =
        (1 / 2 : ℝ) *
          ((P p (EuclideanSpace.single q 1)) j +
            (P q (EuclideanSpace.single p 1)) j -
              (P j (EuclideanSpace.single q 1)) p) := by
    rw [hgamma]
    rw [hP1 p q, hP2 p q]
  calc
    _ = ∑ k : Fin 3, ∑ p : Fin 3, ∑ q : Fin 3,
        A (EuclideanSpace.single k 1) j *
          ((A.inverse (EuclideanSpace.single q 1)) p *
            coordinateChristoffel A P k p q) := by
      simp_rw [Finset.mul_sum]
    _ = ∑ p : Fin 3, ∑ k : Fin 3, ∑ q : Fin 3,
        A (EuclideanSpace.single k 1) j *
          ((A.inverse (EuclideanSpace.single q 1)) p *
            coordinateChristoffel A P k p q) := by
      exact Finset.sum_comm
    _ = ∑ p : Fin 3, ∑ q : Fin 3, ∑ k : Fin 3,
        A (EuclideanSpace.single k 1) j *
          ((A.inverse (EuclideanSpace.single q 1)) p *
            coordinateChristoffel A P k p q) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_comm
    _ = ∑ p : Fin 3, ∑ q : Fin 3,
        (A.inverse (EuclideanSpace.single q 1)) p *
          (∑ k : Fin 3,
            A (EuclideanSpace.single k 1) j *
              coordinateChristoffel A P k p q) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = ∑ p : Fin 3, ∑ q : Fin 3,
        (A.inverse (EuclideanSpace.single q 1)) p *
          ((1 / 2 : ℝ) *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [hgamma' p q]
    _ = (1 / 2 : ℝ) *
        ∑ p : Fin 3, ∑ q : Fin 3,
          (A.inverse (EuclideanSpace.single q 1)) p *
            ((P p (EuclideanSpace.single q 1)) j +
              (P q (EuclideanSpace.single p 1)) j -
                (P j (EuclideanSpace.single q 1)) p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
