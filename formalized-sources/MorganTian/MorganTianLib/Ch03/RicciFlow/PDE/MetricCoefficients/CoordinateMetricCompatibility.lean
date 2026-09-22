import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffel
import Mathlib
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Torsion symmetry and metric compatibility of the actual coordinate formula. -/
theorem coordinate_metric_compatibility (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hAsym : ∀ v w : E3, inner ℝ (A v) w = inner ℝ v (A w))
    (P : Fin 3 → E3 →L[ℝ] E3)
    (hP : ∀ r : Fin 3, ∀ v w : E3, inner ℝ (P r v) w = inner ℝ v (P r w)) :
    (∀ k i j : Fin 3, coordinateChristoffel A P k i j = coordinateChristoffel A P k j i) ∧
    ∀ r i j : Fin 3,
      (P r (EuclideanSpace.single j 1)) i =
        (∑ k : Fin 3, (A (EuclideanSpace.single k 1)) j * coordinateChristoffel A P k r i) +
        (∑ k : Fin 3, (A (EuclideanSpace.single k 1)) i * coordinateChristoffel A P k r j) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨e, he, he_inv⟩ := coercive_operator_inverse A c hc hA
  have hAi : A.inverse = e.symm.toContinuousLinearMap := by
    rw [← he]
    exact ContinuousLinearMap.inverse_equiv e
  have hcomp : ∀ x : E3, A (A.inverse x) = x := by
    intro x
    rw [hAi, ← he]
    simp
  have h_expand : ∀ x : E3,
      (∑ k : Fin 3, x k • EuclideanSpace.single k (1 : ℝ)) = x := by
    intro x
    simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  have hcomp_coord : ∀ j l : Fin 3,
      ∑ k : Fin 3, A (EuclideanSpace.single k 1) j *
          A.inverse (EuclideanSpace.single l 1) k =
        if j = l then 1 else 0 := by
    intro j l
    calc
      ∑ k : Fin 3, A (EuclideanSpace.single k 1) j *
          A.inverse (EuclideanSpace.single l 1) k =
          (A (A.inverse (EuclideanSpace.single l 1))) j := by
            conv_rhs => rw [← h_expand (A.inverse (EuclideanSpace.single l 1))]
            simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
              Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro k hk
            ring
      _ = (EuclideanSpace.single l 1) j := congrArg (fun x : E3 => x j)
        (hcomp (EuclideanSpace.single l 1))
      _ = if j = l then 1 else 0 := by
        rw [EuclideanSpace.single_apply]
  have hPcoord : ∀ r i j : Fin 3,
      (P r (EuclideanSpace.single i 1)) j =
        (P r (EuclideanSpace.single j 1)) i := by
    intro r i j
    simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
      hP r (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  have hsum : ∀ (j : Fin 3) (B : Fin 3 → ℝ),
      (∑ k : Fin 3, A (EuclideanSpace.single k 1) j *
        ((1 / 2 : ℝ) * ∑ l : Fin 3,
          A.inverse (EuclideanSpace.single l 1) k * B l)) =
        (1 / 2 : ℝ) * ∑ l : Fin 3,
          (if j = l then 1 else 0) * B l := by
    intro j B
    calc
      (∑ k : Fin 3, A (EuclideanSpace.single k 1) j *
        ((1 / 2 : ℝ) * ∑ l : Fin 3,
          A.inverse (EuclideanSpace.single l 1) k * B l)) =
          ∑ k : Fin 3, ∑ l : Fin 3, (1 / 2 : ℝ) *
            (A (EuclideanSpace.single k 1) j *
              A.inverse (EuclideanSpace.single l 1) k * B l) := by
        apply Finset.sum_congr rfl
        intro k hk
        calc
          A (EuclideanSpace.single k 1) j *
              ((1 / 2 : ℝ) * ∑ l : Fin 3,
                A.inverse (EuclideanSpace.single l 1) k * B l) =
              (A (EuclideanSpace.single k 1) j * (1 / 2 : ℝ)) *
                ∑ l : Fin 3, A.inverse (EuclideanSpace.single l 1) k * B l := by
                  ring
          _ = ∑ l : Fin 3, (A (EuclideanSpace.single k 1) j * (1 / 2 : ℝ)) *
                (A.inverse (EuclideanSpace.single l 1) k * B l) := by
                  rw [Finset.mul_sum]
          _ = ∑ l : Fin 3, (1 / 2 : ℝ) *
                (A (EuclideanSpace.single k 1) j *
                  A.inverse (EuclideanSpace.single l 1) k * B l) := by
                  apply Finset.sum_congr rfl
                  intro l hl
                  ring
      _ = ∑ l : Fin 3, ∑ k : Fin 3, (1 / 2 : ℝ) *
            (A (EuclideanSpace.single k 1) j *
              A.inverse (EuclideanSpace.single l 1) k * B l) := by
        rw [Finset.sum_comm]
      _ = ∑ l : Fin 3, (1 / 2 : ℝ) *
            ((∑ k : Fin 3, A (EuclideanSpace.single k 1) j *
              A.inverse (EuclideanSpace.single l 1) k) * B l) := by
        apply Finset.sum_congr rfl
        intro l hl
        calc
          (∑ k : Fin 3, (1 / 2 : ℝ) *
            (A (EuclideanSpace.single k 1) j *
              A.inverse (EuclideanSpace.single l 1) k * B l)) =
              (1 / 2 : ℝ) * ∑ k : Fin 3,
                (A (EuclideanSpace.single k 1) j *
                  A.inverse (EuclideanSpace.single l 1) k * B l) := by
                  rw [← Finset.mul_sum]
          _ = (1 / 2 : ℝ) *
              ((∑ k : Fin 3, A (EuclideanSpace.single k 1) j *
                A.inverse (EuclideanSpace.single l 1) k) * B l) := by
                  rw [Finset.sum_mul]
      _ = (1 / 2 : ℝ) * ∑ l : Fin 3,
            (if j = l then 1 else 0) * B l := by
        simp_rw [hcomp_coord]
        rw [Finset.mul_sum]
  have h_lower : ∀ (j r i : Fin 3),
      ∑ k : Fin 3, A (EuclideanSpace.single k 1) j *
          coordinateChristoffel A P k r i =
        (1 / 2 : ℝ) *
          ((P r (EuclideanSpace.single j 1)) i +
            (P i (EuclideanSpace.single j 1)) r -
              (P j (EuclideanSpace.single i 1)) r) := by
    intro j r i
    unfold coordinateChristoffel
    calc
      (∑ k : Fin 3, A (EuclideanSpace.single k 1) j *
          ((1 / 2 : ℝ) * ∑ l : Fin 3,
            A.inverse (EuclideanSpace.single l 1) k *
              ((P r (EuclideanSpace.single l 1)) i +
                (P i (EuclideanSpace.single l 1)) r -
                  (P l (EuclideanSpace.single i 1)) r))) =
          (1 / 2 : ℝ) * ∑ l : Fin 3,
            (if j = l then 1 else 0) *
              ((P r (EuclideanSpace.single l 1)) i +
                (P i (EuclideanSpace.single l 1)) r -
                  (P l (EuclideanSpace.single i 1)) r) :=
        hsum j (fun l =>
          (P r (EuclideanSpace.single l 1)) i +
            (P i (EuclideanSpace.single l 1)) r -
              (P l (EuclideanSpace.single i 1)) r)
      _ = (1 / 2 : ℝ) *
          ((P r (EuclideanSpace.single j 1)) i +
            (P i (EuclideanSpace.single j 1)) r -
              (P j (EuclideanSpace.single i 1)) r) := by
        simp
  constructor
  · intro k i j
    unfold coordinateChristoffel
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    have hp : (P l (EuclideanSpace.single j 1)) i =
        (P l (EuclideanSpace.single i 1)) j := by
      simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
        hP l (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
    rw [hp]
    ring
  · intro r i j
    rw [h_lower j r i, h_lower i r j]
    have hp := hPcoord r j i
    rw [← hp]
    ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
