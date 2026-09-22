import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateMetricCompatibility
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricInverseBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Torsion freedom and metric compatibility determine the actual coordinate coefficients. -/
theorem coordinate_connection_unique (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hAs : ∀ v w : E3, inner ℝ (A v) w=inner ℝ v (A w))
    (P : Fin 3 → E3 →L[ℝ] E3)
    (hP : ∀ r : Fin 3, ∀ v w : E3, inner ℝ (P r v) w=inner ℝ v (P r w))
    (Γ : Fin 3 → Fin 3 → Fin 3 → ℝ)
    (htor : ∀ k i j, Γ k i j=Γ k j i)
    (hcompat : ∀ r i j, (P r (EuclideanSpace.single j 1)) i =
      (∑ k : Fin 3, (A (EuclideanSpace.single k 1)) j*Γ k r i)+
      (∑ k : Fin 3, (A (EuclideanSpace.single k 1)) i*Γ k r j)) :
    Γ=coordinateChristoffel A P :=
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
  have hcomp' : ∀ x : E3, A.inverse (A x) = x := by
    intro x
    rw [hAi, ← he]
    simp
  have h_expand : ∀ x : E3,
      (∑ k : Fin 3, x k • EuclideanSpace.single k (1 : ℝ)) = x := by
    intro x
    simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  have hcomp_coord : ∀ k m : Fin 3,
      ∑ l : Fin 3, A.inverse (EuclideanSpace.single l 1) k *
          A (EuclideanSpace.single m 1) l =
        if k = m then 1 else 0 := by
    intro k m
    calc
      ∑ l : Fin 3, A.inverse (EuclideanSpace.single l 1) k *
          A (EuclideanSpace.single m 1) l =
          (A.inverse (A (EuclideanSpace.single m 1))) k := by
            conv_rhs => rw [← h_expand (A (EuclideanSpace.single m 1))]
            simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
              Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro l hl
            ring
      _ = (EuclideanSpace.single m 1) k := congrArg (fun x : E3 => x k)
        (hcomp' (EuclideanSpace.single m 1))
      _ = if k = m then 1 else 0 := by
        rw [EuclideanSpace.single_apply]
  have h_lower : ∀ (j r i : Fin 3),
      ∑ k : Fin 3, A (EuclideanSpace.single k 1) j * Γ k r i =
        (1 / 2 : ℝ) *
          ((P r (EuclideanSpace.single j 1)) i +
            (P i (EuclideanSpace.single j 1)) r -
              (P j (EuclideanSpace.single i 1)) r) := by
    intro j r i
    have hPcoord : ∀ (s a b : Fin 3),
        (P s (EuclideanSpace.single a 1)) b =
          (P s (EuclideanSpace.single b 1)) a := by
      intro s a b
      simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
        hP s (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)
    have h1 := hcompat r i j
    have h2 :
        (P i (EuclideanSpace.single j 1)) r =
          (∑ k : Fin 3, A (EuclideanSpace.single k 1) j * Γ k r i) +
          (∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k j i) := by
      calc
        (P i (EuclideanSpace.single j 1)) r =
            (P i (EuclideanSpace.single r 1)) j := hPcoord i j r
        _ = (∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k i j) +
              (∑ k : Fin 3, A (EuclideanSpace.single k 1) j * Γ k i r) :=
          hcompat i j r
        _ = (∑ k : Fin 3, A (EuclideanSpace.single k 1) j * Γ k i r) +
              (∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k i j) := by
          rw [add_comm]
        _ = (∑ k : Fin 3, A (EuclideanSpace.single k 1) j * Γ k r i) +
              (∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k i j) := by
          have hs1 : (∑ k : Fin 3, A (EuclideanSpace.single k 1) j * Γ k i r) =
              ∑ k : Fin 3, A (EuclideanSpace.single k 1) j * Γ k r i := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [htor k i r]
          rw [hs1]
        _ = (∑ k : Fin 3, A (EuclideanSpace.single k 1) j * Γ k r i) +
              (∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k j i) := by
          have hs2 : (∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k i j) =
              ∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k j i := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [htor k i j]
          rw [hs2]
    have h3 :
        (P j (EuclideanSpace.single i 1)) r =
          (∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k j i) +
          (∑ k : Fin 3, A (EuclideanSpace.single k 1) i * Γ k r j) := by
      calc
        (P j (EuclideanSpace.single i 1)) r =
            (P j (EuclideanSpace.single r 1)) i := hPcoord j i r
        _ = (∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k j i) +
              (∑ k : Fin 3, A (EuclideanSpace.single k 1) i * Γ k j r) :=
          hcompat j i r
        _ = (∑ k : Fin 3, A (EuclideanSpace.single k 1) r * Γ k j i) +
              (∑ k : Fin 3, A (EuclideanSpace.single k 1) i * Γ k r j) := by
          have hs1 : (∑ k : Fin 3, A (EuclideanSpace.single k 1) i * Γ k j r) =
              ∑ k : Fin 3, A (EuclideanSpace.single k 1) i * Γ k r j := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [htor k j r]
          rw [hs1]
    linarith [h1, h2, h3]
  have h_raise : ∀ k r i : Fin 3,
      Γ k r i = ∑ l : Fin 3, A.inverse (EuclideanSpace.single l 1) k *
        (∑ m : Fin 3, A (EuclideanSpace.single m 1) l * Γ m r i) := by
    intro k r i
    calc
      Γ k r i = ∑ m : Fin 3, (if k = m then 1 else 0) * Γ m r i := by
        simp
      _ = ∑ m : Fin 3,
          (∑ l : Fin 3, A.inverse (EuclideanSpace.single l 1) k *
            A (EuclideanSpace.single m 1) l) * Γ m r i := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [hcomp_coord]
      _ = ∑ l : Fin 3, A.inverse (EuclideanSpace.single l 1) k *
          (∑ m : Fin 3, A (EuclideanSpace.single m 1) l * Γ m r i) := by
        calc
          (∑ m : Fin 3,
              (∑ l : Fin 3, A.inverse (EuclideanSpace.single l 1) k *
                A (EuclideanSpace.single m 1) l) * Γ m r i) =
              ∑ m : Fin 3, ∑ l : Fin 3,
                (A.inverse (EuclideanSpace.single l 1) k *
                  A (EuclideanSpace.single m 1) l) * Γ m r i := by
            apply Finset.sum_congr rfl
            intro m hm
            rw [Finset.sum_mul]
          _ = ∑ l : Fin 3, ∑ m : Fin 3,
                (A.inverse (EuclideanSpace.single l 1) k *
                  A (EuclideanSpace.single m 1) l) * Γ m r i := by
            rw [Finset.sum_comm]
          _ = ∑ l : Fin 3, A.inverse (EuclideanSpace.single l 1) k *
                (∑ m : Fin 3, A (EuclideanSpace.single m 1) l * Γ m r i) := by
            apply Finset.sum_congr rfl
            intro l hl
            calc
              (∑ m : Fin 3,
                  (A.inverse (EuclideanSpace.single l 1) k *
                    A (EuclideanSpace.single m 1) l) * Γ m r i) =
                  ∑ m : Fin 3, A.inverse (EuclideanSpace.single l 1) k *
                    (A (EuclideanSpace.single m 1) l * Γ m r i) := by
                apply Finset.sum_congr rfl
                intro m hm
                ring
              _ = A.inverse (EuclideanSpace.single l 1) k *
                    (∑ m : Fin 3, A (EuclideanSpace.single m 1) l * Γ m r i) := by
                rw [Finset.mul_sum]
  funext k r i
  unfold coordinateChristoffel
  rw [h_raise k r i]
  calc
    (∑ l : Fin 3, A.inverse (EuclideanSpace.single l 1) k *
        (∑ m : Fin 3, A (EuclideanSpace.single m 1) l * Γ m r i)) =
        ∑ l : Fin 3, (1 / 2 : ℝ) *
          (A.inverse (EuclideanSpace.single l 1) k *
            ((P r (EuclideanSpace.single l 1)) i +
              (P i (EuclideanSpace.single l 1)) r -
                (P l (EuclideanSpace.single i 1)) r)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [h_lower l r i]
      ring
    _ = (1 / 2 : ℝ) * ∑ l : Fin 3,
          A.inverse (EuclideanSpace.single l 1) k *
            ((P r (EuclideanSpace.single l 1)) i +
              (P i (EuclideanSpace.single l 1)) r -
                (P l (EuclideanSpace.single i 1)) r) := by
      rw [Finset.mul_sum]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
