import MorganTianLib.Ch01.InvGramTrace
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoerciveInverse
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** metric trace change basis. -/
theorem metric_trace_change_basis (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0 < c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hsym : ∀ v w : E3, inner ℝ (A v) w = inner ℝ v (A w))
    (B : E3 ≃L[ℝ] E3) (D : E3 →L[ℝ] E3 →L[ℝ] E3) :
    let e := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ);
    let C := B.toContinuousLinearMap.adjoint.comp (A.comp B.toContinuousLinearMap);
    (∑ i : Fin 3, ∑ j : Fin 3, (A.inverse (e j)) i • D (e i) (e j)) =
      ∑ i : Fin 3, ∑ j : Fin 3, (C.inverse (e j)) i • D (B (e i)) (B (e j)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let e : Fin 3 → E3 := fun i => EuclideanSpace.single i (1 : ℝ)
  let C : E3 →L[ℝ] E3 :=
    B.toContinuousLinearMap.adjoint.comp (A.comp B.toContinuousLinearMap)
  change (∑ i : Fin 3, ∑ j : Fin 3,
      (A.inverse (e j)) i • D (e i) (e j)) =
    ∑ i : Fin 3, ∑ j : Fin 3,
      (C.inverse (e j)) i • D (B (e i)) (B (e j))
  have hsum_apply (f : Fin 3 → E3) (r : Fin 3) :
      (∑ k : Fin 3, f k) r = ∑ k : Fin 3, (f k) r := by
    change EuclideanSpace.projₗ r (∑ k : Fin 3, f k) = _
    rw [map_sum]
    change (∑ k : Fin 3, (f k).ofLp r) = _
    rfl
  have hdecomp (x : E3) :
      (∑ k : Fin 3, x k • e k) = x := by
    ext r
    change (∑ k : Fin 3,
      x.ofLp k * (EuclideanSpace.single k (1 : ℝ)).ofLp r) = x.ofLp r
    simp [PiLp.single_apply]
  obtain ⟨eA, heA, _⟩ := coercive_operator_inverse A c hc hA
  have hAinv : A.inverse = eA.symm.toContinuousLinearMap := by
    rw [← heA]
    exact ContinuousLinearMap.inverse_equiv eA
  have hAleft (x : E3) : A (A.inverse x) = x := by
    rw [hAinv, ← heA]
    simp
  have hAright (x : E3) : A.inverse (A x) = x := by
    rw [hAinv, ← heA]
    simp
  let K : ℝ := ‖B.symm.toContinuousLinearMap‖ + 1
  let cC : ℝ := c / K ^ 2
  have hK : 0 < K := by
    dsimp [K]
    positivity
  have hcC : 0 < cC := by
    dsimp [cC]
    exact div_pos hc (by positivity)
  have hCcoercive : ∀ v : E3, cC * ‖v‖ ^ 2 ≤ inner ℝ (C v) v := by
    intro v
    have hvnorm : ‖v‖ ≤ K * ‖B v‖ := by
      calc
        ‖v‖ = ‖B.symm.toContinuousLinearMap (B v)‖ := by simp
        _ ≤ ‖B.symm.toContinuousLinearMap‖ * ‖B v‖ :=
          B.symm.toContinuousLinearMap.le_opNorm _
        _ ≤ K * ‖B v‖ := by
          dsimp [K]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
            (norm_nonneg _)
    have hvnorm2 : ‖v‖ ^ 2 ≤ (K * ‖B v‖) ^ 2 := by
      exact (sq_le_sq₀ (norm_nonneg v) (by positivity)).2 hvnorm
    calc
      cC * ‖v‖ ^ 2 ≤ cC * (K * ‖B v‖) ^ 2 :=
        mul_le_mul_of_nonneg_left hvnorm2 hcC.le
      _ = c * ‖B v‖ ^ 2 := by
        dsimp [cC]
        field_simp [ne_of_gt hK]
      _ ≤ inner ℝ (A (B.toContinuousLinearMap v))
          (B.toContinuousLinearMap v) := hA (B.toContinuousLinearMap v)
      _ = inner ℝ (C v) v := by
        symm
        change inner ℝ
          (B.toContinuousLinearMap.adjoint (A (B.toContinuousLinearMap v))) v =
            inner ℝ (A (B.toContinuousLinearMap v))
              (B.toContinuousLinearMap v)
        rw [ContinuousLinearMap.adjoint_inner_left]
  obtain ⟨eC, heC, _⟩ := coercive_operator_inverse C cC hcC hCcoercive
  have hCinv : C.inverse = eC.symm.toContinuousLinearMap := by
    rw [← heC]
    exact ContinuousLinearMap.inverse_equiv eC
  have hCleft (x : E3) : C.inverse (C x) = x := by
    rw [hCinv, ← heC]
    simp
  have hCB (x : E3) : C (B.symm x) =
      B.toContinuousLinearMap.adjoint (A x) := by
    dsimp [C]
    simp
  let H : E3 →L[ℝ] E3 :=
    B.toContinuousLinearMap.comp (C.inverse.comp B.toContinuousLinearMap.adjoint)
  have hHA (x : E3) : H (A x) = x := by
    change B.toContinuousLinearMap
      (C.inverse (B.toContinuousLinearMap.adjoint (A x))) = x
    calc
      B.toContinuousLinearMap
          (C.inverse (B.toContinuousLinearMap.adjoint (A x))) =
          B.toContinuousLinearMap (C.inverse (C (B.symm x))) := by rw [← hCB x]
      _ = B.toContinuousLinearMap (B.symm x) := by rw [hCleft]
      _ = x := by simp
  have hH : H = A.inverse := by
    apply ContinuousLinearMap.ext
    intro x
    calc
      H x = H (A (A.inverse x)) := by rw [hAleft]
      _ = A.inverse x := hHA _
  have hAdjDecomp (j : Fin 3) :
      (∑ l : Fin 3, (B (e l)) j • e l) =
        B.toContinuousLinearMap.adjoint (e j) := by
    ext r
    calc
      (∑ l : Fin 3, (B (e l)) j • e l) r = (B (e r)) j := by
        rw [hsum_apply]
        simp [e, PiLp.single_apply, smul_eq_mul]
      _ = inner ℝ (e j) (B.toContinuousLinearMap (e r)) := by
        rw [EuclideanSpace.inner_single_left]
        simp [e]
      _ = inner ℝ (B.toContinuousLinearMap.adjoint (e j)) (e r) := by
        rw [ContinuousLinearMap.adjoint_inner_left]
      _ = (B.toContinuousLinearMap.adjoint (e j)) r := by
        rw [EuclideanSpace.inner_single_right]
        simp [e]
  have hCcoord (j k : Fin 3) :
      (C.inverse (B.toContinuousLinearMap.adjoint (e j))) k =
        ∑ l : Fin 3, (B (e l)) j * (C.inverse (e l)) k := by
    rw [← hAdjDecomp j, map_sum]
    simp only [map_smul]
    rw [hsum_apply]
    simp [smul_eq_mul]
  have hBcoord (x : E3) (i : Fin 3) :
      (B.toContinuousLinearMap x) i =
        ∑ k : Fin 3, x k * (B.toContinuousLinearMap (e k)) i := by
    calc
      (B.toContinuousLinearMap x) i =
          (B.toContinuousLinearMap (∑ k : Fin 3, x k • e k)) i := by
        rw [hdecomp x]
      _ = (∑ k : Fin 3, x k • B.toContinuousLinearMap (e k)) i := by
        rw [map_sum]
        simp only [map_smul]
      _ = ∑ k : Fin 3, x k * (B.toContinuousLinearMap (e k)) i := by
        rw [hsum_apply]
        simp [smul_eq_mul]
  have hcoeff (i j : Fin 3) :
      (A.inverse (e j)) i =
        ∑ k : Fin 3, ∑ l : Fin 3,
          (C.inverse (e l)) k * (B (e k)) i * (B (e l)) j := by
    calc
      (A.inverse (e j)) i = (H (e j)) i := by rw [hH]
      _ = ∑ k : Fin 3,
          (C.inverse (B.toContinuousLinearMap.adjoint (e j))) k * (B (e k)) i := by
        change (B.toContinuousLinearMap
          (C.inverse (B.toContinuousLinearMap.adjoint (e j)))) i = _
        exact hBcoord (C.inverse (B.toContinuousLinearMap.adjoint (e j))) i
      _ = ∑ k : Fin 3, ∑ l : Fin 3,
          ((B (e l)) j * (C.inverse (e l)) k) * (B (e k)) i := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hCcoord]
        rw [Finset.sum_mul]
      _ = ∑ k : Fin 3, ∑ l : Fin 3,
          (C.inverse (e l)) k * (B (e k)) i * (B (e l)) j := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        ring
  have hDexpand (x y : E3) :
      D x y = ∑ i : Fin 3, ∑ j : Fin 3,
        (x i * y j) • D (e i) (e j) := by
    calc
      D x y = D (∑ i : Fin 3, x i • e i) y := by rw [hdecomp]
      _ = (∑ i : Fin 3, x i • D (e i)) y := by
        congr 1
        rw [map_sum]
        exact Finset.sum_congr rfl
          (fun i hi => LinearMap.map_smul D.toLinearMap (x i) (e i))
      _ = ∑ i : Fin 3, (x i • D (e i)) y := by simp
      _ = ∑ i : Fin 3, x i • D (e i) y := by
        exact Finset.sum_congr rfl (fun i hi => LinearMap.smul_apply _ _ _)
      _ = ∑ i : Fin 3, x i • D (e i) (∑ j : Fin 3, y j • e j) := by
        rw [hdecomp]
      _ = ∑ i : Fin 3, x i • ∑ j : Fin 3, y j • D (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        rw [map_sum]
        exact Finset.sum_congr rfl
          (fun j hj => LinearMap.map_smul (D (e i)).toLinearMap (y j) (e j))
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (x i * y j) • D (e i) (e j) := by
        simp only [Finset.smul_sum, smul_smul]
  have hRHSexpand :
      (∑ k : Fin 3, ∑ l : Fin 3,
        (C.inverse (e l)) k • D (B (e k)) (B (e l))) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (∑ k : Fin 3, ∑ l : Fin 3,
          (C.inverse (e l)) k * (B (e k)) i * (B (e l)) j) •
            D (e i) (e j) := by
    calc
      (∑ k : Fin 3, ∑ l : Fin 3,
          (C.inverse (e l)) k • D (B (e k)) (B (e l))) =
        ∑ k : Fin 3, ∑ l : Fin 3,
          (C.inverse (e l)) k •
            ∑ i : Fin 3, ∑ j : Fin 3,
              ((B (e k)) i * (B (e l)) j) • D (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        rw [hDexpand]
      _ = ∑ k : Fin 3, ∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
          ((C.inverse (e l)) k * ((B (e k)) i * (B (e l)) j)) •
            D (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [smul_smul]
      _ = ∑ k : Fin 3, ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          ((C.inverse (e l)) k * ((B (e k)) i * (B (e l)) j)) •
            D (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
      _ = ∑ i : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          ((C.inverse (e l)) k * ((B (e k)) i * (B (e l)) j)) •
            D (e i) (e j) := by
        rw [Finset.sum_comm]
      _ = ∑ i : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3,
          ((C.inverse (e l)) k * ((B (e k)) i * (B (e l)) j)) •
            D (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_comm]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, ∑ l : Fin 3,
          ((C.inverse (e l)) k * ((B (e k)) i * (B (e l)) j)) •
            D (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_comm]
      _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ k : Fin 3, ∑ l : Fin 3,
            (C.inverse (e l)) k * (B (e k)) i * (B (e l)) j) •
              D (e i) (e j) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        calc
          (∑ k : Fin 3, ∑ l : Fin 3,
              ((C.inverse (e l)) k * ((B (e k)) i * (B (e l)) j)) •
                D (e i) (e j)) =
            ∑ k : Fin 3,
              (∑ l : Fin 3,
                (C.inverse (e l)) k * ((B (e k)) i * (B (e l)) j)) •
                  D (e i) (e j) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [← Finset.sum_smul]
          _ = (∑ k : Fin 3, ∑ l : Fin 3,
              (C.inverse (e l)) k * ((B (e k)) i * (B (e l)) j)) •
                D (e i) (e j) := by rw [← Finset.sum_smul]
          _ = (∑ k : Fin 3, ∑ l : Fin 3,
              (C.inverse (e l)) k * (B (e k)) i * (B (e l)) j) •
                D (e i) (e j) := by
            congr 1
            apply Finset.sum_congr rfl
            intro k hk
            apply Finset.sum_congr rfl
            intro l hl
            ring
  calc
    (∑ i : Fin 3, ∑ j : Fin 3,
        (A.inverse (e j)) i • D (e i) (e j)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (∑ k : Fin 3, ∑ l : Fin 3,
          (C.inverse (e l)) k * (B (e k)) i * (B (e l)) j) •
            D (e i) (e j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hcoeff]
    _ = ∑ k : Fin 3, ∑ l : Fin 3,
        (C.inverse (e l)) k • D (B (e k)) (B (e l)) := hRHSexpand.symm
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
