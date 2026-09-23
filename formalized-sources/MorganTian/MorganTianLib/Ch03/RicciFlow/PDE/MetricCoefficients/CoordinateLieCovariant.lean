import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateLieMetricLowering
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionMetricTrilinear
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricJetGermSymmetry
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "J3" => (E3 →L[ℝ] E3) × (Fin 3 → E3 →L[ℝ] E3)
local notation "M3" => Fin 3 → Fin 3 → ℝ

/-- **Math.** coordinate lie metric covariant. -/
theorem coordinate_lie_metric_covariant (G : E3 → (E3 →L[ℝ] E3)) (W : E3 → E3) (x : E3)
    (hG : DifferentiableAt ℝ G x) (hW : DifferentiableAt ℝ W x)
    (hsym : ∀ᶠ y : E3 in 𝓝 x, ∀ v w : E3, inner ℝ (G y v) w = inner ℝ v (G y w))
    (c : ℝ) (hc : 0 < c) (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (i j : Fin 3) :
    let e := fun k : Fin 3 => EuclideanSpace.single k (1 : ℝ);
    let P := fun r : Fin 3 => fderiv ℝ G x (e r);
    coordinateLieMetricExpr G W x i j =
      inner ℝ (G x (fderiv ℝ W x (e i) + connectionVector (G x) P (e i) (W x))) (e j) +
      inner ℝ (G x (e i)) (fderiv ℝ W x (e j) + connectionVector (G x) P (e j) (W x)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let e : Fin 3 → E3 := fun k => EuclideanSpace.single k (1 : ℝ)
  let P : Fin 3 → E3 →L[ℝ] E3 := fun r => fderiv ℝ G x (e r)
  have hexpand (v : E3) : v = ∑ k : Fin 3, v k • e k := by
    symm
    simpa [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have hself := metric_jet_selfadjoint_of_eventually G x hG hsym
  have hP : ∀ r : Fin 3, ∀ v w : E3,
      inner ℝ (P r v) w = inner ℝ v (P r w) := by
    intro r v w
    exact hself (e r) v w
  have hAsym : ∀ v w : E3, inner ℝ (G x v) w = inner ℝ v (G x w) := by
    intro v w
    exact hsym.self_of_nhds v w
  have hGcoord (a b : Fin 3) : (G x (e a)) b = (G x (e b)) a := by
    simpa [e, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
      hAsym (e a) (e b)
  have hGammaSym :=
    (coordinate_metric_compatibility (G x) c hc hpos hAsym P hP).1
  have hGammaSwap (X Y : E3) :
      connectionVector (G x) P X Y = connectionVector (G x) P Y X := by
    ext k
    change (∑ a : Fin 3, ∑ b : Fin 3,
        coordinateChristoffel (G x) P k a b * X a * Y b) =
      ∑ a : Fin 3, ∑ b : Fin 3,
        coordinateChristoffel (G x) P k a b * Y a * X b
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hGammaSym k b a]
    ring
  have hderivCoord (a b : Fin 3) :
      (fderiv ℝ G x (W x) (e b)) a =
        ∑ k : Fin 3, W x k * (P k (e b) a) := by
    conv_lhs => rw [hexpand (W x)]
    simp [P, map_sum, map_smul, smul_eq_mul]
  have hcompat := connection_metric_trilinear (G x) P c hc hpos hAsym hP
      (W x) (e j) (e i)
  have hderivCompat :
      (fderiv ℝ G x (W x) (e j)) i =
        inner ℝ (G x (connectionVector (G x) P (W x) (e j))) (e i) +
        inner ℝ (G x (e j)) (connectionVector (G x) P (W x) (e i)) := by
    calc
      (fderiv ℝ G x (W x) (e j)) i =
          ∑ k : Fin 3, W x k * (P k (e j) i) := hderivCoord i j
      _ = inner ℝ ((∑ k : Fin 3, W x k • P k) (e j)) (e i) := by
        rw [EuclideanSpace.inner_single_right]
        simp [map_sum, smul_eq_mul]
      _ = inner ℝ (G x (connectionVector (G x) P (W x) (e j))) (e i) +
          inner ℝ (G x (e j)) (connectionVector (G x) P (W x) (e i)) := hcompat
  have hderivConn :
      (fderiv ℝ G x (W x) (e j)) i =
        inner ℝ (G x (connectionVector (G x) P (e i) (W x))) (e j) +
        inner ℝ (G x (e i)) (connectionVector (G x) P (e j) (W x)) := by
    have hconvA :
        inner ℝ (G x (connectionVector (G x) P (e j) (W x))) (e i) =
          inner ℝ (G x (e i)) (connectionVector (G x) P (e j) (W x)) := by
      calc
        _ = inner ℝ (e i) (G x (connectionVector (G x) P (e j) (W x))) :=
          real_inner_comm _ _
        _ = _ := (hAsym (e i) (connectionVector (G x) P (e j) (W x))).symm
    have hconvB :
        inner ℝ (G x (e j)) (connectionVector (G x) P (e i) (W x)) =
          inner ℝ (G x (connectionVector (G x) P (e i) (W x))) (e j) := by
      calc
        _ = inner ℝ (connectionVector (G x) P (e i) (W x)) (G x (e j)) :=
          real_inner_comm _ _
        _ = _ := (hAsym (connectionVector (G x) P (e i) (W x)) (e j)).symm
    calc
      (fderiv ℝ G x (W x) (e j)) i =
          inner ℝ (G x (connectionVector (G x) P (W x) (e j))) (e i) +
            inner ℝ (G x (e j)) (connectionVector (G x) P (W x) (e i)) :=
          hderivCompat
      _ = inner ℝ (G x (connectionVector (G x) P (e j) (W x))) (e i) +
            inner ℝ (G x (e j)) (connectionVector (G x) P (e i) (W x)) := by
          rw [hGammaSwap (W x) (e j), hGammaSwap (W x) (e i)]
      _ = inner ℝ (G x (connectionVector (G x) P (e i) (W x))) (e j) +
            inner ℝ (G x (e i)) (connectionVector (G x) P (e j) (W x)) := by
          rw [hconvA, hconvB]
          ring
  have hmetricLeft (v : E3) :
      inner ℝ (G x v) (e j) =
        ∑ k : Fin 3, (G x (e k)) j * v k := by
    calc
      inner ℝ (G x v) (e j) = inner ℝ v (G x (e j)) := hAsym v (e j)
      _ = inner ℝ (∑ k : Fin 3, v k • e k) (G x (e j)) :=
        congrArg (fun z : E3 => inner ℝ z (G x (e j))) (hexpand v)
      _ = ∑ k : Fin 3, inner ℝ (v k • e k) (G x (e j)) := by rw [sum_inner]
      _ = ∑ k : Fin 3, v k * (G x (e j)) k := by
        simp [e, real_inner_smul_left, EuclideanSpace.inner_single_left]
      _ = ∑ k : Fin 3, (G x (e k)) j * v k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← hGcoord k j]
        ring
  have hmetricRight (v : E3) :
      inner ℝ (G x (e i)) v =
        ∑ k : Fin 3, (G x (e k)) i * v k := by
    calc
      inner ℝ (G x (e i)) v =
          inner ℝ (G x (e i)) (∑ k : Fin 3, v k • e k) :=
        congrArg (fun z : E3 => inner ℝ (G x (e i)) z) (hexpand v)
      _ = ∑ k : Fin 3, inner ℝ (G x (e i)) (v k • e k) := by rw [inner_sum]
      _ = ∑ k : Fin 3, v k * (G x (e i)) k := by
        simp [e, real_inner_smul_right, EuclideanSpace.inner_single_right]
      _ = ∑ k : Fin 3, (G x (e k)) i * v k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [← hGcoord i k]
        ring
  have hmetricLeftCoord (v : E3) :
      inner ℝ (G x v) (EuclideanSpace.single j 1) =
        ∑ k : Fin 3, (G x (EuclideanSpace.single k 1)) j * v k := by
    simpa [e] using hmetricLeft v
  have hmetricRightCoord (v : E3) :
      inner ℝ (G x (EuclideanSpace.single i 1)) v =
        ∑ k : Fin 3, (G x (EuclideanSpace.single k 1)) i * v k := by
    simpa [e] using hmetricRight v
  change coordinateLieMetricExpr G W x i j =
    inner ℝ (G x (fderiv ℝ W x (e i) +
      connectionVector (G x) P (e i) (W x))) (e j) +
    inner ℝ (G x (e i)) (fderiv ℝ W x (e j) +
      connectionVector (G x) P (e j) (W x))
  dsimp [coordinateLieMetricExpr]
  rw [hderivConn]
  rw [Finset.sum_add_distrib]
  rw [← hmetricLeftCoord (fderiv ℝ W x (EuclideanSpace.single i 1)),
    ← hmetricRightCoord (fderiv ℝ W x (EuclideanSpace.single j 1))]
  simp only [map_add, inner_add_left, inner_add_right]
  ring
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
