import Mathlib
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** linear hessian contraction. -/
theorem linear_hessian_contraction (B : E3 →L[ℝ] E3) (H : E3 →L[ℝ] E3 →L[ℝ] ℝ) :
    let e := fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ);
    (∑ k : Fin 3, H (B (e k)) (B (e k))) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (∑ k : Fin 3, (B (e k)) i * (B (e k)) j) * H (e i) (e j) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp
  let e : Fin 3 → E3 := fun i => EuclideanSpace.single i (1 : ℝ)
  have hdecomp (x : E3) : x = ∑ i : Fin 3, (x i) • e i := by
    simpa [e, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x).symm
  have hbilin (x y : E3) : H x y = ∑ i : Fin 3, ∑ j : Fin 3,
      x i * y j * H (e i) (e j) := by
    calc
      H x y = ∑ i : Fin 3, (x i) • H (e i) y := by
        rw [hdecomp x]
        simp only [map_sum, map_smul]
        simp [e, Pi.single_apply]
      _ = ∑ i : Fin 3, x i * (∑ j : Fin 3, y j * H (e i) (e j)) := by
        congr 1
        funext i
        rw [hdecomp y]
        simp only [map_sum, map_smul, smul_eq_mul]
        simp [e, Pi.single_apply]
      _ = ∑ i : Fin 3, ∑ j : Fin 3, x i * y j * H (e i) (e j) := by
        simp_rw [Finset.mul_sum, mul_assoc]
  calc
    (∑ k : Fin 3, H (B (e k)) (B (e k))) =
        ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3,
          (B (e k)) i * (B (e k)) j * H (e i) (e j) := by
            apply Finset.sum_congr rfl
            intro k _
            exact hbilin (B (e k)) (B (e k))
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ k : Fin 3, (B (e k)) i * (B (e k)) j) * H (e i) (e j) := by
            rw [Finset.sum_comm]
            congr 1
            funext i
            rw [Finset.sum_comm]
            congr 1
            funext j
            rw [← Finset.sum_mul]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
