import PoincareConjecture.ParallelImplementation.SixComponentHessianNorm
import PoincareConjecture.ParallelImplementation.DuhamelHessianOperatorSchauder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SixComponentDuhamelHessian
open MorganTianLib.ParabolicPDE Set MeasureTheory
open scoped Topology ContDiff BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Uniform joint space-time bounds for the actual vector-valued Duhamel Hessian. -/
theorem six_component_duhamel_hessian_schauder
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (ℝ × E3) →ᵇ E6) (H T : ℝ),
      0 ≤ H → 0 ≤ T →
      (∀ t ∈ Icc (0:ℝ) T, ∀ x y, ‖F (t,x)-F (t,y)‖ ≤ H*‖x-y‖^alpha) →
      let u : ℝ → E3 → E6 := fun t x => WithLp.toLp 2 (fun k : Fin 6 =>
        ∫ s in (0:ℝ)..t, ∫ y : E3, euclideanHeatKernel 3 (t-s) (x-y)*(F (s,y) k))
      (∀ t ∈ Icc (0:ℝ) T, ContDiff ℝ 2 (u t)) ∧
      (∀ t ∈ Icc (0:ℝ) T, ∀ x, ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C*H*t^(alpha/2)) ∧
      ∀ t ∈ Icc (0:ℝ) T, ∀ s ∈ Icc (0:ℝ) T, ∀ x y,
        ‖fderiv ℝ (fderiv ℝ (u t)) x-fderiv ℝ (fderiv ℝ (u s)) y‖ ≤
          C*H*(‖x-y‖^alpha+|t-s|^(alpha/2)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨C₀, hC₀, hscalar⟩ :=
    PoincareConjecture.ParallelImplementation.DuhamelHessianOperatorSchauder.actual_duhamel_hessian_operator_schauder
      alpha ha ha1
  let C : ℝ := 6 * C₀
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro F H T hH hT hholder
  let u : ℝ → E3 → E6 := fun t x => WithLp.toLp 2 (fun k : Fin 6 =>
    ∫ s in (0:ℝ)..t, ∫ y : E3,
      euclideanHeatKernel 3 (t-s) (x-y) * (F (s,y) k))
  have hcoordLipschitz (k : Fin 6) :
      LipschitzWith 1 (fun v : E6 => v k) := by
    refine LipschitzWith.of_dist_le_mul ?_
    intro v w
    calc
      dist (v k) (w k) = ‖(v-w) k‖ := by
        rw [dist_eq_norm]
        congr 1
      _ ≤ ‖v-w‖ := PiLp.norm_apply_le (v-w) k
      _ = 1 * dist v w := by simp [dist_eq_norm]
  let Fk : Fin 6 → (ℝ × E3) →ᵇ ℝ := fun k =>
    F.comp (fun v : E6 => v k) (hcoordLipschitz k)
  have hholderk (k : Fin 6) :
      ∀ r ∈ Icc (0:ℝ) T, ∀ x z : E3,
        |Fk k (r,x) - Fk k (r,z)| ≤ H * ‖x-z‖^alpha := by
    intro r hr x z
    calc
      |Fk k (r,x) - Fk k (r,z)| = ‖(F (r,x)-F (r,z)) k‖ := by
        simp [Fk, BoundedContinuousFunction.comp_apply, Real.norm_eq_abs]
      _ ≤ ‖F (r,x)-F (r,z)‖ := PiLp.norm_apply_le _ _
      _ ≤ H * ‖x-z‖^alpha := hholder r hr x z
  let uk (k : Fin 6) : ℝ → E3 → ℝ := fun t x =>
    ∫ s in (0:ℝ)..t, ∫ y : E3,
      euclideanHeatKernel 3 (t-s) (x-y) * Fk k (s,y)
  have hucoord (k : Fin 6) (t : ℝ) (x : E3) : u t x k = uk k t x := by
    simp [u, uk, Fk, BoundedContinuousFunction.comp_apply]
  have hucoord_fun (k : Fin 6) (t : ℝ) : (fun x : E3 => u t x k) = uk k t := by
    funext x
    exact hucoord k t x
  have hscalarResult (k : Fin 6) := hscalar (Fk k) H T hH hT (hholderk k)
  have hvectorC2 (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) : ContDiff ℝ 2 (u t) := by
    apply (contDiff_piLp (p := 2)).2
    intro k
    have hk := (hscalarResult k).1 t ht
    simpa only [hucoord_fun k t] using hk
  have hzeroC2 : ContDiff ℝ 2 (fun _ : E3 => (0 : E6)) := contDiff_const
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact hvectorC2 t ht
  · intro t ht x
    let D : ℝ := C₀ * H * t^(alpha/2)
    have hpow : 0 ≤ t^(alpha/2) := Real.rpow_nonneg ht.1 _
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hcomponents : ∀ k : Fin 6,
        ‖fderiv ℝ (fderiv ℝ (fun y : E3 => u t y k)) x -
          fderiv ℝ (fderiv ℝ (fun y : E3 => (0:E6) k)) x‖ ≤ D := by
      intro k
      have hk := (hscalarResult k).2.1 t ht x
      simpa [D, hucoord_fun k t] using hk
    have hbound :=
      PoincareConjecture.ParallelImplementation.SixComponentHessianNorm.six_component_hessian_norm_difference
        (u t) (fun _ : E3 => (0:E6)) (hvectorC2 t ht) hzeroC2 x x D hD hcomponents
    calc
      ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ 6 * D := by
        simpa using hbound
      _ = C * H * t^(alpha/2) := by dsimp [D, C]; ring
  · intro t ht s hs x y
    let D : ℝ := C₀ * H * (‖x-y‖^alpha + |t-s|^(alpha/2))
    have hspace : 0 ≤ ‖x-y‖^alpha := Real.rpow_nonneg (norm_nonneg _) _
    have htime : 0 ≤ |t-s|^(alpha/2) := Real.rpow_nonneg (abs_nonneg _) _
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hcomponents : ∀ k : Fin 6,
        ‖fderiv ℝ (fderiv ℝ (fun z : E3 => u t z k)) x -
          fderiv ℝ (fderiv ℝ (fun z : E3 => u s z k)) y‖ ≤ D := by
      intro k
      have hk := (hscalarResult k).2.2 t ht s hs x y
      simpa [D, hucoord_fun] using hk
    have hbound :=
      PoincareConjecture.ParallelImplementation.SixComponentHessianNorm.six_component_hessian_norm_difference
        (u t) (u s) (hvectorC2 t ht) (hvectorC2 s hs) x y D hD hcomponents
    calc
      ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u s)) y‖ ≤ 6 * D := hbound
      _ = C * H * (‖x-y‖^alpha + |t-s|^(alpha/2)) := by dsimp [D, C]; ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SixComponentDuhamelHessian
