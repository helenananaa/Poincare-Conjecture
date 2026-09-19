import ReferenceBridges.GlobalTransfer.Core
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open Set Riemannian Manifold
open PoincareConjecture.ParallelMath.Transfer
open scoped ContDiff Manifold ENNReal Bundle
/-- **Math.** Explicit standard plane bilinear form. -/
def planeForm : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun v w => v.1*w.1+v.2*w.2)
    (by intros; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (by intros; simp only [Prod.fst_add, Prod.snd_add]; ring)
    (by intros; simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
example : gramArea planeForm (1,0) (0,1) = 1 := by norm_num [gramArea, planeForm]
example : gramArea planeForm (2,0) (1,3) = 6 := by norm_num [gramArea, planeForm]
example : gramArea planeForm (2,0) (3,0) = 0 := by norm_num [gramArea, planeForm]
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (y : Y) :
    ¬ NonNull (ContinuousMap.const X y) := by
  intro h
  exact h ⟨y, ContinuousMap.Homotopic.refl _⟩
example : metricEDist (DCEuclideanMetric (F := ℝ)) (0 : ℝ) 0 = 0 := by
  letI : Bundle.RiemannianBundle (fun x : ℝ => TangentSpace 𝓘(ℝ,ℝ) x) :=
    ⟨(DCEuclideanMetric (F := ℝ)).toRiemannianMetric⟩
  exact Manifold.riemannianEDist_self
example (x : EuclideanSpace ℝ (Fin 2)) :
    paramAreaDensity (DCEuclideanMetric (F := EuclideanSpace ℝ (Fin 2))) id x = 1 := by
  unfold paramAreaDensity
  rw [mfderiv_id]
  change Real.sqrt ((inner ℝ (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) (EuclideanSpace.single 0 1)) *
      (inner ℝ (EuclideanSpace.single 1 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) (EuclideanSpace.single 1 1)) -
      (inner ℝ (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 2)) (EuclideanSpace.single 1 1))^2) = 1
  norm_num [EuclideanSpace.inner_single_left]

