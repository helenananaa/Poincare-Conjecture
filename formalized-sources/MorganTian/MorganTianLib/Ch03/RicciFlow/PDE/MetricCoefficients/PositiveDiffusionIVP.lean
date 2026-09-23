import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PositiveDiffusionFactor
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConstantDiffusionIVP
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** positive diffusion local classical ivp. -/
theorem positive_diffusion_local_classical_ivp (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0<c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hsym : ∀ v w : E3, inner ℝ (A v) w=inner ℝ v (A w))
    (f : E3 →ᵇ ℝ) (hf : UniformContinuous f) :
    ∃ T : ℝ, 0<T ∧ ∃ u : (ℝ × E3) →ᵇ ℝ,
      (∀ x : E3, u (0,x)=f x) ∧ TendstoUniformly (fun t x => u (t,x)) f (𝓝[>] (0:ℝ)) ∧
      ∀ t ∈ Ioo (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => u (t,x)) ∧ ∀ x : E3,
        HasDerivAt (fun s : ℝ => u (s,x))
          (∑ i : Fin 3, ∑ j : Fin 3, A (EuclideanSpace.single j 1) i *
            fderiv ℝ (fun z : E3 => fderiv ℝ (fun w : E3 => u (t,w)) z
              (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)) t :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨B, hB⟩ := positive_diffusion_factor A c hc hA hsym
  obtain ⟨T, hT, u, hu0, htrace, hu⟩ :=
    constant_diffusion_local_classical_ivp B f hf
  refine ⟨T, hT, u, hu0, htrace, ?_⟩
  intro t ht
  obtain ⟨huC, huderiv⟩ := hu t ht
  refine ⟨huC, ?_⟩
  intro x
  let e : Fin 3 → E3 := fun k => EuclideanSpace.single k (1 : ℝ)
  have hexpand (v : E3) : v = ∑ k : Fin 3, v k • e k := by
    symm
    simpa [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have hAdjCoord (j k : Fin 3) :
      ((B.toContinuousLinearMap).adjoint (e j)) k = B (e k) j := by
    calc
      ((B.toContinuousLinearMap).adjoint (e j)) k =
          inner ℝ ((B.toContinuousLinearMap).adjoint (e j)) (e k) := by
        simp [e, EuclideanSpace.inner_single_right]
      _ = inner ℝ (e j) (B (e k)) :=
        (B.toContinuousLinearMap).adjoint_inner_left _ _
      _ = B (e k) j := by
        simp [e, EuclideanSpace.inner_single_left]
  have hBcoord (j i : Fin 3) :
      (B ((B.toContinuousLinearMap).adjoint (e j))) i =
        ∑ k : Fin 3, ((B.toContinuousLinearMap).adjoint (e j)) k * B (e k) i := by
    calc
      (B ((B.toContinuousLinearMap).adjoint (e j))) i =
          (B (∑ k : Fin 3, ((B.toContinuousLinearMap).adjoint (e j)) k • e k)) i := by
            rw [← hexpand ((B.toContinuousLinearMap).adjoint (e j))]
      _ = (∑ k : Fin 3, ((B.toContinuousLinearMap).adjoint (e j)) k • B (e k)) i := by
            simp only [map_sum, map_smul]
      _ = ∑ k : Fin 3, ((B.toContinuousLinearMap).adjoint (e j)) k * B (e k) i := by
            simp
  have hAapply (j : Fin 3) : A (e j) = B ((B.toContinuousLinearMap).adjoint (e j)) := by
    simpa [ContinuousLinearMap.comp_apply] using
      congrArg (fun L : E3 →L[ℝ] E3 => L (e j)) hB
  have hcoeff (i j : Fin 3) :
      (∑ k : Fin 3, B (e k) i * B (e k) j) = A (e j) i := by
    calc
      (∑ k : Fin 3, B (e k) i * B (e k) j) =
          ∑ k : Fin 3, ((B.toContinuousLinearMap).adjoint (e j)) k * B (e k) i := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [hAdjCoord]
            ring
      _ = (B ((B.toContinuousLinearMap).adjoint (e j))) i := (hBcoord j i).symm
      _ = A (e j) i := by rw [← hAapply j]
  have hsum :
      (∑ i : Fin 3, ∑ j : Fin 3,
        (∑ k : Fin 3, B (e k) i * B (e k) j) *
          fderiv ℝ (fun z : E3 => fderiv ℝ
            (fun w : E3 => u (t,w)) z (e j)) x (e i)) =
      ∑ i : Fin 3, ∑ j : Fin 3,
        A (e j) i * fderiv ℝ (fun z : E3 => fderiv ℝ
          (fun w : E3 => u (t,w)) z (e j)) x (e i) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoeff i j]
  rw [← hsum]
  exact huderiv x
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
