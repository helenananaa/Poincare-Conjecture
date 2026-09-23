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

/-- **Math.** positive diffusion factor. -/
theorem positive_diffusion_factor (A : E3 →L[ℝ] E3) (c : ℝ) (hc : 0 < c)
    (hA : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (A v) v)
    (hsym : ∀ v w : E3, inner ℝ (A v) w = inner ℝ v (A w)) :
    ∃ B : E3 ≃L[ℝ] E3,
      A = B.toContinuousLinearMap.comp B.toContinuousLinearMap.adjoint :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : PartialOrder (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.instPartialOrder
  letI : IsOrderedAddMonoid (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.instIsOrderedAddMonoid
  letI : NonnegSpectrumClass ℝ (Matrix (Fin 3) (Fin 3) ℝ) := Matrix.instNonnegSpectrumClass
  let eucCLM := Matrix.toEuclideanCLM (n := Fin 3) (𝕜 := ℝ)
  let M : Matrix (Fin 3) (Fin 3) ℝ := eucCLM.symm A
  have hM : eucCLM M = A := by
    simp [M]
  have hMlinear : (eucCLM M).toLinearMap = A.toLinearMap := by
    exact congrArg ContinuousLinearMap.toLinearMap hM
  have hMsym : M.toEuclideanLin.IsSymmetric := by
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    change (eucCLM M).toLinearMap.IsSymmetric
    rw [hMlinear]
    exact hsym
  have hMherm : M.IsHermitian :=
    (Matrix.isSymmetric_toEuclideanLin_iff).mp hMsym
  have hMpos : M.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hMherm, ?_⟩
    intro x hx
    let v : E3 := WithLp.toLp 2 x
    have hv : v ≠ 0 := by
      intro hv
      apply hx
      simpa [v] using congrArg WithLp.ofLp hv
    have hdot : inner ℝ (A v) v = star x ⬝ᵥ (M *ᵥ x) := by
      rw [hsym v v, ← hM]
      simpa [eucCLM, v] using (Matrix.inner_toEuclideanCLM M v v)
    have hcoercive := hA v
    rw [hdot] at hcoercive
    have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    exact lt_of_lt_of_le (mul_pos hc (sq_pos_of_pos hnorm)) hcoercive
  have hMnonneg : 0 ≤ M := hMpos.posSemidef.nonneg
  have hMqr : QuasispectrumRestricts M ContinuousMap.realToNNReal := by
    exact QuasispectrumRestricts.nnreal_of_nonneg hMnonneg
  obtain ⟨S, hSself, -, hSsq⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hMherm hMqr
  have hMunit : IsUnit M := hMpos.isUnit
  have hSunit : IsUnit S := by
    apply isUnit_mul_self_iff.mp
    rw [hSsq]
    exact hMunit
  have hSvecinj : Function.Injective (S.mulVec) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hSunit
  have hSinj : Function.Injective (eucCLM S : E3 →L[ℝ] E3) := by
    intro x y hxy
    apply WithLp.ofLp_injective 2
    apply hSvecinj
    simpa [eucCLM] using congrArg WithLp.ofLp hxy
  have hSsurj : Function.Surjective (eucCLM S).toLinearMap :=
    LinearMap.injective_iff_surjective.mp hSinj
  let e : E3 ≃ₗ[ℝ] E3 :=
    LinearEquiv.ofBijective (eucCLM S).toLinearMap ⟨hSinj, hSsurj⟩
  let B : E3 ≃L[ℝ] E3 := e.toContinuousLinearEquiv
  have hB : B.toContinuousLinearMap = eucCLM S := by
    ext v
    rfl
  refine ⟨B, ?_⟩
  rw [hB]
  calc
    A = eucCLM M := hM.symm
    _ = eucCLM (S * S) := congrArg eucCLM hSsq.symm
    _ = (eucCLM S).comp (eucCLM S).adjoint := by
      have hSadj : (eucCLM S).adjoint = eucCLM S := by
        calc
          _ = star (eucCLM S) := (ContinuousLinearMap.star_eq_adjoint _).symm
          _ = eucCLM (star S) := (eucCLM.map_star' S).symm
          _ = eucCLM S := congrArg eucCLM hSself.star_eq
      calc
        eucCLM (S * S) = eucCLM S * eucCLM S := eucCLM.map_mul S S
        _ = (eucCLM S).comp (eucCLM S) := by rw [ContinuousLinearMap.mul_def]
        _ = (eucCLM S).comp (eucCLM S).adjoint := by rw [hSadj]
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
