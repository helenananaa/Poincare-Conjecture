import Mathlib
import PoincareConjecture.ParallelImplementation.SymmetricSixPacking
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.PositiveOperatorPointNormalization
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_positive_operator_normalizer
    (M : E3 →L[ℝ] E3)
    (hsym : ∀ v w : E3, inner ℝ (M v) w = inner ℝ (M w) v)
    (hpos : ∀ v : E3, v ≠ 0 → 0 < inner ℝ (M v) v) :

    ∃ A : E3 ≃L[ℝ] E3, ∀ v w : E3,
      inner ℝ (M (A v)) (A w) = inner ℝ v w :=
/- SWARM_PROOF_BEGIN -/
by
  let T : E3 →ₗ[ℝ] E3 := M.toLinearMap
  have hT : T.IsSymmetric := by
    intro v w
    calc
      inner ℝ (T v) w = inner ℝ (M v) w := rfl
      _ = inner ℝ (M w) v := hsym v w
      _ = inner ℝ v (M w) := real_inner_comm _ _
      _ = inner ℝ v (T w) := rfl
  have hn : Module.finrank ℝ E3 = 3 := by simp
  let b := hT.eigenvectorBasis hn
  have heig (i : Fin 3) : 0 < hT.eigenvalues hn i := by
    have hbi : b i ≠ 0 := by
      intro hi
      have hnorm : ‖b i‖ = 1 := b.norm_eq_one i
      rw [hi, norm_zero] at hnorm
      norm_num at hnorm
    have hval : inner ℝ (M (b i)) (b i) = hT.eigenvalues hn i := by
      change inner ℝ (T (b i)) (b i) = hT.eigenvalues hn i
      rw [hT.apply_eigenvectorBasis hn i]
      simp [b, real_inner_smul_left]
    have hposbi := hpos (b i) hbi
    rw [hval] at hposbi
    exact hposbi
  let c : Fin 3 → ℝ := fun i => (Real.sqrt (hT.eigenvalues hn i))⁻¹
  have hcpos (i : Fin 3) : 0 < c i := by
    dsimp [c]
    exact inv_pos.mpr (Real.sqrt_pos.2 (heig i))
  have hc (i : Fin 3) : c i ≠ 0 := (hcpos i).ne'
  have hcc (i : Fin 3) : hT.eigenvalues hn i * c i * c i = 1 := by
    dsimp [c]
    calc
      hT.eigenvalues hn i * (Real.sqrt (hT.eigenvalues hn i))⁻¹ *
          (Real.sqrt (hT.eigenvalues hn i))⁻¹ =
          hT.eigenvalues hn i /
            (Real.sqrt (hT.eigenvalues hn i) * Real.sqrt (hT.eigenvalues hn i)) := by ring
      _ = hT.eigenvalues hn i / hT.eigenvalues hn i := by
        rw [← sq, Real.sq_sqrt (le_of_lt (heig i))]
      _ = 1 := div_self (heig i).ne'
  let dcoord : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) :=
    LinearEquiv.piCongrRight fun i =>
      LinearEquiv.smulOfNeZero ℝ (M := ℝ) (c i) (hc i)
  let p : E3 ≃L[ℝ] (Fin 3 → ℝ) := PiLp.continuousLinearEquiv 2 ℝ fun _ : Fin 3 => ℝ
  let d : E3 ≃L[ℝ] E3 := p.trans (dcoord.toContinuousLinearEquiv.trans p.symm)
  let e : E3 ≃L[ℝ] E3 := b.repr.toContinuousLinearEquiv
  let A : E3 ≃L[ℝ] E3 := e.trans (d.trans e.symm)
  refine ⟨A, ?_⟩
  intro v w
  have hcoord (x : E3) (i : Fin 3) : b.repr (A x) i = c i * b.repr x i := by
    simp [A, e, d, p, dcoord, LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit]
  have hdiag (x : E3) (i : Fin 3) : b.repr (T x) i = hT.eigenvalues hn i * b.repr x i :=
    hT.eigenvectorBasis_apply_self_apply hn x i
  change inner ℝ (T (A v)) (A w) = inner ℝ v w
  rw [← b.repr.inner_map_map (T (A v)) (A w)]
  rw [← b.repr.inner_map_map v w]
  have hleft (i : Fin 3) : b.repr (T (A v)) i =
      hT.eigenvalues hn i * (c i * b.repr v i) := by
    rw [hdiag, hcoord]
  simp_rw [PiLp.inner_apply, hleft, hcoord, RCLike.inner_apply', conj_trivial]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    (hT.eigenvalues hn i * (c i * b.repr v i)) * (c i * b.repr w i) =
        (hT.eigenvalues hn i * c i * c i) * (b.repr v i * b.repr w i) := by ring
    _ = b.repr v i * b.repr w i := by rw [hcc i, one_mul]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.PositiveOperatorPointNormalization
