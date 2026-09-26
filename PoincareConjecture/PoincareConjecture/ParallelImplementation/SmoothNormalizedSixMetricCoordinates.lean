import Mathlib
import PoincareConjecture.ParallelImplementation.SymmetricSixPacking
import PoincareConjecture.ParallelImplementation.PositiveOperatorPointNormalization
import PoincareConjecture.ParallelImplementation.FixedLinearMetricCongruence
import PoincareConjecture.ParallelImplementation.SymmetricOperatorSixEncoding
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothNormalizedSixMetricCoordinates
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_smooth_normalized_six_metric_coordinates
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i =
      ∑ j : Fin 3, MorganTianLib.MetricCoefficient.symmetricSixMatrix q i j*v j)
    (M : E3 → (E3 →L[ℝ] E3)) (hM : ContDiff ℝ ∞ M)
    (hsym : ∀ x v w : E3, inner ℝ (M x v) w = inner ℝ (M x w) v)
    (p : E3) (hpos : ∀ v : E3, v ≠ 0 → 0 < inner ℝ (M p v) v) :

    ∃ A : E3 ≃L[ℝ] E3, ∃ u : E3 → E6, ContDiff ℝ ∞ u ∧ u 0=0 ∧
      ∀ x v w : E3, inner ℝ ((1+E (u x)) v) w = inner ℝ (M (p+A x) (A v)) (A w) :=
/- SWARM_PROOF_BEGIN -/
by
  have hMp_sym : ∀ v w : E3,
      inner ℝ (M p v) w = inner ℝ (M p w) v := by
    intro v w
    exact hsym p v w
  obtain ⟨A, hA⟩ := PoincareConjecture.ParallelImplementation.PositiveOperatorPointNormalization.exists_positive_operator_normalizer
    (M p) hMp_sym hpos
  obtain ⟨C, _hCnorm, hC⟩ := PoincareConjecture.ParallelImplementation.FixedLinearMetricCongruence.exists_fixed_metric_congruence A
  obtain ⟨P, _hPnorm, hP⟩ := PoincareConjecture.ParallelImplementation.SymmetricOperatorSixEncoding.exists_symmetric_operator_six_encoding
  let N : E3 → (E3 →L[ℝ] E3) := fun x => C (M (p + A x)) - 1
  let u : E3 → E6 := fun x => P (N x)
  have hshift : ContDiff ℝ ∞ (fun x : E3 => p + A x) := by
    fun_prop
  have hMshift : ContDiff ℝ ∞ (fun x : E3 => M (p + A x)) :=
    hM.comp hshift
  have hCshift : ContDiff ℝ ∞ (fun x : E3 => C (M (p + A x))) := by
    exact ContDiff.continuousLinearMap_comp C hMshift
  have hN : ContDiff ℝ ∞ N := by
    dsimp [N]
    exact hCshift.sub contDiff_const
  have hu : ContDiff ℝ ∞ u := by
    dsimp [u]
    exact ContDiff.continuousLinearMap_comp P hN
  have hCbase : C (M p) = (1 : E3 →L[ℝ] E3) := by
    apply ContinuousLinearMap.ext
    intro v
    ext i
    have h := hC (M p) v (EuclideanSpace.single i 1)
    rw [hA v (EuclideanSpace.single i 1)] at h
    simpa [PiLp.inner_apply] using h
  have hNbase : N 0 = 0 := by
    dsimp [N]
    have hzero : p + A 0 = p := by simp
    rw [hzero, hCbase]
    simp
  have hu0 : u 0 = 0 := by
    dsimp [u]
    rw [hNbase]
    simp
  have hNsym (x : E3) : ∀ v w : E3,
      inner ℝ (N x v) w = inner ℝ (N x w) v := by
    intro v w
    change inner ℝ (C (M (p + A x)) v - v) w =
      inner ℝ (C (M (p + A x)) w - w) v
    calc
      inner ℝ (C (M (p + A x)) v - v) w =
          inner ℝ (M (p + A x) (A v)) (A w) - inner ℝ v w := by
        rw [inner_sub_left, hC]
      _ = inner ℝ (M (p + A x) (A w)) (A v) - inner ℝ w v := by
        rw [hsym (p + A x) (A v) (A w), real_inner_comm v w]
      _ = inner ℝ (C (M (p + A x)) w - w) v := by
        rw [inner_sub_left, hC]
  have hEncode (x : E3) : E (u x) = N x := by
    exact hP E hE (N x) (hNsym x)
  refine ⟨A, u, hu, hu0, ?_⟩
  intro x v w
  have hrealize : (1 : E3 →L[ℝ] E3) + E (u x) = C (M (p + A x)) := by
    rw [hEncode x]
    dsimp [N]
    abel
  rw [hrealize]
  exact hC (M (p + A x)) v w
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothNormalizedSixMetricCoordinates
