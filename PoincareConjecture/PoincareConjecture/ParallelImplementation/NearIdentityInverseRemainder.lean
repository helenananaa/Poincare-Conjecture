import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.NearIdentityInverseRemainder
theorem inverse_second_order_remainder
    {A : Type*} [NormedRing A]
    (a c b d : A) (M : ℝ) (hM : 0 ≤ M)
    (hb : b*(1-a)=1) (hd : (1-c)*d=1)
    (hbN : ‖b‖ ≤ M) (hdN : ‖d‖ ≤ M) :
    d-b-b*(c-a)*b = b*(c-a)*b*(c-a)*d ∧
      ‖d-b-b*(c-a)*b‖ ≤ M^3*‖c-a‖^2 :=
/- SWARM_PROOF_BEGIN -/
by
  have hres : b * (c - a) * d = d - b := by
    calc
      b * (c - a) * d = b * ((1 - a) - (1 - c)) * d := by
        congr 2
        noncomm_ring
      _ = (b * (1 - a)) * d - b * ((1 - c) * d) := by
        noncomm_ring
      _ = d - b := by
        rw [hb, hd]
        simp
  have hid : d - b - b * (c - a) * b =
      b * (c - a) * b * (c - a) * d := by
    calc
      d - b - b * (c - a) * b = b * (c - a) * d - b * (c - a) * b := by
        rw [← hres]
      _ = b * (c - a) * (d - b) := by
        noncomm_ring
      _ = b * (c - a) * (b * (c - a) * d) := by
        rw [← hres]
      _ = b * (c - a) * b * (c - a) * d := by
        noncomm_ring
  refine ⟨hid, ?_⟩
  rw [hid]
  calc
    ‖b * (c - a) * b * (c - a) * d‖ ≤
        ‖b * (c - a) * b * (c - a)‖ * ‖d‖ := norm_mul_le _ _
    _ ≤ (‖b * (c - a) * b‖ * ‖c - a‖) * ‖d‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ ((‖b * (c - a)‖ * ‖b‖) * ‖c - a‖) * ‖d‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ (((‖b‖ * ‖c - a‖) * ‖b‖) * ‖c - a‖) * ‖d‖ := by
      gcongr
      exact norm_mul_le _ _
    _ ≤ (((M * ‖c - a‖) * M) * ‖c - a‖) * M := by
      gcongr
    _ = M ^ 3 * ‖c - a‖ ^ 2 := by ring
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.NearIdentityInverseRemainder
