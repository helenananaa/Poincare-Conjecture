import Mathlib
set_option autoImplicit false
namespace SwarmAcceptance
open Set
theorem periodic_remainder_identity (f : ℝ → ℝ) (L t : ℝ)
    (h : Function.Periodic f L) : f (t - (⌊t / L⌋ : ℤ) * L) = f t :=
/- SWARM_PROOF_BEGIN -/
by
  -- Periodicity holds at every integer multiple of `L`; `⌊t / L⌋` is merely such an integer.
  simpa using h.sub_int_mul_eq (⌊t / L⌋)
/- SWARM_PROOF_END -/
end SwarmAcceptance
