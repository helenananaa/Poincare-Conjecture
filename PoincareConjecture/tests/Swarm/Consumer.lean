import tests.Swarm.Transport
import tests.Swarm.Period
set_option autoImplicit false
namespace SwarmAcceptance
open Set
theorem combined_regression {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) (f : ℝ → ℝ) (L : ℝ)
    (hf : ContDiff ℝ ⊤ f) (hp : Function.Periodic f L) :
    e '' closure A = closure (e '' A) ∧
    ContDiff ℝ ⊤ (fun t : ℝ => f (t - (⌊t / L⌋ : ℤ) * L)) :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · exact transport_closure e A
  · have hfun : (fun t : ℝ => f (t - (⌊t / L⌋ : ℤ) * L)) = f := by
      funext t
      exact periodic_remainder_identity f L t hp
    rw [hfun]
    exact hf
/- SWARM_PROOF_END -/
end SwarmAcceptance
