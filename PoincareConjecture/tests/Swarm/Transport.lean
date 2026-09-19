import Mathlib
set_option autoImplicit false
namespace SwarmAcceptance
open Set
theorem transport_closure {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (A : Set X) : e '' closure A = closure (e '' A) :=
/- SWARM_PROOF_BEGIN -/
by
  exact e.image_closure A
/- SWARM_PROOF_END -/
end SwarmAcceptance
