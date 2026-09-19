import Mathlib
import PoincareConjecture.ParallelMath.Variational.Core
import PoincareConjecture.Topology.FiberSaturation.TorusShortStrip
import Mathlib.Topology.Covering.Quotient

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Transport
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ENNReal Manifold ContDiff

/-- **Math.** Every fiber is explicitly enumerated by deck iterates of one chosen lift. -/
theorem mappingTorus_fiber_equiv_integers {X : Type*} [TopologicalSpace X]
    (phi : X ≃ₜ X) (L : ℝ) (hL : 0 < L) (p : X × ℝ) :
    ∃ e : ℤ ≃ {q : X × ℝ //
      PoincareConjecture.Topology.FiberSaturation.MappingTorus.proj phi L q =
        PoincareConjecture.Topology.FiberSaturation.MappingTorus.proj phi L p},
      ∀ n : ℤ, (e n).1 =
        PoincareConjecture.Topology.FiberSaturation.MappingTorus.deck phi L n p :=
/- SWARM_PROOF_BEGIN -/
open PoincareConjecture.Topology.FiberSaturation.MappingTorus in
by
  let f : ℤ → {q : X × ℝ // proj phi L q = proj phi L p} :=
    fun n => ⟨deck phi L n p, proj_deck phi L n p⟩
  refine ⟨Equiv.ofBijective f ⟨?inj, ?surj⟩, fun _ => rfl⟩
  case inj =>
    intro n m hnm
    have hval : deck phi L n p = deck phi L m p := Subtype.ext_iff.mp hnm
    have hsnd : p.2 + (n : ℝ) * L = p.2 + (m : ℝ) * L := by
      simpa [deck] using congrArg Prod.snd hval
    have hmul : (n : ℝ) * L = (m : ℝ) * L := add_left_cancel hsnd
    exact Int.cast_injective (mul_right_cancel₀ (ne_of_gt hL) hmul)
  case surj =>
    intro q
    obtain ⟨n, hn⟩ := (proj_eq_iff phi L p q.1).mp q.2.symm
    exact ⟨n, Subtype.ext hn⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelMath.Transport
