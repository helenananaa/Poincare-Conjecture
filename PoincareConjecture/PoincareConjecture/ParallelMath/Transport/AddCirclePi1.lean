import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.ZMultiples

set_option autoImplicit false
noncomputable section

namespace PoincareConjecture.ParallelMath.Transport

/-- Mathlib covering of the additive circle: `π₁(ℝ/Tℤ) ≅ ℤ`. Primary package
only; does not import Hatcher. -/
theorem addCircle_fundamentalGroup_equiv_int
    (T : ℝ) (hT : 0 < T) (x : AddCircle T) :
    Nonempty (FundamentalGroup (AddCircle T) x ≃* Multiplicative ℤ) :=
/- SWARM_PROOF_BEGIN -/
by
  let cov : IsAddQuotientCoveringMap ((↑) : ℝ → AddCircle T) (AddSubgroup.zmultiples T) :=
    AddCircle.isAddQuotientCoveringMap_coe T
  obtain ⟨t, ht⟩ := cov.surjective x
  let e : ((↑) : ℝ → AddCircle T) ⁻¹' {x} := ⟨t, ht⟩
  let φ :
      FundamentalGroup (AddCircle T) x ≃*
        (Multiplicative (AddSubgroup.zmultiples T))ᵐᵒᵖ :=
    cov.fundamentalGroupEquiv e
  have hinj : Function.Injective (zmultiplesHom ℝ T) := by
    intro n m hnm
    have hmul : (n : ℝ) * T = (m : ℝ) * T := by
      simpa [zmultiplesHom_apply, zsmul_eq_mul] using hnm
    exact Int.cast_injective (mul_right_cancel₀ (ne_of_gt hT) hmul)
  let eZ : ℤ ≃+ AddSubgroup.zmultiples T := AddMonoidHom.ofInjective hinj
  exact ⟨φ.trans MulOpposite.opMulEquiv.symm |>.trans (AddEquiv.toMultiplicative eZ).symm⟩
/- SWARM_PROOF_END -/

end PoincareConjecture.ParallelMath.Transport
