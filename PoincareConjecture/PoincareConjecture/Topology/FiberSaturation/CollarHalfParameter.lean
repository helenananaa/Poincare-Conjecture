import PoincareConjecture.Topology.FiberSaturation.OneSidedCollar
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- Include the normalized half-open collar parameter in the full open interval. -/
def halfCollarParameter (t : Ico (0 : ℝ) 1) : NeckParameter :=
  ⟨(t : ℝ), ⟨lt_of_lt_of_le (by norm_num) t.property.1, t.property.2⟩⟩

/-- Normalized nonnegative collar coordinates keep the actual product/subspace topology. -/
theorem exists_halfCollar_parameter_homeomorph
    {X : Type*} [TopologicalSpace X] :
    ∃ e : (X × Ico (0 : ℝ) 1) ≃ₜ {z : X × NeckParameter // 0 ≤ (z.2 : ℝ)},
      ∀ z, (e z : X × NeckParameter) = (z.1, halfCollarParameter z.2) :=
/- SWARM_PROOF_BEGIN -/
by
  let e : (X × Ico (0 : ℝ) 1) ≃ₜ {z : X × NeckParameter // 0 ≤ (z.2 : ℝ)} :=
  { toFun := fun z => ⟨(z.1, halfCollarParameter z.2), z.2.property.1⟩
    invFun := fun z =>
      (z.1.1, ⟨(z.1.2 : ℝ), ⟨z.2, z.1.2.property.2⟩⟩)
    left_inv := fun z => Prod.ext rfl (Subtype.ext rfl)
    right_inv := fun z => Subtype.ext (Prod.ext rfl (Subtype.ext rfl))
    continuous_toFun :=
      (continuous_fst.prodMk
        ((continuous_subtype_val.subtype_mk _).comp continuous_snd)).subtype_mk _
    continuous_invFun :=
      (continuous_subtype_val.fst.prodMk
        ((continuous_subtype_val.comp
            (continuous_snd.comp continuous_subtype_val)).subtype_mk _)) }
  exact ⟨e, fun _ => rfl⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation
