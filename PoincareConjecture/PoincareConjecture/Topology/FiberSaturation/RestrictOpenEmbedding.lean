import Mathlib

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation
open Set

/-- An open embedding restricts to exact coordinates on an open patch of any subspace.
All subspaces retain their original induced topologies. -/
theorem openEmbedding_restrict_set_coordinates
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) (S : Set Y) :
    ∃ e : {a : X // f a ∈ S} ≃ₜ {y : S // (y : Y) ∈ range f},
      (∀ a, ((e a).1 : Y) = f a.1) ∧
      IsOpen {y : S | (y : Y) ∈ range f} :=
/- SWARM_PROOF_BEGIN -/
by
  let eRange : X ≃ₜ range f := hf.toIsEmbedding.toHomeomorph
  let eRestr : {a : X // f a ∈ S} ≃ₜ {y : range f // (y : Y) ∈ S} :=
    eRange.subtype fun a => Iff.of_eq <| congrArg (· ∈ S) <|
      (show (eRange a : Y) = f a from rfl).symm
  let eSwap : {y : range f // (y : Y) ∈ S} ≃ₜ {y : S // (y : Y) ∈ range f} :=
    { toFun := fun y => ⟨⟨y.1, y.2⟩, y.1.2⟩
      invFun := fun y => ⟨⟨y.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
      continuous_invFun :=
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _ }
  refine ⟨eRestr.trans eSwap, fun a => rfl, ?_⟩
  exact hf.isOpen_range.preimage continuous_subtype_val
/- SWARM_PROOF_END -/
end PoincareConjecture.Topology.FiberSaturation
