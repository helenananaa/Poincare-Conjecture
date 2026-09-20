import LeeSmoothLib.Ch08.Sec08_62.NilpotentPBWWeightedBridge

universe uK uL

namespace LeeNilpotentPBWWeightedBridge

/-- Every finite-dimensional nilpotent Lie algebra over a characteristic-zero field has a
finite-dimensional faithful representation by nilpotent endomorphisms. Both the ordered PBW
basis and the high-weight rewrite are supplied by proved theorems, not extra assumptions.
This is the nilpotent case; it does not assert the remaining general Ado extension theorem. -/
theorem existsFaithfulFiniteDimensionalNilpotentRepresentation
    (K : Type uK) [Field K] [CharZero K]
    (L : Type uL) [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
    [LieRing.IsNilpotent L] :
    ∃ (V : Type (max uK uL)) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (_ : LieRingModule L V) (_ : LieModule K L V),
        LieModule.IsFaithful K L V ∧
          ∀ x : L, IsNilpotent (LieModule.toEnd K L V x) := by
  exact existsFaithfulFiniteDimensional_of_nilpotent_of_PBW K L
    (realPBW_hasOrderedPBWBasis K L)

end LeeNilpotentPBWWeightedBridge
