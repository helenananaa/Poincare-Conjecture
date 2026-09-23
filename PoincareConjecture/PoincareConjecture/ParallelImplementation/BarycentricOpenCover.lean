import PoincareConjecture.ParallelImplementation.BarycentricMembership
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BarycentricOpenCover
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators
theorem positive_coordinate_open_cover
    {V : Type*} [Fintype V] [DecidableEq V] (K : FiniteAbstractComplex V) :
    (∀ v : V, IsOpen {x : {x : V → ℝ // x ∈ (realization K).space} | 0 < x.1 v}) ∧
    (⋃ v : V, {x : {x : V → ℝ // x ∈ (realization K).space} | 0 < x.1 v}) = Set.univ :=
/- SWARM_PROOF_BEGIN -/
by
  constructor
  · intro v
    have hc : Continuous (fun x : {x : V → ℝ // x ∈ (realization K).space} => x.1 v) :=
      (continuous_apply v).comp continuous_subtype_val
    change IsOpen ((fun x : {x : V → ℝ // x ∈ (realization K).space} => x.1 v) ⁻¹'
      Set.Ioi (0 : ℝ))
    exact hc.isOpen_preimage (Set.Ioi (0 : ℝ)) isOpen_Ioi
  · ext x
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨hnonneg, hsum, _⟩ :=
      PoincareConjecture.ParallelImplementation.BarycentricMembership.mem_realization_iff_barycentric
        K x.1 |>.mp x.2
    have hpos : 0 < x.1 :=
      (Fintype.sum_pos_iff_of_nonneg hnonneg).mp (by rw [hsum]; norm_num)
    exact (Pi.lt_def.mp hpos).2
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BarycentricOpenCover
