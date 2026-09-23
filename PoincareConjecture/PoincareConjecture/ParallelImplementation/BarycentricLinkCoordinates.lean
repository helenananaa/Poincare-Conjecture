import PoincareConjecture.ParallelImplementation.BarycentricMembership
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BarycentricLinkCoordinates
open PoincareConjecture.ParallelImplementation.FinitePLRealization
open scoped BigOperators
theorem normalized_vertex_deletion_in_link
    {V : Type*} [Fintype V] [DecidableEq V] (K : FiniteAbstractComplex V)
    (v : V) (hv : ({v} : Finset V) ∈ K.faces)
    (x : V → ℝ) (hx : x ∈ (realization K).space)
    (hxv : 0 < x v) (hxv1 : x v < 1) :
    let y : V → ℝ := fun w => if w = v then 0 else x w / (1 - x v)
    (∀ w, 0 ≤ y w) ∧ (∑ w, y w) = 1 ∧
      (Finset.univ.filter (fun w => 0 < y w)) ∈ (abstractLink K {v} hv).faces :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let y : V → ℝ := fun w => if w = v then 0 else x w / (1 - x v)
  change (∀ w, 0 ≤ y w) ∧ (∑ w, y w) = 1 ∧
    (Finset.univ.filter (fun w => 0 < y w)) ∈ (abstractLink K {v} hv).faces
  rcases (BarycentricMembership.mem_realization_iff_barycentric K x).mp hx with
    ⟨hxnonneg, hxsum, hxface⟩
  have hden : 0 < 1 - x v := by linarith
  have hy_nonneg : ∀ w, 0 ≤ y w := by
    intro w
    by_cases hw : w = v
    · simp [y, hw]
    · simp [y, hw, div_nonneg (hxnonneg w) (le_of_lt hden)]
  have hErase : (∑ w ∈ Finset.univ.erase v, x w) = 1 - x v := by
    have hsplit := Finset.univ.sum_erase_add x (Finset.mem_univ v)
    rw [hxsum] at hsplit
    linarith
  have hy_sum : (∑ w, y w) = (∑ w ∈ Finset.univ.erase v, x w) / (1 - x v) := by
    calc
      (∑ w, y w) = (∑ w ∈ Finset.univ.erase v, y w) + y v := by
        rw [← Finset.univ.sum_erase_add y (Finset.mem_univ v)]
      _ = (∑ w ∈ Finset.univ.erase v, x w / (1 - x v)) := by
        rw [show y v = 0 by simp [y]]
        simp only [add_zero]
        apply Finset.sum_congr rfl
        intro w hw
        have hwv : w ≠ v := (Finset.mem_erase.mp hw).1
        simp [y, hwv]
      _ = (∑ w ∈ Finset.univ.erase v, x w) / (1 - x v) := by
        rw [Finset.sum_div]
  have hysum : (∑ w, y w) = 1 := by
    rw [hy_sum, hErase]
    exact div_self (ne_of_gt hden)
  have hposy : 0 < y :=
    (Fintype.sum_pos_iff_of_nonneg hy_nonneg).mp (by rw [hysum]; norm_num)
  have hex : ∃ w, 0 < y w := (Pi.lt_def.mp hposy).2
  rcases hex with ⟨w₀, hw₀⟩
  let S : Finset V := Finset.univ.filter (fun w => 0 < y w)
  let T : Finset V := Finset.univ.filter (fun w => 0 < x w)
  have hS_eq : S = T.erase v := by
    ext w
    simp only [S, T, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · intro hy
      have hwv : w ≠ v := by
        intro hwv
        subst w
        simp [y] at hy
      refine ⟨hwv, ?_⟩
      have hdiv : 0 < x w / (1 - x v) := by simpa [y, hwv] using hy
      exact (div_pos_iff_of_pos_right hden).mp hdiv
    · rintro ⟨hwv, hxw⟩
      have hdiv : 0 < x w / (1 - x v) := div_pos hxw hden
      simpa [y, hwv] using hdiv
  have hS_nonempty : S.Nonempty := by
    refine ⟨w₀, ?_⟩
    simp [S, hw₀]
  have hS_subset_T : S ⊆ T := by
    rw [hS_eq]
    exact Finset.erase_subset _ _
  have hS_disjoint : Disjoint S ({v} : Finset V) := by
    apply Finset.disjoint_left.mpr
    intro w hwS hwv
    have hwne : w ≠ v := by
      have : w ∈ T.erase v := by simpa [hS_eq] using hwS
      exact (Finset.mem_erase.mp this).1
    exact hwne (Finset.mem_singleton.mp hwv)
  have hUnion_subset : S ∪ {v} ⊆ T := by
    intro w hw
    rcases Finset.mem_union.mp hw with hwS | hwv
    · exact hS_subset_T hwS
    · have hwv' : w = v := Finset.mem_singleton.mp hwv
      subst w
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxv⟩
  have hUnion_nonempty : (S ∪ {v}).Nonempty := by
    exact ⟨v, Finset.mem_union.mpr (Or.inr (Finset.mem_singleton_self v))⟩
  have hUnion_face : S ∪ {v} ∈ K.faces :=
    (K.isRelLowerSet_faces hxface).2 hUnion_subset hUnion_nonempty
  refine ⟨hy_nonneg, hysum, ?_⟩
  change S.Nonempty ∧ Disjoint S ({v} : Finset V) ∧ S ∪ {v} ∈ K.faces
  exact ⟨hS_nonempty, hS_disjoint, hUnion_face⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BarycentricLinkCoordinates
