import Mathlib

open Set MeasureTheory Function
open scoped BigOperators ENNReal

namespace PoincareConjecture.CriticalPath.SurgeryBudget

universe u

/-- A finite measured slice. The underlying space may change at a surgery. -/
structure MeasuredSlice where
  carrier : Type u
  measurable : MeasurableSpace carrier
  measure : @Measure carrier measurable
  finite : @IsFiniteMeasure carrier measurable measure

instance : CoeSort MeasuredSlice (Type u) := ⟨MeasuredSlice.carrier⟩
instance (X : MeasuredSlice) : MeasurableSpace X := X.measurable
instance (X : MeasuredSlice) : IsFiniteMeasure X.measure := X.finite

noncomputable def MeasuredSlice.volume (X : MeasuredSlice) : ℝ :=
  (X.measure Set.univ).toReal

theorem MeasuredSlice.volume_nonneg (X : MeasuredSlice) : 0 ≤ X.volume :=
  ENNReal.toReal_nonneg

/-- Disjoint measurable pieces before and after replacement. `none` is the
surviving core; `some j` pairs an old cutting region with its inserted cap.
The two slices need not have the same underlying topological space. -/
structure MeasuredReplacement (X Y : MeasuredSlice.{u}) (k : ℕ) where
  old : Option (Fin k) → Set X
  new : Option (Fin k) → Set Y
  old_measurable : ∀ i, MeasurableSet (old i)
  new_measurable : ∀ i, MeasurableSet (new i)
  old_disjoint : Pairwise (Disjoint on old)
  new_disjoint : Pairwise (Disjoint on new)
  old_cover : (⋃ i, old i) = Set.univ
  new_cover : (⋃ i, new i) = Set.univ
  core_nonincrease : (Y.measure (new none)).toReal ≤ (X.measure (old none)).toReal

/-- The total loss is derived from the disjoint pieces, not assumed.
Core volume is allowed to decrease, so discarded components cause no problem. -/
theorem MeasuredReplacement.total_loss
    {X Y : MeasuredSlice.{u}} {k : ℕ} (r : MeasuredReplacement X Y k)
    {delta : ℝ}
    (hlocal : ∀ j : Fin k,
      delta + (Y.measure (r.new (some j))).toReal ≤
        (X.measure (r.old (some j))).toReal) :
    delta * (k : ℝ) + Y.volume ≤ X.volume := by
  have hx : X.volume = ∑ i : Option (Fin k), (X.measure (r.old i)).toReal := by
    unfold MeasuredSlice.volume
    rw [← r.old_cover, measure_iUnion r.old_disjoint r.old_measurable,
      ENNReal.tsum_toReal_eq (fun i ↦ measure_ne_top X.measure (r.old i))]
    simp
  have hy : Y.volume = ∑ i : Option (Fin k), (Y.measure (r.new i)).toReal := by
    unfold MeasuredSlice.volume
    rw [← r.new_cover, measure_iUnion r.new_disjoint r.new_measurable,
      ENNReal.tsum_toReal_eq (fun i ↦ measure_ne_top Y.measure (r.new i))]
    simp
  have hp := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hlocal j)
  rw [Finset.sum_add_distrib] at hp
  have hp' : delta * (k : ℝ) +
      (∑ j : Fin k, (Y.measure (r.new (some j))).toReal) ≤
        ∑ j : Fin k, (X.measure (r.old (some j))).toReal := by
    simpa [mul_comm] using hp
  rw [hx, hy, Fintype.sum_option, Fintype.sum_option]
  linarith [r.core_nonincrease]

end PoincareConjecture.CriticalPath.SurgeryBudget
