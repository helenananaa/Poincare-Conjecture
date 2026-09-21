import PoincareConjecture.CriticalPath.SurgeryBudget.MeasuredHistory
import Lean

open PoincareConjecture.CriticalPath.SurgeryBudget
open Set MeasureTheory Function
open scoped ENNReal NNReal

/-- A nonempty finite slice with a prescribed integer mass. -/
noncomputable def unitMassSlice (n : ℕ) : MeasuredSlice where
  carrier := Unit
  measurable := ⊤
  measure := (n : ℝ≥0) • Measure.dirac ()
  finite := by infer_instance

theorem unitMassSlice_volume (n : ℕ) : (unitMassSlice n).volume = n := by
  change (((n : ℝ≥0) • Measure.dirac ()) Set.univ).toReal = (n : ℝ)
  rw [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ ())]
  simp

/-- One genuine nonzero replacement: mass 3 is reduced to mass 2. -/
example : ∃ r : MeasuredReplacement (unitMassSlice 3) (unitMassSlice 2) 1,
    ∀ j : Fin 1,
      1 + ((unitMassSlice 2).measure (r.new (some j))).toReal ≤
        ((unitMassSlice 3).measure (r.old (some j))).toReal := by
  let pieces : Option (Fin 1) → Set Unit := fun i ↦
    match i with | none => ∅ | some _ => Set.univ
  have hmeas : ∀ i, MeasurableSet (pieces i) := by
    intro i
    cases i <;> simp [pieces]
  have hdisj : Pairwise (Disjoint on pieces) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [pieces, Function.onFun]
  have hcover : (⋃ i, pieces i) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨some 0, Set.mem_univ x⟩
  refine ⟨{
    old := pieces
    new := pieces
    old_measurable := hmeas
    new_measurable := hmeas
    old_disjoint := hdisj
    new_disjoint := hdisj
    old_cover := hcover
    new_cover := hcover
    core_nonincrease := by
      change ((unitMassSlice 2).measure ∅).toReal ≤ ((unitMassSlice 3).measure ∅).toReal
      rw [measure_empty, measure_empty] }, ?_⟩
  intro j
  change 1 + (unitMassSlice 2).volume ≤ (unitMassSlice 3).volume
  rw [unitMassSlice_volume, unitMassSlice_volume]
  norm_num

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``MeasuredSlice.volume_nonneg,
    ``MeasuredReplacement.total_loss,
    ``MeasuredSurgeryHistory.toBudgetTrace,
    ``MeasuredSurgeryHistory.event_count_le,
    ``finite_event_set_of_measured_histories]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in names do
    unless (← getEnv).contains name do throwError "Missing theorem: {name}"
    let axioms ← Lean.collectAxioms name
    unless (axioms.filter (fun a ↦ !allowed.contains a)).isEmpty do
      throwError "Unexpected axioms: {name}: {axioms}"
    logInfo m!"PASS {name}: {axioms}"
  logInfo m!"MEASURED_SURGERY_HISTORY_GUARD_PASS {names.size}"
