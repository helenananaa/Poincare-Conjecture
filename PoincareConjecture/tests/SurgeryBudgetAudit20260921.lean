import PoincareConjecture.CriticalPath.SurgeryBudget.EventFiniteness
import PoincareConjecture
import Lean

open Lean Elab Command in
run_cmd do
  let names : Array Name := #[
    ``PoincareConjecture.CriticalPath.SurgeryBudget.weighted_cut_budget,
    ``PoincareConjecture.CriticalPath.SurgeryBudget.event_count_le_components_and_cuts,
    ``PoincareConjecture.CriticalPath.SurgeryBudget.finite_of_uniform_finite_subset_real_bound,
    ``PoincareConjecture.CriticalPath.SurgeryBudget.BudgetTrace.event_count_le,
    ``PoincareConjecture.CriticalPath.SurgeryBudget.finite_event_set_of_budget_traces,
    ``PoincareConjecture.CriticalPath.SurgeryBudget.no_infinite_budget_trace_chain,
    ``PoincareConjecture.CriticalPath.SurgeryBudget.finite_event_set_of_three_dimensional_budget]
  for n in names do
    unless (← getEnv).contains n do throwError "Missing target: {n}"
    let a ← Lean.collectAxioms n
    unless (a.filter (fun x ↦ !(#[``propext, ``Classical.choice, ``Quot.sound]).contains x)).isEmpty do
      throwError "Unaccepted axioms: {n}: {a}"
    logInfo m!"PASS {n}: {a}"
  logInfo m!"SURGERY_BUDGET_GUARD_PASS {names.size}"

open PoincareConjecture.CriticalPath.SurgeryBudget in
example : Nonempty (BudgetTrace 2 0 2 1 3 1) := by
  refine ⟨{
    time := fun i ↦ (i : ℝ)
    volume := fun i ↦ 3 - (i : ℝ)
    cuts := fun _ ↦ 1
    discards := fun _ ↦ 0
    components := fun _ ↦ 1
    time_zero := by norm_num
    volume_zero := by norm_num
    components_zero := rfl
    horizon := by intro i hi; exact_mod_cast hi
    volume_nonneg := by
      intro i hi
      have h : (i : ℝ) ≤ 2 := by exact_mod_cast hi
      linarith
    volume_step := by intro i hi; norm_num [Nat.cast_add] <;> linarith
    component_step := by intro i hi; norm_num
    event_active := by intro i hi; norm_num
  }⟩
