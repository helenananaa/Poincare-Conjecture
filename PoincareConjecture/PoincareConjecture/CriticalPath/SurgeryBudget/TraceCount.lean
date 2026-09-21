import PoincareConjecture.CriticalPath.SurgeryBudget.WeightedVolume
import PoincareConjecture.CriticalPath.SurgeryBudget.ComponentAccounting

open scoped BigOperators

namespace PoincareConjecture.CriticalPath.SurgeryBudget

/-- Numerical data for n surgery events on a bounded horizon. The volume recurrence and
component bookkeeping are explicit hypotheses to be supplied by actual geometry.
No result about Ricci-flow existence or event-count boundedness is stored in this structure. -/
structure BudgetTrace (n : ℕ) (a T delta initialVolume : ℝ) (initialComponents : ℕ) where
  time : ℕ → ℝ
  volume : ℕ → ℝ
  cuts : ℕ → ℕ
  discards : ℕ → ℕ
  components : ℕ → ℕ
  time_zero : time 0 = 0
  volume_zero : volume 0 = initialVolume
  components_zero : components 0 = initialComponents
  horizon : ∀ i ≤ n, time i ≤ T
  volume_nonneg : ∀ i ≤ n, 0 ≤ volume i
  volume_step : ∀ i < n, volume (i + 1) ≤
    Real.exp (a * (time (i + 1) - time i)) * volume i - delta * (cuts i : ℝ)
  component_step : ∀ i < n, components (i + 1) + discards i ≤ components i + cuts i
  event_active : ∀ i < n, 1 ≤ cuts i + discards i

/-- A quantitative bounded-horizon event estimate from volume and component data. -/
theorem BudgetTrace.event_count_le
    {n initialComponents : ℕ} {a T delta initialVolume : ℝ}
    (b : BudgetTrace n a T delta initialVolume initialComponents)
    (ha : 0 ≤ a) (hdelta : 0 < delta) :
    (n : ℝ) ≤ (initialComponents : ℝ) +
      2 * (Real.exp (a * T) * initialVolume / delta) := by
/- SWARM_PROOF_BEGIN -/
  have hcuts := weighted_cut_budget n a T delta b.time b.volume b.cuts ha hdelta
    b.time_zero b.horizon b.volume_nonneg b.volume_step
  have hevents := event_count_le_components_and_cuts n initialComponents b.components
    b.cuts b.discards b.components_zero b.component_step b.event_active
  have hevents' : (n : ℝ) ≤ (initialComponents : ℝ) +
      2 * ((∑ i ∈ Finset.range n, b.cuts i : ℕ) : ℝ) := by
    exact_mod_cast hevents
  have hcuts' : ((∑ i ∈ Finset.range n, b.cuts i : ℕ) : ℝ) ≤
      Real.exp (a * T) * initialVolume / delta := by
    apply (le_div_iff₀ hdelta).2
    simpa [b.volume_zero, mul_comm] using hcuts
  nlinarith [hevents', hcuts']
/- SWARM_PROOF_END -/

end PoincareConjecture.CriticalPath.SurgeryBudget
