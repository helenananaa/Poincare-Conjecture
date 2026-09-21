import PoincareConjecture.CriticalPath.SurgeryBudget.MeasuredPieces
import PoincareConjecture.CriticalPath.SurgeryBudget.TraceCount
import PoincareConjecture.CriticalPath.SurgeryBudget.FiniteSubset

open Set MeasureTheory
open scoped BigOperators

namespace PoincareConjecture.CriticalPath.SurgeryBudget

universe u

/-- A finite piecewise history expressed with actual finite measures on changing
spaces. Smooth-stage growth and local replacement losses are separate inputs.
The total volume recurrence is not a field: it is proved from those inputs. -/
structure MeasuredSurgeryHistory (n : ℕ) (a T delta initialVolume : ℝ)
    (initialComponents : ℕ) where
  pre : ℕ → MeasuredSlice.{u}
  post : ℕ → MeasuredSlice.{u}
  time : ℕ → ℝ
  cuts : ℕ → ℕ
  discards : ℕ → ℕ
  components : ℕ → ℕ
  time_zero : time 0 = 0
  time_mono : Monotone time
  horizon : ∀ i ≤ n, time i ≤ T
  initial_volume : (post 0).volume = initialVolume
  initial_components : components 0 = initialComponents
  smooth_growth : ∀ i < n, (pre i).volume ≤
    Real.exp (a * (time (i + 1) - time i)) * (post i).volume
  replacement : ∀ i < n, MeasuredReplacement (pre i) (post (i + 1)) (cuts i)
  local_loss : ∀ i (hi : i < n) (j : Fin (cuts i)),
    delta + ((post (i + 1)).measure ((replacement i hi).new (some j))).toReal ≤
      ((pre i).measure ((replacement i hi).old (some j))).toReal
  component_step : ∀ i < n, components (i + 1) + discards i ≤ components i + cuts i
  event_active : ∀ i < n, 1 ≤ cuts i + discards i

/-- Assemble the numerical budget from measured local pieces. -/
noncomputable def MeasuredSurgeryHistory.toBudgetTrace
    {n initialComponents : ℕ} {a T delta initialVolume : ℝ}
    (h : MeasuredSurgeryHistory.{u} n a T delta initialVolume initialComponents) :
    BudgetTrace n a T delta initialVolume initialComponents where
  time := h.time
  volume := fun i ↦ (h.post i).volume
  cuts := h.cuts
  discards := h.discards
  components := h.components
  time_zero := h.time_zero
  volume_zero := h.initial_volume
  components_zero := h.initial_components
  horizon := h.horizon
  volume_nonneg := fun i _ ↦ (h.post i).volume_nonneg
  volume_step := by
    intro i hi
    have hl := (h.replacement i hi).total_loss (h.local_loss i hi)
    have hg := h.smooth_growth i hi
    linarith
  component_step := h.component_step
  event_active := h.event_active

/-- The count estimate for a measured history, not a pre-assumed numerical trace. -/
theorem MeasuredSurgeryHistory.event_count_le
    {n initialComponents : ℕ} {a T delta initialVolume : ℝ}
    (h : MeasuredSurgeryHistory.{u} n a T delta initialVolume initialComponents)
    (ha : 0 ≤ a) (hdelta : 0 < delta) :
    (n : ℝ) ≤ (initialComponents : ℝ) +
      2 * (Real.exp (a * T) * initialVolume / delta) :=
  h.toBudgetTrace.event_count_le ha hdelta

/-- No local-finiteness assumption: every finite sample is covered by a measured
history on the same bounded horizon. The histories must still be supplied by geometry. -/
theorem finite_event_set_of_measured_histories
    {Event : Type*} (events : Set Event)
    {a T delta initialVolume : ℝ} {initialComponents : ℕ}
    (ha : 0 ≤ a) (hdelta : 0 < delta)
    (hcover : ∀ s : Finset Event, (↑s : Set Event) ⊆ events →
      ∃ n : ℕ, s.card ≤ n ∧
        Nonempty (MeasuredSurgeryHistory.{u} n a T delta initialVolume initialComponents)) :
    events.Finite ∧ (events.ncard : ℝ) ≤ (initialComponents : ℝ) +
      2 * (Real.exp (a * T) * initialVolume / delta) := by
  apply finite_of_uniform_finite_subset_real_bound
  intro s hs
  obtain ⟨n, hcard, ⟨h⟩⟩ := hcover s hs
  have hcard' : (s.card : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcard
  exact hcard'.trans (h.event_count_le ha hdelta)

end PoincareConjecture.CriticalPath.SurgeryBudget
