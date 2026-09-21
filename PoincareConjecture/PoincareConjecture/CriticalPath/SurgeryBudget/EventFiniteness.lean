import PoincareConjecture.CriticalPath.SurgeryBudget.TraceCount
import PoincareConjecture.CriticalPath.SurgeryBudget.FiniteSubset

namespace PoincareConjecture.CriticalPath.SurgeryBudget

/-- Quantitative budget data on every finite sample proves finiteness without assuming
local finiteness. Constructing those data from a geometric surgery flow is a separate task. -/
theorem finite_event_set_of_budget_traces
    (S : Set ℝ) (a T delta initialVolume : ℝ) (initialComponents : ℕ)
    (ha : 0 ≤ a) (hdelta : 0 < delta)
    (htraces : ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ S →
      Nonempty (BudgetTrace s.card a T delta initialVolume initialComponents)) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (initialComponents : ℝ) +
      2 * (Real.exp (a * T) * initialVolume / delta) := by
  apply finite_of_uniform_finite_subset_real_bound
  intro s hs
  obtain ⟨b⟩ := htraces s hs
  exact b.event_count_le ha hdelta

/-- Uniform positive loss and bounded-horizon growth exclude arbitrarily long event chains. -/
theorem no_infinite_budget_trace_chain
    (a T delta initialVolume : ℝ) (initialComponents : ℕ)
    (ha : 0 ≤ a) (hdelta : 0 < delta)
    (htraces : ∀ n : ℕ, Nonempty (BudgetTrace n a T delta initialVolume initialComponents)) :
    False := by
  obtain ⟨n, hn⟩ := exists_nat_gt
    ((initialComponents : ℝ) + 2 * (Real.exp (a * T) * initialVolume / delta))
  obtain ⟨b⟩ := htraces n
  exact (not_le_of_gt hn) (b.event_count_le ha hdelta)

/-- Three-dimensional numerical specialization: scalar lower bound -6 and
loss cVol*hmin^3 per cut. The geometric lower scale and volume-loss estimates are inputs. -/
theorem finite_event_set_of_three_dimensional_budget
    (S : Set ℝ) (T cVol hmin initialVolume : ℝ) (initialComponents : ℕ)
    (hcVol : 0 < cVol) (hhmin : 0 < hmin)
    (htraces : ∀ s : Finset ℝ, (↑s : Set ℝ) ⊆ S →
      Nonempty (BudgetTrace s.card 6 T (cVol * hmin ^ 3) initialVolume initialComponents)) :
    S.Finite ∧ (S.ncard : ℝ) ≤ (initialComponents : ℝ) +
      2 * (Real.exp (6 * T) * initialVolume / (cVol * hmin ^ 3)) := by
  exact finite_event_set_of_budget_traces S 6 T (cVol * hmin ^ 3) initialVolume
    initialComponents (by norm_num) (mul_pos hcVol (pow_pos hhmin 3)) htraces

end PoincareConjecture.CriticalPath.SurgeryBudget
