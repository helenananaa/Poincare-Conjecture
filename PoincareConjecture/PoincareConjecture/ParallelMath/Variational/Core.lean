import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelMath.Variational
open Set
/-- Infimum of a fixed, explicitly supplied admissible cost family.
No minimizer or geometric width realization is assumed. -/
def leastCost {A : Type*} (f : A → ℝ) : ℝ := sInf (range f)
/-- Supremum over the parameters of one sweepout; boundedness is a theorem input. -/
def peakCost {B : Type*} (f : B → ℝ) : ℝ := sSup (range f)
/-- Infimum over sweepouts of their parameterwise supremum, on fixed admissible types. -/
def leastPeak {A B : Type*} (F : A → B → ℝ) : ℝ :=
  leastCost (fun a => peakCost (F a))
end PoincareConjecture.ParallelMath.Variational
