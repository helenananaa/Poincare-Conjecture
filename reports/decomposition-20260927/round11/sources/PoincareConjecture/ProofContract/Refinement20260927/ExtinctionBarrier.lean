import PoincareConjecture.ProofContract.Refinement20260927.PatchGeometryBudget
import MorganTianLib.Ch02.ForwardDifference
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MorganTianLib
open scoped Topology
/-- **Math.** Integrating-factor potential for an upper Dini width inequality.
This real-valued expression is not itself a construction of geometric min-max width. -/
def widthPotential (a c t w : ℝ) : ℝ :=
  w / (t+c)^((3:ℝ)/4) + 4*a*(t+c)^((1:ℝ)/4)
/-- **Math.** Independent scalar-analysis leaf, with the actual one-sided
limsup bound, not a differentiability assumption on the unknown width. -/
def WidthIntervalComparisonStatement : Prop :=
  ∀ (a c s t : ℝ) (w : ℝ → ℝ), 0 < a → 0 < c → 0 ≤ s → s < t →
    ContinuousOn w (Icc s t) →
    (∀ r ∈ Ico s t, ForwardDiffQuotientLE w r (-a + 3/(4*(r+c))*w r)) →
    widthPotential a c t (w t) ≤ widthPotential a c s (w s)
/-- **Math.** Independent real-power growth leaf. Constants are fixed BEFORE
choosing a horizon, so this does not assume a sufficiently late empty state. -/
def WidthHorizonStatement : Prop :=
  ∀ a c w0 : ℝ, 0 < a → 0 < c → 0 ≤ w0 →
    ∃ T : ℝ, 0 < T ∧ widthPotential a c 0 w0 < 4*a*(T+c)^((1:ℝ)/4)
/-- **Math.** Analytic extinction certificate along the SAME event times.
The geometric construction of width and its surgery behavior remains research.
Different continuous profiles on event-free intervals must meet the same endpoints. -/
structure ExtinctionProfile (a c w0 T : ℝ) (events : Set ℝ) where
  pre : ℝ → ℝ
  post : ℝ → ℝ
  initial : post 0 ≤ w0
  terminal_nonneg : 0 ≤ pre T
  jumps : ∀ t ∈ events, post t ≤ pre t
  intervals : ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → events ∩ Ioo s t = ∅ →
    ∃ w : ℝ → ℝ, ContinuousOn w (Icc s t) ∧ w s = post s ∧ w t = pre t ∧
      ∀ r ∈ Ico s t, ForwardDiffQuotientLE w r (-a + 3/(4*(r+c))*w r)
theorem widthPotential_mono {a c t x y : ℝ} (hc : 0 < c) (ht : 0 ≤ t) (h : x ≤ y) :
    widthPotential a c t x ≤ widthPotential a c t y := by
  unfold widthPotential
  have hd : 0 < (t+c)^((3:ℝ)/4) := Real.rpow_pos_of_pos (by linarith) _
  exact add_le_add (div_le_div_of_nonneg_right h hd.le) le_rfl
private theorem decreasing_chain {x y : ℝ}
    (h : Relation.ReflTransGen (fun a b : ℝ => b ≤ a) x y) : y ≤ x := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact hstep.trans ih
/-- **Math.** Continuous interval estimates and downward jumps combine over a
finite event set; finiteness must come from the independent volume budget. -/
theorem extinctionProfile_terminal_bound (compare : WidthIntervalComparisonStatement)
    {a c w0 T : ℝ} {E : Set ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 < T)
    (hE : E.Finite) (hEt : E ⊆ Ioo 0 T) (W : ExtinctionProfile a c w0 T E) :
    4*a*(T+c)^((1:ℝ)/4) ≤ widthPotential a c 0 w0 := by
  let before := fun t => widthPotential a c t (W.pre t)
  let after := fun t => widthPotential a c t (W.post t)
  have chain := checked_finite_timeline ℝ (fun x y => y ≤ x) before after 0 T hT E hE hEt
    (fun t ht => Relation.ReflTransGen.single
      (widthPotential_mono hc (hEt ht).1.le (W.jumps t ht))) (by
      intro s t hs hst ht hgap
      obtain ⟨w,hw,hstart,hend,hd⟩ := W.intervals s t hs hst ht hgap
      apply Relation.ReflTransGen.single
      have hb := compare a c s t w ha hc hs hst hw hd
      simpa only [before,after,hstart,hend] using hb)
  have htotal : before T ≤ after 0 := decreasing_chain chain
  have hfirst : after 0 ≤ widthPotential a c 0 w0 := widthPotential_mono hc le_rfl W.initial
  have hnonneg : 0 ≤ W.pre T / (T+c)^((3:ℝ)/4) :=
    div_nonneg W.terminal_nonneg (Real.rpow_pos_of_pos (by linarith : 0 < T+c) _).le
  change W.pre T / (T+c)^((3:ℝ)/4) + 4*a*(T+c)^((1:ℝ)/4) ≤ _ at htotal
  exact (le_add_of_nonneg_left hnonneg).trans (htotal.trans hfirst)
/-- **Math.** A late nonnegative terminal width contradicts the actual accumulated estimates. -/
theorem extinctionProfile_impossible (compare : WidthIntervalComparisonStatement)
    {a c w0 T : ℝ} {E : Set ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 < T)
    (hlate : widthPotential a c 0 w0 < 4*a*(T+c)^((1:ℝ)/4))
    (hE : E.Finite) (hEt : E ⊆ Ioo 0 T) : ¬ Nonempty (ExtinctionProfile a c w0 T E) := by
  rintro ⟨W⟩
  exact (not_le_of_gt hlate) (extinctionProfile_terminal_bound compare ha hc hT hE hEt W)
#print axioms widthPotential_mono
#print axioms extinctionProfile_terminal_bound
#print axioms extinctionProfile_impossible
end PoincareConjecture.ProofContract.Refinement20260927
