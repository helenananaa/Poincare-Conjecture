import PoincareConjecture.ProofContract.Refinement20260927.MinimaxSweepout
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set Filter MorganTianLib
open scoped Topology
/-- **Math.** Independent near-max/low-energy split. ONE time radius works
for all sequence indices and slices; no optimal sweepout is assumed. -/
def UniformNearMaxTaylorStatement : Prop :=
  ∀ (v velocity : ℕ → SweepParameter → ℝ) (future : ℕ → ℝ → SweepParameter → ℝ)
    (m q : ℕ → ℝ) (W delta L Q K H : ℝ) (J : ℕ),
    0 < delta → 0 < H → 0 ≤ L → 0 ≤ Q → 0 ≤ K →
    (∀ j, J ≤ j → W ≤ m j) →
    (∀ j, J ≤ j → -Q ≤ q j) →
    (∀ j, J ≤ j → ∀ x, v j x ≤ m j) →
    (∀ j, J ≤ j → ∀ x, velocity j x ≤ L) →
    (∀ j, J ≤ j → ∀ x, W-delta < v j x → velocity j x ≤ q j) →
    (∀ j, J ≤ j → ∀ h, 0 < h → h < H → ∀ x,
      future j h x ≤ v j x + h*velocity j x + K*h^2) →
    ∃ h0 : ℝ, 0 < h0 ∧ h0 ≤ H ∧ ∀ j, J ≤ j → ∀ h, 0 < h → h < h0 → ∀ x,
      future j h x ≤ m j + h*q j + K*h^2
/-- **Math.** Fixed-h sequence limit BEFORE h tends to zero. J,H,K may depend
on eta, but not on j or h. No differentiability of w is assumed. -/
def MinimaxDiniLimitStatement : Prop :=
  ∀ (w : ℝ → ℝ) (m : ℕ → ℝ) (t a b : ℝ), Tendsto m atTop (𝓝 (w t)) →
    (∀ eta : ℝ, 0 < eta → ∃ J : ℕ, ∃ H K : ℝ, 0 < H ∧ 0 ≤ K ∧
      ∀ j, J ≤ j → ∀ h, 0 < h → h < H →
        w (t+h) ≤ m j + h*(-a+b*m j+eta) + K*h^2) →
    ForwardDiffQuotientLE w t (-a+b*w t)
/-- **Math.** Data needed from good sweepouts. Actual slice derivatives, a
uniform Taylor bound and the near-max estimate are all explicit obligations.
Existence of such sweepouts, including harmonic-map compactness, is NOT proved. -/
structure GoodSweepoutAt (F : SweepoutSpectrum.{u}) (t a b : ℝ) where
  sequence : ℕ → F.index
  converges : Tendsto (fun j => F.peak (sequence j) t) atTop (𝓝 (F.width t))
  velocity : ℕ → SweepParameter → ℝ
  derivative : ∀ j x, HasDerivAt (fun r => F.energy (sequence j) r x) (velocity j x) t
  control : ∀ eta : ℝ, 0 < eta → ∃ delta H L K : ℝ, ∃ J : ℕ,
    0 < delta ∧ 0 < H ∧ 0 ≤ L ∧ 0 ≤ K ∧
    (∀ j, J ≤ j → ∀ x, velocity j x ≤ L) ∧
    (∀ j, J ≤ j → ∀ x, F.width t-delta < F.energy (sequence j) t x →
      velocity j x ≤ -a+b*F.peak (sequence j) t+eta) ∧
    (∀ j, J ≤ j → ∀ h, 0 < h → h < H → ∀ x,
      F.energy (sequence j) (t+h) x ≤
        F.energy (sequence j) t x + h*velocity j x + K*h^2)
/-- **Math.** The two independent leaves give the EXACT Dini input consumed
by the checked extinction comparison. No infimum-attainment assumption. -/
theorem width_dini_of_good_sweepouts (nearMax : UniformNearMaxTaylorStatement)
    (limitPass : MinimaxDiniLimitStatement) (F : SweepoutSpectrum.{u})
    (t a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (G : GoodSweepoutAt F t a b) :
    ForwardDiffQuotientLE F.width t (-a+b*F.width t) := by
  apply limitPass F.width (fun j => F.peak (G.sequence j) t) t a b G.converges
  intro eta heta
  obtain ⟨delta,H,L,K,J,hd,hH,hL,hK,hvel,hnear,hTaylor⟩ := G.control eta heta
  let m := fun j => F.peak (G.sequence j) t
  let q := fun j => -a+b*m j+eta
  have hq : ∀ j, J ≤ j → -a ≤ q j := by
    intro j _
    have hp := mul_nonneg hb (F.peak_nonneg (G.sequence j) t)
    dsimp [q,m]; linarith
  obtain ⟨h0,hh0,h0H,hbound⟩ := nearMax
    (fun j => F.energy (G.sequence j) t) G.velocity
    (fun j h => F.energy (G.sequence j) (t+h)) m q
    (F.width t) delta L a K H J hd hH hL ha.le hK
    (fun j _ => F.width_le_peak (G.sequence j) t) hq
    (fun j _ x => F.energy_le_peak (G.sequence j) t x) hvel hnear hTaylor
  refine ⟨J,h0,K,hh0,hK,?_⟩
  intro j hj h hh hh0'
  apply (F.width_le_peak (G.sequence j) (t+h)).trans
  apply csSup_le (range_nonempty _)
  rintro _ ⟨x,rfl⟩
  exact hbound j hj h hh hh0' x
#print axioms width_dini_of_good_sweepouts
end PoincareConjecture.ProofContract.Refinement20260927
