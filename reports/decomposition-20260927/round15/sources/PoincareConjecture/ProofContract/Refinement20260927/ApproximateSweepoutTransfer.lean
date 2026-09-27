import PoincareConjecture.ProofContract.Refinement20260927.SweepoutPostcomposition
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
open scoped Manifold ContDiff
/-- **Math.** For every positive energy error there is an actual representative
transfer with that error. The maps may depend on the error; an exactly
nonexpanding smooth map is NOT required. Class membership is in the index type. -/
def ApproximateSweepoutTransfer (F G : SweepoutSpectrum.{u}) (t : ℝ) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ send : F.index → G.index,
    ∃ reparam : F.index → SweepParameter → SweepParameter,
      ∀ i x, G.energy (send i) t x ≤ (1+eta) * F.energy i t (reparam i x)
/-- **Math.** The original exact transfer is still accepted, so this is a
weaker interface, not a stronger unproved demand imposed on the old route. -/
theorem SweepoutTransfer.toApproximate {F G : SweepoutSpectrum.{u}} {t : ℝ}
    (h : SweepoutTransfer F G t) : ApproximateSweepoutTransfer F G t := by
  intro eta he
  refine ⟨h.send,h.reparam,?_⟩
  intro i x
  have hn := F.nonneg i t (h.reparam i x)
  have hp := mul_nonneg he.le hn
  nlinarith [h.energy_le i x]
/-- **Math.** The infimum need not be attained; positive multiplication is
handled by dividing BEFORE taking the infimum over the source class. -/
theorem spectrum_transfer_mul_bound (F G : SweepoutSpectrum.{u}) (t L : ℝ) (hL : 0 < L)
    (send : F.index → G.index) (reparam : F.index → SweepParameter → SweepParameter)
    (he : ∀ i x, G.energy (send i) t x ≤ L * F.energy i t (reparam i x)) :
    G.width t ≤ L * F.width t := by
  have hpoint (i : F.index) : G.width t ≤ L * F.peak i t := by
    apply (G.width_le_peak (send i) t).trans
    apply csSup_le (range_nonempty _)
    rintro _ ⟨x,rfl⟩
    exact (he i x).trans (mul_le_mul_of_nonneg_left (F.energy_le_peak i t (reparam i x)) hL.le)
  have hdiv : G.width t / L ≤ F.width t := by
    apply le_csInf (range_nonempty _)
    rintro _ ⟨i,rfl⟩
    exact (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using hpoint i)
  simpa only [mul_comm] using (div_le_iff₀ hL).mp hdiv
/-- **Math.** Arbitrarily small multiplicative error is sufficient for an
EXACT width jump inequality; no limit of the representative maps is asserted. -/
theorem approximateTransfer_width_le {F G : SweepoutSpectrum.{u}} {t : ℝ}
    (h : ApproximateSweepoutTransfer F G t) : G.width t ≤ F.width t := by
  apply le_of_forall_pos_le_add
  intro e he
  let eta := e / (F.width t+1)
  have hn := F.width_nonneg t
  have heta : 0 < eta := div_pos he (by linarith)
  obtain ⟨send,reparam,henergy⟩ := h eta heta
  have hb := spectrum_transfer_mul_bound F G t (1+eta) (by linarith) send reparam henergy
  have hc : eta * (F.width t+1) = e := div_mul_cancel₀ e (by linarith)
  nlinarith
/-- **Math.** One sufficient geometric source of approximate transfer. The
existence of these class-preserving smooth almost-contractions is NOT asserted. -/
def AlmostContractingClassMaps {M N : CompactSmoothThree.{u}}
    (C : BasedSphereClass M) (D : BasedSphereClass N)
    (gM : Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : Riemannian.RiemannianMetric (𝓡 3) N) : Prop :=
  ∀ eta : ℝ, 0 < eta → ∃ h : SmoothClassMap C D, TargetMetricBound gM gN h.map (1+eta)
/-- **Math.** Differential almost-contraction and relative-class preservation
produce the precise error-tolerant transfer; the chosen maps are not assumed equal. -/
theorem almostContracting_to_approximate (continuousEnergy : SphereEnergyContinuityStatement.{u})
    {M N : CompactSmoothThree.{u}} (C : BasedSphereClass M) (D : BasedSphereClass N)
    (gM : ℝ → Riemannian.RiemannianMetric (𝓡 3) M)
    (gN : ℝ → Riemannian.RiemannianMetric (𝓡 3) N) (t : ℝ)
    (h : AlmostContractingClassMaps C D (gM t) (gN t)) :
    ApproximateSweepoutTransfer (intrinsicSpectrum continuousEnergy M C gM)
      (intrinsicSpectrum continuousEnergy N D gN) t := by
  intro eta heta
  obtain ⟨map,hbound⟩ := h eta heta
  refine ⟨map.send,fun _ x => x,?_⟩
  intro i x
  have hf : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p => i.val.map ((x:ℝ),p)) :=
    i.val.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  simpa only [intrinsicSpectrum,SmoothClassMap.send,SmoothClassMap.sendSweepout,Function.comp_def]
    using sphere_energy_postcompose_le continuousEnergy (gM t) (gN t) map.map map.smooth
      (fun p => i.val.map ((x:ℝ),p)) hf hbound
#print axioms SweepoutTransfer.toApproximate
#print axioms spectrum_transfer_mul_bound
#print axioms approximateTransfer_width_le
#print axioms almostContracting_to_approximate
end PoincareConjecture.ProofContract.Refinement20260927
