import PoincareConjecture.ProofContract.Refinement20260927.RelativeApproximation
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open V1 Set MeasureTheory
open scoped Manifold ContDiff Topology
/-- **Math.** A continuous representative with differentiable, integrable slices.
The reference need not have a jointly smooth parameter extension. -/
structure RegularizationData (N : CompactSmoothThree.{u})
    (g : Riemannian.RiemannianMetric (𝓡 3) N) (D : BasedSphereClass N) where
  reference : C(SweepDomain, N)
  ends : EqOn reference (ContinuousMap.const SweepDomain D.base) sweepoutEnds
  correct_class : reference.HomotopicRel D.reference.continuousMap sweepoutEnds
  differentiable : ∀ s : SweepParameter, MDifferentiable (𝓡 2) (𝓡 3) (fun p => reference (s,p))
  integrable : ∀ s : SweepParameter,
    Integrable (sphereEnergyDensity N g (fun p => reference (s,p))) sphereEnergyMeasure
  dimension : ℕ
  model : AmbientEnergyModel N g dimension
  C : ℝ
  Q : ℝ
  C_nonneg : 0 ≤ C
  Q_nonneg : 0 ≤ Q
  approximants : ∀ delta : ℝ, 0 < delta → ∃ h : SmoothBasedSweepout N D.base,
    (∀ q : SweepDomain, dist (model.retraction.embed (h.continuousMap q))
      (model.retraction.embed (reference q)) < delta) ∧
    ∀ s : SweepParameter, AmbientC1Bounds model (fun p => reference (s,p))
      (fun p => h.map ((s:ℝ),p)) C Q delta
theorem AmbientC1Bounds.mono {N : CompactSmoothThree.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) N} {n : ℕ}
    {A : AmbientEnergyModel N g n} {f h : Sphere2 → N} {C Q d e : ℝ}
    (hb : AmbientC1Bounds A f h C Q d) (hle : d ≤ e) : AmbientC1Bounds A f h C Q e := by
  intro p
  exact ⟨(hb p).1, (hb p).2.1.trans hle,
    fun i => ⟨((hb p).2.2 i).1, ((hb p).2.2 i).2.trans hle⟩⟩
/-- **Math.** The two independent leaves turn actual approximation data into
smooth representatives in the SAME fixed relative class with controlled energy. -/
theorem RegularizationData.approximate (relative : RelativeRetractionHomotopyStatement.{u})
    (energy : SphereEnergyApproximationStatement.{u}) {N : CompactSmoothThree.{u}}
    {g : Riemannian.RiemannianMetric (𝓡 3) N} {D : BasedSphereClass N}
    (R : RegularizationData N g D) (e : ℝ) (he : 0 < e) :
    ∃ h : D.Representative, ∀ s : SweepParameter,
      sphereDirichletEnergy N g (fun p => h.val.map ((s:ℝ),p)) ≤
        sphereDirichletEnergy N g (fun p => R.reference (s,p)) + e := by
  obtain ⟨rho,hrho,homotopy⟩ := relative N R.dimension R.model.retraction R.reference
  obtain ⟨delta,hdelta,_hle,estimate⟩ := energy N g R.dimension R.model R.C R.Q e
    R.C_nonneg R.Q_nonneg he
  obtain ⟨h,hclose,hjet⟩ := R.approximants (min rho delta) (lt_min hrho hdelta)
  have hends : EqOn h.continuousMap R.reference sweepoutEnds := by
    intro q hq
    have href := R.ends hq
    change R.reference q = D.base at href
    change h.map ((q.1:ℝ),q.2) = R.reference q
    rw [href]
    rcases hq with hzero | hone
    · rw [hzero]; exact (h.ends q.2).1
    · rw [hone]; exact (h.ends q.2).2
  have hh := homotopy h.continuousMap
    (fun q => (hclose q).trans_le (min_le_left _ _)) hends
  refine ⟨⟨h,hh.trans R.correct_class⟩,?_⟩
  intro s
  have hsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun p => h.map ((s:ℝ),p)) :=
    h.smooth.comp (contMDiff_const.prodMk contMDiff_id)
  have hb := estimate (fun p => R.reference (s,p)) (fun p => h.map ((s:ℝ),p))
    (R.differentiable s) hsmooth (R.integrable s) ((hjet s).mono (min_le_right _ _))
  have hu := (abs_le.mp hb).2
  linarith
/-- **Math.** Additive errors allow smooth approximation even on zero-energy
slices, where a purely multiplicative error would require exact preservation. -/
def AdditiveRepresentativeTransfer (F G : SweepoutSpectrum.{u}) (t : ℝ) : Prop :=
  ∀ e : ℝ, 0 < e → ∀ i : F.index, ∃ j : G.index,
    ∀ x, G.energy j t x ≤ F.peak i t + e
theorem additiveTransfer_width_le {F G : SweepoutSpectrum.{u}} {t : ℝ}
    (h : AdditiveRepresentativeTransfer F G t) : G.width t ≤ F.width t := by
  apply le_csInf (range_nonempty _)
  rintro _ ⟨i,rfl⟩
  apply le_of_forall_pos_le_add
  intro e he
  obtain ⟨j,hj⟩ := h e he i
  apply (G.width_le_peak j t).trans
  exact csSup_le (range_nonempty _) (by rintro _ ⟨x,rfl⟩; exact hj x)
theorem approximateTransfer_to_additive {F G : SweepoutSpectrum.{u}} {t : ℝ}
    (h : ApproximateSweepoutTransfer F G t) : AdditiveRepresentativeTransfer F G t := by
  intro e he i
  let eta := e / (F.peak i t+1)
  have hn := F.peak_nonneg i t
  have hp : 0 < eta := div_pos he (by linarith)
  obtain ⟨send,reparam,hbound⟩ := h eta hp
  refine ⟨send i,?_⟩
  intro x
  have hb := (hbound i x).trans (mul_le_mul_of_nonneg_left
    (F.energy_le_peak i t (reparam i x)) (by linarith : 0 ≤ 1+eta))
  have heq : eta*(F.peak i t+1) = e := div_mul_cancel₀ e (by linarith)
  nlinarith
/-- **Math.** An actual slice-wise energy controlled reference plus relative
C1 approximation data; producing those data is still a geometric obligation. -/
def RegularizedClassTransfer (source target : IntrinsicSpectrumData.{u}) (t : ℝ) : Prop :=
  ∀ i : source.sweepouts.Representative,
    ∃ R : RegularizationData target.space (target.metric t) target.sweepouts,
      ∀ x : SweepParameter,
        sphereDirichletEnergy target.space (target.metric t) (fun p => R.reference (x,p)) ≤
          (source.spectrum checked_sphere_energy_continuity).energy i t x
theorem regularizedClassTransfer_to_additive (relative : RelativeRetractionHomotopyStatement.{u})
    (energy : SphereEnergyApproximationStatement.{u})
    {source target : IntrinsicSpectrumData.{u}} {t : ℝ}
    (h : RegularizedClassTransfer source target t) :
    AdditiveRepresentativeTransfer (source.spectrum checked_sphere_energy_continuity)
      (target.spectrum checked_sphere_energy_continuity) t := by
  intro e he i
  obtain ⟨R,hreference⟩ := h i
  obtain ⟨j,hj⟩ := R.approximate relative energy e he
  refine ⟨j,?_⟩
  intro x
  exact (hj x).trans (add_le_add ((hreference x).trans
    ((source.spectrum checked_sphere_energy_continuity).energy_le_peak i t x)) le_rfl)
#print axioms AmbientC1Bounds.mono
#print axioms RegularizationData.approximate
#print axioms additiveTransfer_width_le
#print axioms approximateTransfer_to_additive
#print axioms regularizedClassTransfer_to_additive
end PoincareConjecture.ProofContract.Refinement20260927
