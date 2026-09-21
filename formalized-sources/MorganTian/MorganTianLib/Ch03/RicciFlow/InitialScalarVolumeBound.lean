import MorganTianLib.Ch04.ScalarMinimumBounds
import MorganTianLib.Ch03.RicciFlow.CompactVolumeScalarLower
open Set MeasureTheory Riemannian
open scoped ContDiff Manifold Topology ENNReal Bundle
noncomputable section
namespace MorganTianLib
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [Nonempty M] [CompactSpace M] [T2Space M]
/-- **Math.** Compact-flow volume growth from an initial scalar lower bound;
no all-times scalar bound or initial volume-finiteness assumption is supplied. -/
theorem compact_real_volume_upper_of_initial_scalar_lower
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {T C : ℝ} (hC : 0 ≤ C)
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hinit : ∀ p : M, -C ≤ scalarCurvatureAt (g 0) (g 0).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g 0)) p)
    {s : Set M} (hs : MeasurableSet s) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    riemannianMeasure (I := I) (g t) mu s ≠ ⊤ ∧
      (riemannianMeasure (I := I) (g t) mu s).toReal ≤
        Real.exp (C * t) * (riemannianMeasure (I := I) (g 0) mu s).toReal := by
/- SWARM_PROOF_BEGIN -/
  have hmin : -C ≤ scalarCurvatureMinimum (g 0) :=
    (le_scalarCurvatureMinimum_iff (g 0)
      (canonicalLeviCivita_isLeviCivita (g 0))).mpr hinit
  have hrestrict : ∀ {U : ℝ}, 0 < U → U < T →
      IsRicciFlowOn g (Icc (0 : ℝ) U) := by
    intro U hU hUT
    have hsub : Icc (0 : ℝ) U ⊆ Ico 0 T := by
      intro u hu
      exact ⟨hu.1, hu.2.trans_lt hUT⟩
    have hnontrivial : (Icc (0 : ℝ) U).Nontrivial := by
      apply nontrivial_of_mem_mem_ne
        (show (0 : ℝ) ∈ Icc 0 U from ⟨le_rfl, hU.le⟩)
        (show U ∈ Icc 0 U from ⟨hU.le, le_rfl⟩)
        (ne_of_lt hU)
    refine
      { ordConnected := ordConnected_Icc
        nontrivial := hnontrivial
        smooth := hflow.smooth.mono (Set.prod_mono subset_rfl hsub)
        equation := ?_ }
    intro u hu p x y
    exact (hflow.equation u (hsub hu) p x y).mono hsub
  have hscalar : ∀ {U : ℝ}, U < T →
      ∀ u ∈ Icc (0 : ℝ) U, ∀ p : M,
        -C ≤ scalarCurvatureAt (g u) (g u).leviCivitaConnection
          (canonicalLeviCivita_isLeviCivita (g u)) p := by
    intro U hUT u hu p
    have huIco : u ∈ Ico (0 : ℝ) T :=
      ⟨hu.1, hu.2.trans_lt hUT⟩
    have hbar := scalarCurvatureMinimum_negative_lower_bound_of_isRicciFlowOn
      hflow huIco (by linarith [hC]) hmin
    have hn : 0 < (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
    have hden : 0 < 2 * u * C + (Module.finrank ℝ E : ℝ) := by
      have huC : 0 ≤ u * C := mul_nonneg hu.1 hC
      nlinarith
    have hrat : -C ≤
        -(Module.finrank ℝ E : ℝ) * C /
          (2 * u * C + (Module.finrank ℝ E : ℝ)) := by
      apply (le_div_iff₀ hden).2
      have hsq : 0 ≤ C ^ 2 := sq_nonneg C
      have hterm : 0 ≤ u * C ^ 2 := mul_nonneg hu.1 hsq
      nlinarith
    have hbar' :
        -(Module.finrank ℝ E : ℝ) * C /
          (2 * u * C + (Module.finrank ℝ E : ℝ)) ≤
            scalarCurvatureMinimum (g u) := by
      simpa [abs_of_nonneg hC] using hbar
    exact hrat.trans (hbar'.trans
      (scalarCurvatureMinimum_le_scalarCurvatureAt (g u)
        (canonicalLeviCivita_isLeviCivita (g u)) p))
  by_cases htpos : 0 < t
  · exact compact_real_volume_upper_of_scalar_lower mu
      (hrestrict htpos ht.2) (hscalar ht.2) hs ⟨ht.1, le_rfl⟩
  · have ht0 : t = 0 := le_antisymm (le_of_not_gt htpos) ht.1
    have hTpos : 0 < T := lt_of_le_of_lt ht.1 ht.2
    have hhalfpos : 0 < T / 2 := by linarith
    have hhalfT : T / 2 < T := by linarith
    have hres := compact_real_volume_upper_of_scalar_lower mu
      (hrestrict hhalfpos hhalfT) (hscalar hhalfT) hs
        ⟨le_rfl, hhalfpos.le⟩
    simpa [ht0] using hres
/- SWARM_PROOF_END -/
end MorganTianLib
