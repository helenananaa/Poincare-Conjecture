import PoincareConjecture.ProofContract.Refinement20260927.RicciVolumeBudget
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedClosedScalarPropagation
open PoincareConjecture.ProofContract.Refinement20260927
theorem closed_scalar_propagation : ClosedScalarPropagationStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  letI : NeZero (Module.finrank ℝ PoincareConjecture.ProofContract.V1.Euclidean3) :=
    ⟨by simp [PoincareConjecture.ProofContract.V1.Euclidean3]⟩
  intro M g T C hT hC hflow hinit t ht p
  have hsub : Set.Ico (0 : ℝ) T ⊆ Set.Icc 0 T := by
    intro u hu
    exact ⟨hu.1, hu.2.le⟩
  have hflowIco : MorganTianLib.IsRicciFlowOn g (Set.Ico (0 : ℝ) T) := by
    exact
      { ordConnected := Set.ordConnected_Ico
        nontrivial := by
          apply Set.nontrivial_of_mem_mem_ne
            (show (0 : ℝ) ∈ Set.Ico 0 T from ⟨le_rfl, hT⟩)
            (show T / 2 ∈ Set.Ico 0 T by constructor <;> linarith)
            (by linarith)
        smooth := hflow.smooth.mono (Set.prod_mono Set.Subset.rfl hsub)
        equation := by
          intro u hu q x y
          exact (hflow.equation u (hsub hu) q x y).mono hsub }
  have hmin0 : -C ≤ MorganTianLib.scalarCurvatureMinimum (g 0) :=
    (MorganTianLib.le_scalarCurvatureMinimum_iff (g 0)
      (MorganTianLib.canonicalLeviCivita_isLeviCivita (g 0))).2 hinit
  have hmono :=
    MorganTianLib.monotoneOn_scalarCurvatureMinimum_of_isRicciFlowOn_Ico hflowIco
  have hscalarHalf : ∀ u ∈ Set.Ico (0 : ℝ) T, ∀ q : M,
      -C ≤ MorganTianLib.scalarCurvatureAt (g u) (g u).leviCivitaConnection
        (MorganTianLib.canonicalLeviCivita_isLeviCivita (g u)) q := by
    intro u hu q
    have huMono : MorganTianLib.scalarCurvatureMinimum (g 0) ≤
        MorganTianLib.scalarCurvatureMinimum (g u) :=
      hmono ⟨le_rfl, hT⟩ hu hu.1
    have hminU : -C ≤ MorganTianLib.scalarCurvatureMinimum (g u) :=
      hmin0.trans huMono
    exact (MorganTianLib.le_scalarCurvatureMinimum_iff (g u)
      (MorganTianLib.canonicalLeviCivita_isLeviCivita (g u))).1 hminU q
  have hminHalf : ∀ u ∈ Set.Ico (0 : ℝ) T,
      -C ≤ MorganTianLib.scalarCurvatureMinimum (g u) := by
    intro u hu
    exact (MorganTianLib.le_scalarCurvatureMinimum_iff (g u)
      (MorganTianLib.canonicalLeviCivita_isLeviCivita (g u))).2 (hscalarHalf u hu)
  by_cases ht0 : t = 0
  · subst t
    exact hinit p
  · by_cases htT : t = T
    · subst t
      have hcont := MorganTianLib.continuousOn_scalarCurvatureMinimum_of_isRicciFlowOn
        hflow (show Set.Icc (0 : ℝ) T ⊆ Set.Icc 0 T from Set.Subset.rfl)
      have hcontClosure : ContinuousOn (fun s : ℝ =>
          MorganTianLib.scalarCurvatureMinimum (g s))
          (closure (Set.Ico (0 : ℝ) T)) := by
        simpa only [closure_Ico (ne_of_lt hT)] using hcont
      have hminT : -C ≤ MorganTianLib.scalarCurvatureMinimum (g T) :=
        le_on_closure hminHalf continuousOn_const hcontClosure (by
          rw [closure_Ico (ne_of_lt hT)]
          exact ⟨hT.le, le_rfl⟩)
      exact hminT.trans (MorganTianLib.scalarCurvatureMinimum_le_scalarCurvatureAt
        (g T) (MorganTianLib.canonicalLeviCivita_isLeviCivita (g T)) p)
    · have htlt : t < T := lt_of_le_of_ne ht.2 htT
      exact hscalarHalf t ⟨ht.1, htlt⟩ p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedClosedScalarPropagation
