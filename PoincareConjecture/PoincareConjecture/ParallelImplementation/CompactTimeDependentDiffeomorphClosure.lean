import PoincareConjecture.ParallelImplementation.CompactSmoothFamilyLocalDiffeomorph
import PoincareConjecture.ParallelImplementation.TimeDependentFlowJointSmooth
import MorganTianLib.Ch03.RicciFlow.TimeDependentGaugeFlow
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CompactTimeDependentDiffeomorphClosure
open MorganTianLib Riemannian Set
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
theorem exists_time_dependent_diffeomorph_flow
    [CompactSpace M]
    (V : SmoothTimeDependentVectorField (I := I) (M := M)) :
    ∃ T : ℝ, 0 < T ∧ ∃ φ : ℝ → Diffeomorph I I M M ∞,
      φ 0 = Diffeomorph.refl I M ∞ ∧
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : M × ℝ => φ q.2 q.1)
        ((Set.univ : Set M) ×ˢ Ico 0 T) ∧
      ∀ t ∈ Ico 0 T, ∀ p : M,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s p) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (φ t p, t))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  by_cases hM : Nonempty M
  · obtain ⟨p₀⟩ := hM
    obtain ⟨B⟩ := MorganTianLib.exists_timeDependentFlowBox
      (I := I) (M := M) V 0
    obtain ⟨ε, hε, hεη, hjoint⟩ :=
      PoincareConjecture.ParallelImplementation.TimeDependentFlowJointSmooth.exists_short_joint_smooth_spatialFlow B
    obtain ⟨epsilonLocal, hLocalPos, hLocalLe, hLocal⟩ :=
      PoincareConjecture.ParallelImplementation.CompactSmoothFamilyLocalDiffeomorph.exists_uniform_local_diffeomorph_window
        (fun q : M × ℝ => B.spatialFlow q.1 q.2) ε hε hjoint B.spatialFlow_zero
    have hprodAt : ∀ p : M, ∃ U : Set M, ∃ S : Set ℝ,
        IsOpen U ∧ p ∈ U ∧ IsOpen S ∧ (0 : ℝ) ∈ S ∧ U ×ˢ S ⊆ B.U := by
      intro p
      have hp : (p, (0 : ℝ)) ∈ B.U := B.slice_subset (by simp)
      exact mem_nhds_prod_iff'.mp (B.isOpen_U.mem_nhds hp)
    choose U S hUopen hpU hSopen h0S hrect using hprodAt
    have hrad : ∀ p : M, ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℝ) r ⊆ S p := by
      intro p
      exact Metric.mem_nhds_iff.mp ((hSopen p).mem_nhds (h0S p))
    choose r hr hball using hrad
    obtain ⟨cover, hcover⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
        U hUopen (by
          intro p hp
          exact mem_iUnion.mpr ⟨p, hpU p⟩)
    have hcoverNe : cover.Nonempty := by
      by_contra hne
      have hempty : cover = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hfalse : (Set.univ : Set M) ⊆ (∅ : Set M) := by
        simpa [hempty] using hcover
      have hpfalse := hfalse (mem_univ p₀)
      simp at hpfalse
    let ρ : ℝ := (cover.image r).min' (hcoverNe.image r)
    have hρpos : 0 < ρ := by
      obtain ⟨p, hp, hpeq⟩ := Finset.mem_image.mp
        (Finset.min'_mem (cover.image r) (hcoverNe.image r))
      change 0 < (cover.image r).min' (hcoverNe.image r)
      rw [← hpeq]
      exact hr p
    have hρle : ∀ p : M, p ∈ cover → ρ ≤ r p := by
      intro p hp
      exact Finset.min'_le (cover.image r) (r p)
        (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
    have htube : ∀ p : M, ∀ s ∈ Set.Ioo (-ρ) ρ, (p, s) ∈ B.U := by
      intro p s hs
      obtain ⟨i, hi, hpi⟩ := mem_iUnion₂.mp (hcover (mem_univ p))
      have hsball : s ∈ Metric.ball (0 : ℝ) (r i) := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero]
        exact lt_of_lt_of_le (abs_lt.mpr hs) (hρle i hi)
      exact hrect i ⟨hpi, hball i hsball⟩
    let T : ℝ := min epsilonLocal ρ / 2
    have hT : 0 < T := by dsimp [T]; positivity
    have hTlocal : T ≤ epsilonLocal := by dsimp [T]; linarith [min_le_left epsilonLocal ρ]
    have hTε : T ≤ ε := hTlocal.trans hLocalLe
    have hTρ : T ≤ ρ := by dsimp [T]; linarith [min_le_right epsilonLocal ρ]
    have hTeta : T ≤ B.eta := hTε.trans hεη
    let F : M → ℝ → M := B.spatialFlow
    have hFjoint : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞
        (fun q : M × ℝ => F q.1 q.2)
        ((Set.univ : Set M) ×ˢ Set.Ioo (-T) T) := by
      apply hjoint.mono
      intro q hq
      refine ⟨mem_univ q.1, ?_⟩
      constructor
      · exact lt_of_le_of_lt (neg_le_neg hTε) hq.2.1
      · exact lt_of_lt_of_le hq.2.2 hTε
    have hFzero : ∀ p : M, F p 0 = p := by
      intro p
      exact B.spatialFlow_zero p
    let Bshift : ∀ s : ℝ, s ∈ Set.Ioo (-T) T →
        MorganTianLib.TimeDependentFlowBox (I := I) (M := M) V s := by
      intro s hs
      refine ⟨B.eta, B.U, B.Φ, B.eta_pos, B.isOpen_U, ?_, B.apply_zero,
        B.integral_curve, B.continuousOn, B.time_coord⟩
      rintro ⟨p, t⟩ ⟨-, ht⟩
      have ht' : t = s := by simpa using ht
      subst t
      apply htube p s
      constructor <;> linarith [hs.1, hs.2, hTρ]
    have hcomp₀ : ∀ (s : ℝ) (hs : s ∈ Set.Ioo (-T) T) (p : M),
        (Bshift s hs).spatialFlow (F p s) (-s) = p := by
      intro s hs p
      change (Bshift s hs).spatialFlow (B.spatialFlow p s) (-s) = p
      simpa using MorganTianLib.TimeDependentFlowBox.spatialFlow_comp_inverse_of_common
        (B₀ := B) (B₁ := Bshift s hs) (ht := by ring) p
          (show s ∈ Set.Ioo (-B.eta) B.eta from by
            constructor <;> linarith [hs.1, hs.2, hTeta])
          (show -s ∈ Set.Ioo (-B.eta) B.eta from by
            constructor <;> linarith [hs.1, hs.2, hTeta])
    have hcomp₁ : ∀ (s : ℝ) (hs : s ∈ Set.Ioo (-T) T) (q : M),
        F ((Bshift s hs).spatialFlow q (-s)) s = q := by
      intro s hs q
      change B.spatialFlow ((Bshift s hs).spatialFlow q (-s)) s = q
      simpa using MorganTianLib.TimeDependentFlowBox.spatialFlow_comp_inverse_of_common
        (B₀ := Bshift s hs) (B₁ := B) (ht := by ring) q
          (show -s ∈ Set.Ioo (-B.eta) B.eta from by
            constructor <;> linarith [hs.1, hs.2, hTeta])
          (show -(-s) ∈ Set.Ioo (-B.eta) B.eta from by
            simpa using (show s ∈ Set.Ioo (-B.eta) B.eta from by
              constructor <;> linarith [hs.1, hs.2, hTeta]))
    have hmapBijective : ∀ s : ℝ, s ∈ Set.Ioo (-T) T →
        Function.Bijective (fun p => F p s) := by
      intro s hs
      constructor
      · intro p q hpq
        have h := congrArg (fun x => (Bshift s hs).spatialFlow x (-s)) hpq
        rw [hcomp₀ s hs p, hcomp₀ s hs q] at h
        exact h
      · intro q
        exact ⟨(Bshift s hs).spatialFlow q (-s), hcomp₁ s hs q⟩
    have hmapContMDiff : ∀ s : ℝ, s ∈ Set.Ioo (-T) T →
        ContMDiff I I ∞ (fun p => F p s) := by
      intro s hs
      have hsection : ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun p : M => (p, s)) := contMDiff_id.prodMk contMDiff_const
      have hmaps : MapsTo (fun p : M => (p, s)) Set.univ
          ((Set.univ : Set M) ×ˢ Set.Ioo (-T) T) := by
        intro p hp
        exact ⟨mem_univ p, hs⟩
      have hcomp := hFjoint.comp hsection.contMDiffOn hmaps
      rw [← contMDiffOn_univ]
      simpa [Function.comp_def] using hcomp
    have hsliceDiffeo : ∀ s : ℝ, s ∈ Set.Ioo (-T) T →
        ∃ f : Diffeomorph I I M M ∞, ∀ p : M, f p = F p s := by
      intro s hs
      have hsLocal : s ∈ Set.Ioo (-epsilonLocal) epsilonLocal := by
        constructor <;> linarith [hs.1, hs.2, hTlocal]
      have hld : IsLocalDiffeomorph I I ∞ (fun p : M => F p s) := hLocal s hsLocal
      refine ⟨hld.diffeomorphOfBijective (hmapBijective s hs), ?_⟩
      intro p
      rfl
    let φ : ℝ → Diffeomorph I I M M ∞ := fun t =>
      if ht : t ∈ Set.Ioo (-T) T then (hsliceDiffeo t ht).choose
      else Diffeomorph.refl I M ∞
    have hφflow : ∀ t : ℝ, t ∈ Set.Ioo (-T) T → ∀ p : M,
        φ t p = F p t := by
      intro t ht p
      simp only [φ, dif_pos ht]
      exact (hsliceDiffeo t ht).choose_spec p
    have h0T : (0 : ℝ) ∈ Set.Ioo (-T) T := by
      constructor <;> linarith [hT]
    have hφzero : φ 0 = Diffeomorph.refl I M ∞ := by
      apply Diffeomorph.ext
      intro p
      change φ 0 p = p
      calc
        φ 0 p = F p 0 := hφflow 0 h0T p
        _ = p := hFzero p
    have htimeDomain : (Set.univ : Set M) ×ˢ Set.Ico (0 : ℝ) T ⊆
        (Set.univ : Set M) ×ˢ Set.Ioo (-T) T := by
      rintro ⟨p, t⟩ ⟨-, ht⟩
      refine ⟨mem_univ p, ?_⟩
      exact ⟨by linarith [ht.1, hT], ht.2⟩
    have hjointIco := hFjoint.mono htimeDomain
    have hjointAgreement : EqOn (fun q : M × ℝ => φ q.2 q.1)
        (fun q => F q.1 q.2) ((Set.univ : Set M) ×ˢ Set.Ico 0 T) := by
      rintro ⟨p, t⟩ ⟨-, ht⟩
      exact hφflow t ⟨by linarith [ht.1, hT], ht.2⟩ p
    have hjointFamily := hjointIco.congr hjointAgreement
    have hderivative : ∀ t : ℝ, t ∈ Set.Ico 0 T → ∀ p : M,
        HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s => φ s p) t
          ((1 : ℝ →L[ℝ] ℝ).smulRight (V (φ t p, t))) := by
      intro t ht p
      have hts : t ∈ Set.Ioo (-T) T := ⟨by linarith [ht.1, hT], ht.2⟩
      have hte : t ∈ Set.Ioo (-B.eta) B.eta := by
        constructor <;> linarith [hts.1, hts.2, hTeta]
      have hflow := B.spatialFlow_hasMFDerivAt p hte
      have hval : φ t p = B.spatialFlow p t := by
        simpa [F] using hφflow t hts p
      rw [hval.symm] at hflow
      have hlocalEq : (B.spatialFlow p) =ᶠ[𝓝 t] (fun s => φ s p) := by
        filter_upwards [isOpen_Ioo.mem_nhds hts] with s hs
        exact (hφflow s hs p).symm
      rw [zero_add] at hflow
      exact hflow.congr_of_eventuallyEq hlocalEq.symm
    exact ⟨T, hT, φ, hφzero, hjointFamily, hderivative⟩
  ·
    refine ⟨1, by norm_num, (fun _ => Diffeomorph.refl I M ∞), rfl, ?_, ?_⟩
    · intro q hq
      rcases q with ⟨p, t⟩
      exact False.elim (hM ⟨p⟩)
    · intro t ht p
      exact False.elim (hM ⟨p⟩)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CompactTimeDependentDiffeomorphClosure
