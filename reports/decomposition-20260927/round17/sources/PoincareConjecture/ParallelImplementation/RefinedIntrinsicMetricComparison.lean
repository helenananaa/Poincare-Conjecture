import PoincareConjecture.ProofContract.Refinement20260927.IntrinsicSphereEnergy
import MorganTianLib.Ch01.OrthoFrame
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedIntrinsicMetricComparison
open PoincareConjecture.ProofContract.Refinement20260927
theorem intrinsic_metric_comparison : IntrinsicMetricTimeComparisonStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro M g a b hab hg t ht eta heta
  by_cases habEq : a = b
  · subst b
    refine ⟨1, by norm_num, ?_⟩
    intro s hs hst p v
    have hs_eq : s = a := by
      rcases hs with ⟨hsa, has⟩
      linarith
    have ht_eq : t = a := by
      rcases ht with ⟨hta, hat⟩
      linarith
    subst s
    subst t
    have hvnonneg : 0 ≤ (g a).metricInner p v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact ((g a).metricInner_self_pos p v hv).le
    constructor <;> nlinarith [mul_nonneg heta.le hvnonneg]
  · have hablt : a < b := lt_of_le_of_ne hab habEq
    let E3 := PoincareConjecture.ProofContract.V1.Euclidean3
    let I3 := modelWithCornersSelf ℝ E3
    let H : M × ℝ → Type := MorganTianLib.HorizontalTangentSpace I3 M
    let D : M × ℝ → Type := fun z => H z →L[ℝ] ℝ
    let B : M × ℝ → Type := fun z => H z →L[ℝ] H z →L[ℝ] ℝ
    let F := E3 →L[ℝ] E3 →L[ℝ] ℝ
    have hTbase (p : M) :
        (trivializationAt E3 H (p, (0 : ℝ))).baseSet =
          (chartAt E3 p).source ×ˢ (Set.univ : Set ℝ) := by
      ext z
      change z.1 ∈ (trivializationAt E3 (TangentSpace I3) p).baseSet ↔
        z.1 ∈ (chartAt E3 p).source ∧ z.2 ∈ (Set.univ : Set ℝ)
      rw [TangentBundle.trivializationAt_baseSet]
      simp
    have hscalarbase (p : M) :
        (trivializationAt ℝ (fun _ : M × ℝ => ℝ) (p, (0 : ℝ))).baseSet =
          (Set.univ : Set (M × ℝ)) := by
      rfl
    have hcoeffFor (p : M) :
        ContinuousOn
          (fun z : M × ℝ =>
            ((trivializationAt F B (p, (0 : ℝ)))
              (MorganTianLib.horizontalMetricSection g z)).2)
          ((chartAt E3 p).source ×ˢ Set.Icc a b) := by
      let U := (chartAt E3 p).source
      let eB := trivializationAt F B (p, (0 : ℝ))
      have hHbase : (trivializationAt E3 H (p, (0 : ℝ))).baseSet =
          U ×ˢ (Set.univ : Set ℝ) := by
        ext z
        change z.1 ∈ (trivializationAt E3 (TangentSpace I3) p).baseSet ↔
          z.1 ∈ (chartAt E3 p).source ∧ z.2 ∈ (Set.univ : Set ℝ)
        rw [TangentBundle.trivializationAt_baseSet]
        simp
      have hscalar : (trivializationAt ℝ (fun _ : M × ℝ => ℝ) (p, (0 : ℝ))).baseSet =
          (Set.univ : Set (M × ℝ)) := by
        ext z
        simp
      have hbase : eB.baseSet = U ×ˢ (Set.univ : Set ℝ) := by
        change (trivializationAt F B (p, (0 : ℝ))).baseSet = U ×ˢ (Set.univ : Set ℝ)
        rw [hom_trivializationAt_baseSet]
        rw [hom_trivializationAt_baseSet]
        rw [hHbase]
        rw [hscalar]
        ext z
        simp [U]
      let S : Set (M × ℝ) := U ×ˢ Set.Icc a b
      have hres : ContMDiffOn
          ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
            (modelWithCornersSelf ℝ ℝ))
          (((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))).prod
            (modelWithCornersSelf ℝ ℝ)).prod
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3) →L[ℝ]
              EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ))) (↑(⊤ : ℕ∞))
          (MorganTianLib.horizontalMetricSection g) S := by
        simpa [S] using hg.mono (show S ⊆ Set.univ ×ˢ Set.Icc a b from by
          intro z hz
          change z.1 ∈ U ∧ z.2 ∈ Set.Icc a b at hz
          exact ⟨Set.mem_univ _, hz.2⟩)
      have hmaps : Set.MapsTo (MorganTianLib.horizontalMetricSection g) S eB.source := by
        intro z hz
        change z.1 ∈ U ∧ z.2 ∈ Set.Icc a b at hz
        rw [Bundle.Trivialization.mem_source, hbase]
        exact ⟨hz.1, Set.mem_univ _⟩
      have hresCont := hres.continuousOn
      have hsectionCoordCont := eB.continuousOn.comp hresCont hmaps
      have hcoeffCont : ContinuousOn
          (fun z : M × ℝ => (eB (MorganTianLib.horizontalMetricSection g z)).2) S := by
        exact continuous_snd.continuousOn.comp hsectionCoordCont (by
          intro z hz
          exact Set.mem_univ _)
      simpa [S, eB] using hcoeffCont
    have hmetricEval (p x : M) (s : ℝ)
        (hx : x ∈ (chartAt E3 p).source) (u : E3) :
        ((trivializationAt F B (p, (0 : ℝ)))
          (MorganTianLib.horizontalMetricSection g (x, s))).2 u u =
        (g s).metricInner x
          ((trivializationAt E3 H (p, (0 : ℝ))).symmL ℝ (x, s) u)
          ((trivializationAt E3 H (p, (0 : ℝ))).symmL ℝ (x, s) u) := by
      let q0 : M × ℝ := (p, (0 : ℝ))
      let τ := trivializationAt E3 H q0
      let σ := trivializationAt ℝ (fun _ : M × ℝ => ℝ) q0
      have hτbase : τ.baseSet = (chartAt E3 p).source ×ˢ (Set.univ : Set ℝ) := by
        simpa [τ, q0] using hTbase p
      have hσbase : σ.baseSet = Set.univ := by
        simpa [σ, q0] using hscalarbase p
      have hτ : (x, s) ∈ τ.baseSet := by
        rw [hτbase]
        exact ⟨hx, Set.mem_univ _⟩
      have hσ : (x, s) ∈ σ.baseSet := by rw [hσbase]; exact Set.mem_univ _
      change ((trivializationAt F B q0)
          (MorganTianLib.horizontalMetricSection g (x, s))).2 u u = _
      rw [hom_trivializationAt_apply]
      simp only [MorganTianLib.horizontalMetricSection]
      rw [inCoordinates_apply_eq₂ hτ hτ hσ]
      rw [τ.symmL_apply hτ u]
      simp
      dsimp [τ, q0]
    let R : F →L[ℝ] MetricOperator :=
      ContinuousLinearMap.compL ℝ E3 (E3 →L[ℝ] ℝ) E3
        (InnerProductSpace.toDual ℝ E3).symm
    have hRquad (A : F) (v : E3) : quadraticValue (R A) v = A v v := by
      change inner ℝ ((InnerProductSpace.toDual ℝ E3).symm (A v)) v = A v v
      exact InnerProductSpace.toDual_symm_apply
    have hpatch (q : M) (K : Set M) (hK : IsCompact K) (hqK : q ∈ K)
        (hKU : K ⊆ (chartAt E3 q).source) :
        ∃ r : ℝ, 0 < r ∧
          ∀ s ∈ Set.Icc a b, dist s t < r → ∀ x ∈ K,
            ∀ v : TangentSpace I3 x,
              (1 - eta) * (g t).metricInner x v v ≤ (g s).metricInner x v v ∧
              (g s).metricInner x v v ≤ (1 + eta) * (g t).metricInner x v v := by
      let c := chartAt E3 q
      let Y : Set E3 := c '' K
      have hYcompact : IsCompact Y :=
        hK.image_of_continuousOn (c.continuousOn.mono hKU)
      let X := {y : E3 // y ∈ Y}
      letI : CompactSpace X := isCompact_iff_compactSpace.mp hYcompact
      have hXne : Nonempty X := by
        refine ⟨⟨c q, ?_⟩⟩
        exact ⟨q, hqK, rfl⟩
      letI : Nonempty X := hXne
      let φ : ℝ × X → M × ℝ := fun z => (c.symm z.2.1, z.1)
      have hsymm : Continuous (fun z : ℝ × X => c.symm z.2.1) := by
        apply c.continuousOn_symm.comp_continuous
          (continuous_subtype_val.comp continuous_snd)
        intro z
        rcases z.2.2 with ⟨x, hx, hxy⟩
        change z.2.1 ∈ c.target
        rw [← hxy]
        exact c.map_source (hKU hx)
      have hφ : Continuous φ := by
        exact hsymm.prodMk continuous_fst
      have hmaps : Set.MapsTo φ (Set.Icc a b ×ˢ (Set.univ : Set X))
          ((chartAt E3 q).source ×ˢ Set.Icc a b) := by
        intro z hz
        rcases z.2.2 with ⟨x, hx, hxy⟩
        have hsymm : c.symm z.2.1 = x := by
          rw [← hxy]
          exact c.left_inv (hKU hx)
        change c.symm z.2.1 ∈ c.source ∧ z.1 ∈ Set.Icc a b
        exact ⟨by rw [hsymm]; exact hKU hx, hz.1⟩
      let Q : ℝ × X → MetricOperator := fun z =>
        R (((trivializationAt F B (q, (0 : ℝ)))
          (MorganTianLib.horizontalMetricSection g (φ z))).2)
      have hQcont : ContinuousOn Q (Set.Icc a b ×ˢ (Set.univ : Set X)) := by
        dsimp [Q]
        exact R.continuous.comp_continuousOn
          ((hcoeffFor q).comp hφ.continuousOn hmaps)
      have hQpos : ∀ z : ℝ × X, ∀ u : E3, u ≠ 0 →
          0 < quadraticValue (Q z) u := by
        intro z u hu
        rcases z.2.2 with ⟨x, hx, hxy⟩
        have hsymm : c.symm z.2.1 = x := by
          rw [← hxy]
          exact c.left_inv (hKU hx)
        have hτ : (x, z.1) ∈ (trivializationAt E3 H (q, (0 : ℝ))).baseSet := by
          rw [hTbase q]
          exact ⟨hKU hx, Set.mem_univ _⟩
        have hsymm_ne :
            (trivializationAt E3 H (q, (0 : ℝ))).symmL ℝ (x, z.1) u ≠ 0 := by
          intro hz
          have hleft := (trivializationAt E3 H (q, (0 : ℝ))).continuousLinearMapAt_symmL
            (R := ℝ) hτ u
          apply hu
          calc
            u = (trivializationAt E3 H (q, (0 : ℝ))).continuousLinearMapAt ℝ (x, z.1)
                ((trivializationAt E3 H (q, (0 : ℝ))).symmL ℝ (x, z.1) u) := hleft.symm
            _ = 0 := by rw [hz]; simp
        have heval : quadraticValue (Q z) u =
            (g z.1).metricInner x
              ((trivializationAt E3 H (q, (0 : ℝ))).symmL ℝ (x, z.1) u)
              ((trivializationAt E3 H (q, (0 : ℝ))).symmL ℝ (x, z.1) u) := by
          rw [hRquad]
          change ((trivializationAt F B (q, (0 : ℝ)))
              (MorganTianLib.horizontalMetricSection g (c.symm z.2.1, z.1))).2 u u = _
          rw [hsymm]
          exact hmetricEval q x z.1 (hKU hx) u
        rw [heval]
        exact (g z.1).metricInner_self_pos x _ hsymm_ne
      have hQposI : ∀ s ∈ Set.Icc a b, ∀ x : X, ∀ u : E3, u ≠ 0 →
          0 < quadraticValue (Q (s, x)) u := by
        intro s hs x u hu
        exact hQpos (s, x) u hu
      have hrel := compact_metric_relative checked_compact_coercivity
        checked_compact_time_variation X Q hab hQcont hQposI ht (eta := eta) heta
      obtain ⟨r, hr, hcomp⟩ := hrel
      refine ⟨r, hr, ?_⟩
      intro s hs hst x hxK v
      let y : E3 := c x
      have hy : y ∈ Y := ⟨x, hxK, rfl⟩
      let z : ℝ × X := (s, ⟨y, hy⟩)
      let u : E3 := (trivializationAt E3 H (q, (0 : ℝ))).continuousLinearMapAt
        ℝ (x, s) v
      have hτ : (x, s) ∈ (trivializationAt E3 H (q, (0 : ℝ))).baseSet := by
        rw [hTbase q]
        exact ⟨hKU hxK, Set.mem_univ _⟩
      have hu : (trivializationAt E3 H (q, (0 : ℝ))).symmL ℝ (x, s) u = v := by
        exact (trivializationAt E3 H (q, (0 : ℝ))).symmL_continuousLinearMapAt
          (R := ℝ) hτ v
      have hEval : quadraticValue (Q z) u = (g s).metricInner x v v := by
        rw [hRquad]
        change ((trivializationAt F B (q, (0 : ℝ)))
            (MorganTianLib.horizontalMetricSection g (c.symm y, s))).2 u u = _
        rw [c.left_inv (hKU hxK), hmetricEval q x s (hKU hxK) u, hu]
      have hτt : (x, t) ∈ (trivializationAt E3 H (q, (0 : ℝ))).baseSet := by
        rw [hTbase q]
        exact ⟨hKU hxK, Set.mem_univ _⟩
      have htransport :
          (trivializationAt E3 H (q, (0 : ℝ))).symmL ℝ (x, t) u =
            (trivializationAt E3 H (q, (0 : ℝ))).symmL ℝ (x, s) u := by
        rw [(trivializationAt E3 H (q, (0 : ℝ))).symmL_apply (R := ℝ) hτt u,
          (trivializationAt E3 H (q, (0 : ℝ))).symmL_apply (R := ℝ) hτ u]
        rfl
      have hEvalT : quadraticValue (Q (t, ⟨y, hy⟩)) u = (g t).metricInner x v v := by
        rw [hRquad]
        change ((trivializationAt F B (q, (0 : ℝ)))
            (MorganTianLib.horizontalMetricSection g (c.symm y, t))).2 u u = _
        rw [c.left_inv (hKU hxK), hmetricEval q x t (hKU hxK) u, htransport, hu]
      have hcomp' := hcomp s hs hst ⟨y, hy⟩ u
      rw [hEvalT, hEval] at hcomp'
      exact hcomp'
    by_cases hEmpty : IsEmpty M
    · refine ⟨1, by norm_num, ?_⟩
      intro s hs hst p v
      exact (hEmpty.false p).elim
    · classical
      have hlocalCompact (p : M) :
          ∃ K : Set M, IsCompact K ∧ p ∈ interior K ∧
            K ⊆ (chartAt E3 p).source := by
        exact exists_compact_subset (chartAt E3 p).open_source (mem_chart_source E3 p)
      let K : M → Set M := fun p => Classical.choose (hlocalCompact p)
      have hKprops (p : M) : IsCompact (K p) ∧ p ∈ interior (K p) ∧
          K p ⊆ (chartAt E3 p).source := Classical.choose_spec (hlocalCompact p)
      have hpatchExists (p : M) : ∃ r : ℝ, 0 < r ∧
          ∀ s ∈ Set.Icc a b, dist s t < r → ∀ x ∈ K p,
            ∀ v : TangentSpace I3 x,
              (1 - eta) * (g t).metricInner x v v ≤ (g s).metricInner x v v ∧
              (g s).metricInner x v v ≤ (1 + eta) * (g t).metricInner x v v := by
        apply hpatch p (K p) (hKprops p).1
        · exact interior_subset (hKprops p).2.1
        · exact (hKprops p).2.2
      choose r hr using hpatchExists
      have hcover : (Set.univ : Set M) ⊆ ⋃ p : M, interior (K p) := by
        intro p hp
        exact Set.mem_iUnion.mpr ⟨p, (hKprops p).2.1⟩
      obtain ⟨F, hFcover⟩ := isCompact_univ.elim_finite_subcover
        (fun p : M => interior (K p)) (fun p => isOpen_interior) hcover
      have hMne : Nonempty M := not_isEmpty_iff.mp hEmpty
      have hFne : F.Nonempty := by
        obtain ⟨p⟩ := hMne
        have hp := hFcover (Set.mem_univ p)
        rcases Set.mem_iUnion₂.mp hp with ⟨q, hqF, hq⟩
        exact ⟨q, hqF⟩
      let r0 : ℝ := F.inf' hFne r
      have hr0 : 0 < r0 := by
        exact (Finset.lt_inf'_iff _).2 (by
          intro q hq
          exact (hr q).1)
      refine ⟨r0, hr0, ?_⟩
      intro s hs hst p v
      have hpcover := hFcover (Set.mem_univ p)
      rcases Set.mem_iUnion₂.mp hpcover with ⟨q, hqF, hpq⟩
      have hpK : p ∈ K q := interior_subset hpq
      have hstq : dist s t < r q := lt_of_lt_of_le hst (Finset.inf'_le _ hqF)
      exact (hr q).2 s hs hstq p hpK v
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedIntrinsicMetricComparison
