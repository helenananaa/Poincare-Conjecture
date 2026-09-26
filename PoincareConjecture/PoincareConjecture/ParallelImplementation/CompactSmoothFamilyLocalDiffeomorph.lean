import DoCarmoLib.Riemannian.Manifold.DoCarmoCh0
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CompactSmoothFamilyLocalDiffeomorph
open Riemannian Set
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
/-- A compact jointly smooth family equal to the identity at time zero is
locally diffeomorphic on one uniform short interval. Invertibility is derived,
not assumed; global bijectivity may then be supplied by actual ODE identities. -/
theorem exists_uniform_local_diffeomorph_window [CompactSpace M]
    (F : M × ℝ → M) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) I ∞ F
      ((Set.univ : Set M) ×ˢ Set.Ioo (-epsilon) epsilon))
    (hzero : ∀ p : M, F (p, 0) = p) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ epsilon ∧
      ∀ t ∈ Set.Ioo (-delta) delta,
        IsLocalDiffeomorph I I ∞ (fun p : M => F (p, t)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  have hlocal : ∀ p : M, ∃ U : Set M, ∃ d : ℝ,
      IsOpen U ∧ p ∈ U ∧ 0 < d ∧ d ≤ epsilon ∧
        ∀ q ∈ U, ∀ t ∈ Set.Ioo (-d) d,
          IsLocalDiffeomorphAt I I ∞ (fun x : M => F (x, t)) q := by
    intro p
    let e := extChartAt I p
    let J := 𝓘(ℝ, E)
    let K := J.prod 𝓘(ℝ, ℝ)
    let P : E × ℝ → M × ℝ := fun z => (e.symm z.1, z.2)
    let Q : E × ℝ → M := fun z => F (P z)
    let D₀ : Set (E × ℝ) := e.target ×ˢ Set.Ioo (-epsilon) epsilon
    let D : Set (E × ℝ) := D₀ ∩ Q ⁻¹' e.source
    let G : E × ℝ → E := e ∘ Q
    let A : E × ℝ → E →L[ℝ] E := fun z =>
      fderiv ℝ G z ∘L ContinuousLinearMap.inl ℝ E ℝ
    let z₀ : E × ℝ := (e p, 0)
    have hD₀ : IsOpen D₀ := by
      exact (isOpen_extChartAt_target (I := I) p).prod isOpen_Ioo
    have hP1 : ContMDiffOn K I ∞ (e.symm ∘ Prod.fst) D₀ := by
      apply (contMDiffOn_extChartAt_symm (I := I) p).comp
        (contMDiffOn_fst (I := J) (J := 𝓘(ℝ, ℝ)))
      intro z hz
      exact hz.1
    have hP2 : ContMDiffOn K 𝓘(ℝ, ℝ) ∞ Prod.snd D₀ :=
      contMDiffOn_snd
    have hP : ContMDiffOn K (I.prod 𝓘(ℝ, ℝ)) ∞ P D₀ := by
      simpa [P] using hP1.prodMk hP2
    have hFP : ContMDiffOn K I ∞ Q D₀ := by
      apply hF.comp hP
      intro z hz
      exact ⟨Set.mem_univ _, hz.2⟩
    have hG : ContMDiffOn K J ∞ G D := by
      simpa [G, D, D₀, e, J, extChartAt_source, Function.comp_def] using
        (contMDiffOn_extChartAt (I := I) (x := p)).comp' hFP
    have hQcont : ContinuousOn Q D₀ := hFP.continuousOn
    have hD : IsOpen D := by
      exact hQcont.isOpen_inter_preimage hD₀ (isOpen_extChartAt_source (I := I) p)
    have hz₀D₀ : z₀ ∈ D₀ := by
      constructor
      · exact e.map_source (mem_extChartAt_source (I := I) p)
      · simp only [z₀, Set.mem_Ioo]
        constructor <;> linarith
    have hQz₀ : Q z₀ = p := by
      calc
        Q z₀ = F (e.symm (e p), 0) := by simp [Q, P, z₀]
        _ = e.symm (e p) := hzero _
        _ = p := e.left_inv (mem_extChartAt_source (I := I) p)
    have hz₀D : z₀ ∈ D := by
      refine ⟨hz₀D₀, ?_⟩
      change Q z₀ ∈ e.source
      rw [hQz₀]
      exact mem_extChartAt_source (I := I) p
    have hGcd : ContDiffOn ℝ (∞ : WithTop ℕ∞) G D := by
      rw [contMDiffOn_iff] at hG
      rcases hG with ⟨-, hcoords⟩
      have hcoord := hcoords z₀ (G z₀)
      simpa [K, J, extChartAt, OpenPartialHomeomorph.extend_coe,
        prodChartedSpace_chartAt, chartAt_self_eq,
        OpenPartialHomeomorph.refl_prod_refl, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Function.comp_def] using hcoord
    have hGderivCont : ContinuousOn (fderiv ℝ G) D :=
      hGcd.continuousOn_fderiv_of_isOpen hD (by simp)
    have hAcont : ContinuousOn A D := by
      have hcomp : Continuous (fun L : (E × ℝ) →L[ℝ] E =>
          L ∘L ContinuousLinearMap.inl ℝ E ℝ) := by
        fun_prop
      simpa [A, Function.comp_def] using hcomp.comp_continuousOn hGderivCont
    have hA₀ : A z₀ = ContinuousLinearMap.id ℝ E := by
      let U₀ : Set E := {u | (u, 0) ∈ D}
      have hU₀open : IsOpen U₀ := by
        exact hD.preimage (continuous_id.prodMk continuous_const)
      have hu₀U₀ : e p ∈ U₀ := by
        exact hz₀D
      have hU₀nhds : U₀ ∈ 𝓝 (e p) := hU₀open.mem_nhds hu₀U₀
      let g₀ : E → E := fun u => G (u, 0)
      have hg₀id : g₀ =ᶠ[𝓝 (e p)] id := by
        filter_upwards [hU₀nhds] with u hu
        have hD' : (u, 0) ∈ D := hu
        have huTarget : u ∈ e.target := hD'.1.1
        have hFsrc : F (e.symm u, 0) ∈ e.source := by
          simpa [Q, P] using hD'.2
        calc
          g₀ u = e (F (e.symm u, 0)) := by rfl
          _ = e (e.symm u) := by rw [hzero]
          _ = u := e.right_inv huTarget
      have hg₀deriv : HasFDerivAt g₀ (A z₀) (e p) := by
        have hGat : HasFDerivAt G (fderiv ℝ G z₀) z₀ :=
          ((hGcd.contDiffAt (hD.mem_nhds hz₀D)).differentiableAt (by simp)).hasFDerivAt
        have hi : HasFDerivAt (fun u : E => (u, (0 : ℝ)))
            (ContinuousLinearMap.inl ℝ E ℝ) (e p) := by
          simpa [ContinuousLinearMap.inl, ContinuousLinearMap.prod] using
            (hasFDerivAt_id (e p)).prodMk (hasFDerivAt_const (0 : ℝ) (e p))
        change HasFDerivAt G (fderiv ℝ G (e p, 0)) (e p, 0) at hGat
        simpa [g₀, A, z₀, Function.comp_def] using
          HasFDerivAt.comp (x := e p) hGat hi
      have hg₀idderiv : HasFDerivAt g₀ (ContinuousLinearMap.id ℝ E) (e p) :=
        (hg₀id.hasFDerivAt_iff).2 (hasFDerivAt_id (e p))
      exact hg₀deriv.unique hg₀idderiv
    let S : Set (E × ℝ) := D ∩ A ⁻¹' Set.range (ContinuousLinearEquiv.toContinuousLinearMap)
    have hSopen : IsOpen S := by
      exact hAcont.isOpen_inter_preimage hD ContinuousLinearEquiv.isOpen
    have hz₀S : z₀ ∈ S := by
      refine ⟨hz₀D, ?_⟩
      change A z₀ ∈ Set.range ContinuousLinearEquiv.toContinuousLinearMap
      rw [hA₀]
      exact ⟨ContinuousLinearEquiv.refl ℝ E, rfl⟩
    have hz₀Snhds : S ∈ 𝓝 z₀ := hSopen.mem_nhds hz₀S
    obtain ⟨U₀', hU₀'nhds, T₀', hT₀'nhds, hbox⟩ :=
      mem_nhds_prod_iff.mp hz₀Snhds
    obtain ⟨Ue, hUesub, hUeopen, hu₀Ue⟩ := mem_nhds_iff.mp hU₀'nhds
    obtain ⟨r, hrpos, hrball⟩ := Metric.mem_nhds_iff.mp hT₀'nhds
    let d := min r epsilon
    have hdpos : 0 < d := lt_min hrpos hepsilon
    have hdr : d ≤ r := min_le_left _ _
    have hde : d ≤ epsilon := min_le_right _ _
    let U : Set M := e.source ∩ e ⁻¹' Ue
    have hUopen : IsOpen U := by
      simpa [U, e] using isOpen_extChartAt_preimage (I := I) p hUeopen
    have hpU : p ∈ U := by
      refine ⟨mem_extChartAt_source (I := I) p, ?_⟩
      exact hu₀Ue
    have hlocalAt : ∀ q ∈ U, ∀ t ∈ Set.Ioo (-d) d,
        IsLocalDiffeomorphAt I I ∞ (fun x : M => F (x, t)) q := by
      intro q hqU t ht
      have huU : e q ∈ Ue := hqU.2
      have htT : t ∈ T₀' := by
        apply hrball
        rw [Metric.mem_ball, Real.dist_eq]
        apply abs_lt.mpr
        constructor
        · simpa using (neg_le_neg hdr).trans_lt ht.1
        · simpa using ht.2.trans_le hdr
      have hboxmem : (e q, t) ∈ U₀' ×ˢ T₀' := ⟨hUesub huU, htT⟩
      have hzS : (e q, t) ∈ S := hbox hboxmem
      let u := e q
      let z := (u, t)
      have hzS' : z ∈ S := by simpa [u, z] using hzS
      have hzD : z ∈ D := hzS'.1
      have hqleft : e.symm (e q) = q := e.left_inv hqU.1
      have hQeq : Q z = F (q, t) := by
        simp [Q, P, z, u, hqleft]
      have hFsource : F (q, t) ∈ e.source := by
        rw [← hQeq]
        exact hzD.2
      let U_t : Set E := {v | (v, t) ∈ D}
      have hUtop : IsOpen U_t := by
        exact hD.preimage (continuous_id.prodMk continuous_const)
      have huUt : u ∈ U_t := by
        exact hzD
      let g_t : E → E := fun v => G (v, t)
      have hgt : ContDiffOn ℝ (∞ : WithTop ℕ∞) g_t U_t := by
        have hins : ContDiffOn ℝ (∞ : WithTop ℕ∞) (fun v : E => (v, t)) U_t :=
          contDiffOn_id.prodMk contDiffOn_const
        have hmaps : MapsTo (fun v : E => (v, t)) U_t D := fun _ hv => hv
        simpa [g_t, Function.comp_def] using hGcd.comp hins hmaps
      obtain ⟨g', hg'⟩ := hzS'.2
      have hGat : HasFDerivAt G (fderiv ℝ G z) z :=
        ((hGcd.contDiffAt (hD.mem_nhds hzD)).differentiableAt (by simp)).hasFDerivAt
      have hinsderiv : HasFDerivAt (fun v : E => (v, t))
          (ContinuousLinearMap.inl ℝ E ℝ) u := by
        simpa [ContinuousLinearMap.inl, ContinuousLinearMap.prod] using
          (hasFDerivAt_id u).prodMk (hasFDerivAt_const t u)
      have hgtderiv : HasFDerivAt g_t (g' : E →L[ℝ] E) u := by
        change HasFDerivAt G (fderiv ℝ G (u, t)) (u, t) at hGat
        have h := HasFDerivAt.comp (x := u) hGat hinsderiv
        simpa [g_t, A, z, hg', Function.comp_def] using h
      have hgtlocal : IsLocalDiffeomorphAt J J ∞ g_t u :=
        Riemannian.isLocalDiffeomorphAt_of_hasFDerivAt_equiv
          hUtop huUt hgt hgtderiv
      obtain ⟨ψ, huψ, hψeq⟩ := hgtlocal
      let ψo := ψ.toOpenPartialHomeomorph.restrOpen U_t hUtop
      let ψ' : PartialDiffeomorph J J E E ∞ := {
        toPartialEquiv := ψo.toPartialEquiv
        open_source := ψo.open_source
        open_target := ψo.open_target
        contMDiffOn_toFun := by
          have hs : ψo.source ⊆ ψ.source := by
            rw [OpenPartialHomeomorph.restrOpen_source]
            exact inter_subset_left
          simpa [ψo] using ψ.contMDiffOn_toFun.mono hs
        contMDiffOn_invFun := by
          have ht' : ψo.target ⊆ ψ.target := by
            change (ψ.toPartialEquiv.restr U_t).target ⊆ ψ.target
            rw [PartialEquiv.restr_target]
            exact inter_subset_left
          have hcont := ψ.contMDiffOn_invFun.mono ht'
          simpa [ψo, OpenPartialHomeomorph.restrOpen_toPartialEquiv] using hcont
      }
      have hψ'source : u ∈ ψ'.source := by
        change u ∈ ψ.source ∩ U_t
        exact ⟨huψ, huUt⟩
      have hψ'sub : ψ'.source ⊆ U_t := by
        change ψo.source ⊆ U_t
        rw [OpenPartialHomeomorph.restrOpen_source]
        exact inter_subset_right
      have hψ'eq : EqOn g_t ψ' ψ'.source := by
        intro v hv
        have hv' : v ∈ ψ.source := by
          have hh := hv
          change v ∈ ψo.source at hh
          rw [OpenPartialHomeomorph.restrOpen_source] at hh
          exact hh.1
        have heq := hψeq hv'
        change g_t v = ψ' v
        have hψval : ψ' v = ψ v := by
          change ψo.toPartialEquiv v = ψ.toPartialEquiv v
          rfl
        exact heq.trans hψval.symm
      let χ : PartialDiffeomorph I J M E ∞ := {
        toPartialEquiv := e
        open_source := by simpa [e] using isOpen_extChartAt_source (I := I) p
        open_target := by simpa [e] using isOpen_extChartAt_target (I := I) p
        contMDiffOn_toFun := by
          simpa [e, extChartAt_source] using
            (contMDiffOn_extChartAt (I := I) (x := p))
        contMDiffOn_invFun := by
          simpa [e] using contMDiffOn_extChartAt_symm (I := I) p
      }
      let Θ := (χ.trans ψ').trans χ.symm
      have hqχ : q ∈ χ.source := by simpa [χ] using hqU.1
      have hχq : χ q = u := rfl
      have hψout : ψ' u ∈ χ.target := by
        have huEq : ψ' u = g_t u := (hψ'eq hψ'source).symm
        rw [huEq]
        have hGue : G (u, t) = e (F (q, t)) := by
          simp [G, Q, P, u, hqleft]
        rw [show g_t u = G (u, t) from rfl, hGue]
        exact e.map_source hFsource
      have hΘsource : q ∈ Θ.source := by
        simpa [Θ, PartialEquiv.trans_source, PartialEquiv.symm_source,
          Set.mem_inter_iff, Set.mem_preimage, PartialEquiv.trans_apply,
          hχq] using And.intro (And.intro hqχ hψ'source) hψout
      have hΘeq : EqOn (fun x : M => F (x, t)) Θ Θ.source := by
        intro x hx
        have hxdata' : (x ∈ χ.source ∧ χ x ∈ ψ'.source) ∧
            ψ' (χ x) ∈ χ.target := by
          simpa [Θ, PartialEquiv.trans_source, PartialEquiv.symm_source,
            Set.mem_inter_iff, Set.mem_preimage, PartialEquiv.trans_apply] using hx
        rcases hxdata' with ⟨⟨hxχ, hxψ⟩, hxout⟩
        have hxdata : x ∈ χ.source ∧ χ x ∈ ψ'.source ∧
            ψ' (χ x) ∈ χ.target := ⟨hxχ, hxψ, hxout⟩
        have hxUt : (χ x, t) ∈ D := hψ'sub hxdata.2.1
        have hxleft : e.symm (e x) = x := by
          have hxχ : x ∈ e.source := by simpa [χ] using hxdata.1
          exact e.left_inv hxχ
        have hQx : Q (χ x, t) = F (x, t) := by
          simp [Q, P, χ, hxleft]
        have hxFsource : F (x, t) ∈ e.source := by
          rw [← hQx]
          exact hxUt.2
        have hGx : G (χ x, t) = e (F (x, t)) := by
          simp [G, hQx]
        have hψx : ψ' (χ x) = e (F (x, t)) := by
          calc
            ψ' (χ x) = g_t (χ x) := (hψ'eq hxdata.2.1).symm
            _ = G (χ x, t) := rfl
            _ = e (F (x, t)) := hGx
        calc
          F (x, t) = e.symm (e (F (x, t))) := (e.left_inv hxFsource).symm
          _ = e.symm (ψ' (χ x)) := by rw [hψx]
          _ = Θ x := by simp [Θ, χ, PartialEquiv.trans_apply]
      exact ⟨Θ, hΘsource, hΘeq⟩
    refine ⟨U, d, hUopen, hpU, hdpos, hde, ?_⟩
    intro q hq t ht
    exact hlocalAt q hq t ht
  by_cases hNonempty : ∃ p : M, True
  · letI : Nonempty M := ⟨Classical.choose hNonempty⟩
    choose U d hUopen hUmem hdpos hdle hproperty using hlocal
    obtain ⟨s, hscover⟩ := isCompact_univ.elim_finite_subcover U hUopen (by
      intro x hx
      exact Set.mem_iUnion.2 ⟨x, hUmem x⟩)
    have hsne : s.Nonempty := by
      obtain ⟨x, -⟩ := hNonempty
      obtain ⟨i, hi, hxUi⟩ := Set.mem_iUnion₂.mp (hscover (Set.mem_univ x))
      exact ⟨i, hi⟩
    let delta := s.inf' hsne d
    have hdeltaPos : 0 < delta := by
      rw [Finset.lt_inf'_iff hsne]
      intro i hi
      exact hdpos i
    have hdeltaLe : delta ≤ epsilon := by
      obtain ⟨i, hi⟩ := hsne
      exact (Finset.inf'_le d hi).trans (hdle i)
    refine ⟨delta, hdeltaPos, hdeltaLe, ?_⟩
    intro t ht x
    obtain ⟨i, hi, hxUi⟩ := Set.mem_iUnion₂.mp (hscover (Set.mem_univ x))
    have ht' : t ∈ Set.Ioo (-(d i)) (d i) := by
      constructor
      · exact (neg_le_neg (Finset.inf'_le d hi)).trans_lt ht.1
      · exact ht.2.trans_le (Finset.inf'_le d hi)
    exact hproperty i x hxUi t ht'
  · refine ⟨epsilon, hepsilon, le_rfl, ?_⟩
    intro t ht x
    exact False.elim (hNonempty ⟨x, trivial⟩)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.CompactSmoothFamilyLocalDiffeomorph
