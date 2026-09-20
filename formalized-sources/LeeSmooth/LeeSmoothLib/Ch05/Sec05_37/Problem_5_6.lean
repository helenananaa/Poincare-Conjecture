import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.SmoothEmbedding
import LeeSmoothLib.Ch03.Sec03_17.Proposition_3_24
import LeeSmoothLib.Ch04.Sec04_21.Definition_4_21_extra_1
import LeeSmoothLib.Ch04.Sec04_24.Exercise_4_16
import LeeSmoothLib.Ch04.Sec04_24.Theorem_4_25
import LeeSmoothLib.Ch05.Sec05_28.Definition_5_28_extra_1
import LeeSmoothLib.Ch05.Sec05_36.Definition_5_36_extra_3
import LeeSmoothLib.Verified.LevelSets.RegularValue
import LeeSmoothLib.Ch05.Sec05_37.Problem_5_6_SelfModel
-- Declarations for this item will be appended below by the statement pipeline.
-- Semantic search tool unavailable in this environment; local mathlib and repository APIs were
-- checked directly for the tangent-space and tangent-bundle surface used below.

open Manifold Set Function Topology
open scoped ContDiff Manifold Topology

noncomputable section

-- The tangent-bundle manifold structure already supplies the intended topology.  Removing this
-- redundant generic instance avoids a topology diamond on Euclidean model spaces below.
attribute [-instance] TopCat.of.chartedSpace

/-- Lowering the differentiability order preserves a smooth embedding.  This is the specialized
copy of the verified helper from Proposition 5.49, kept here to avoid a dependency on later
material from the section. -/
private lemma problem_5_6_isSmoothEmbedding_of_le
    {𝕜 E E' H H' M N : Type*}
    [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
    {n m : ℕ∞ω} {f : N → M} (hmn : m ≤ n)
    (hf : IsSmoothEmbedding I' I n f) :
    IsSmoothEmbedding I' I m f := by
  let hImm := hf.isImmersion
  let hComp := hImm.complement
  let hCompImm := hImm.isImmersionOfComplement_complement
  refine ⟨?_, hf.isEmbedding⟩
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I') (M := N) hmn)
      hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M) hmn)
      hx.codChart_mem_maximalAtlas

section UnitTangentBundle

variable (n m : ℕ)
variable (S : Set (EuclideanSpace ℝ (Fin n)))
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) S]

/-- The unit tangent bundle of the embedded submanifold `S`, owned intrinsically as the unit-norm
locus in `TS`, where the norm is measured after applying the canonical tangent map of the subtype
inclusion `S ↪ ℝ^n`. -/
def unitTangentBundle :=
  { v : TangentBundle (𝓡 m) S |
      let w := tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v
      ‖NormedSpace.fromTangentSpace w.proj w.2‖ = 1 }

namespace unitTangentBundle

/-- The canonical inclusion of the unit tangent bundle into the ambient tangent bundle `Tℝ^n`. -/
def inclusion :
    unitTangentBundle n m S → TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n)) :=
  tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) ∘ Subtype.val

/-- Under the canonical inclusion into the ambient tangent bundle, a point of the unit tangent
bundle has ambient tangent norm `1`. -/
@[simp] theorem norm_eq_one
    (v : unitTangentBundle n m S) :
    ‖NormedSpace.fromTangentSpace
        (inclusion n m S v).proj
        (inclusion n m S v).2‖ = 1 := by
  exact v.2

end unitTangentBundle

end UnitTangentBundle

section EmbeddedUnitTangentBundle

variable (n m : ℕ)
variable (S : Set (EuclideanSpace ℝ (Fin n)))
variable [ChartedSpace (EuclideanSpace ℝ (Fin m)) S]
variable [IsManifold (𝓡 m) (∞ : ℕ∞ω) S]
variable [IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) S]

/-- The squared ambient norm of an intrinsic tangent vector. -/
private def problem_5_6_energy (v : TangentBundle (𝓡 m) S) : ℝ :=
  let w := tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v
  ‖NormedSpace.fromTangentSpace w.proj w.2‖ ^ 2

private lemma problem_5_6_energy_smooth
    (h : ContMDiff (𝓡 m) (𝓡 n) ∞ ((↑) : S → EuclideanSpace ℝ (Fin n))) :
    ContMDiff (𝓡 m).tangent 𝓘(ℝ) ∞ (problem_5_6_energy n m S) := by
  have hT : ContMDiff (𝓡 m).tangent (𝓡 n).tangent ∞
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n))) :=
    h.contMDiff_tangentMap (by simp)
  have hsnd :=
    (contMDiff_snd_tangentBundle_modelSpace
      (EuclideanSpace ℝ (Fin n)) (𝓡 n) :
        ContMDiff (𝓡 n).tangent (𝓡 n) ∞
          (fun p : TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n)) => p.2))
  have hnorm : ContMDiff (𝓡 n) 𝓘(ℝ) ∞
      (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2) := by
    rw [contMDiff_iff_contDiff]
    exact contDiff_norm_sq ℝ
  simpa only [problem_5_6_energy] using! (hnorm.comp (hsnd.comp hT))

/-- Radial scaling in one tangent-space fibre. -/
private def problem_5_6_radialCurve (v : TangentBundle (𝓡 m) S) (t : ℝ) :
    TangentBundle (𝓡 m) S :=
  ⟨v.proj, (1 + t) • v.2⟩

private lemma problem_5_6_radialCurve_smooth (v : TangentBundle (𝓡 m) S) :
    ContMDiff 𝓘(ℝ) (𝓡 m).tangent ∞ (problem_5_6_radialCurve n m S v) := by
  intro t
  rw [Bundle.contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_const, ?_⟩
  letI : FiniteDimensional ℝ (TangentSpace (𝓡 m) v.proj) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin m)))
  let e := trivializationAt (EuclideanSpace ℝ (Fin m))
    (TangentSpace (𝓡 m)) v.proj
  let hv : v.proj ∈ e.baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' v.proj
  let L : TangentSpace (𝓡 m) v.proj →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (e.linearEquivAt ℝ v.proj hv).toContinuousLinearMap
  have hscalar : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => 1 + t) t :=
    contMDiffAt_const.add contMDiffAt_id
  have hvec : ContMDiffAt 𝓘(ℝ) (𝓡 m) ∞
      (fun t : ℝ => (1 + t) • L v.2) t :=
    hscalar.smul contMDiffAt_const
  have hfun :
      (fun s : ℝ => (e ⟨v.proj, (1 + s) • v.2⟩).2) =
        (fun s : ℝ => (1 + s) • L v.2) := by
    funext s
    rw [← e.linearEquivAt_apply (R := ℝ) v.proj hv]
    exact (e.linearEquivAt ℝ v.proj hv).map_smul (1 + s) v.2
  change ContMDiffAt 𝓘(ℝ) (𝓡 m) ∞
    (fun s : ℝ => (e ⟨v.proj, (1 + s) • v.2⟩).2) t
  rw [hfun]
  simpa +instances using! hvec

private lemma problem_5_6_energy_radialCurve
    (v : TangentBundle (𝓡 m) S) (hv : problem_5_6_energy n m S v = 1) (t : ℝ) :
    problem_5_6_energy n m S (problem_5_6_radialCurve n m S v t) = (1 + t) ^ 2 := by
  have hv' :
      ‖NormedSpace.fromTangentSpace (v.proj : EuclideanSpace ℝ (Fin n))
        (mfderiv (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v.proj v.2)‖ ^ 2 = 1 := by
    simpa only [problem_5_6_energy, tangentMap] using! hv
  simp only [problem_5_6_energy, problem_5_6_radialCurve, tangentMap, tangentMap_snd,
    map_smul]
  rw [norm_smul, mul_pow, hv']
  simp [Real.norm_eq_abs, sq_abs]

/-- The value `1` is regular because radial scaling differentiates the energy to `2`. -/
private lemma problem_5_6_energy_regular
    (hEmb : IsSmoothEmbedding (𝓡 m) (𝓡 n) ∞
      ((↑) : S → EuclideanSpace ℝ (Fin n))) :
    Manifold.IsRegularValue (𝓡 m).tangent 𝓘(ℝ) (problem_5_6_energy n m S) 1 := by
  intro v hv
  let γ : ℝ → TangentBundle (𝓡 m) S := problem_5_6_radialCurve n m S v
  let z : TangentSpace (𝓡 m).tangent v := curve_velocity (𝓡 m).tangent γ 0
  have hγ : ContMDiff 𝓘(ℝ) (𝓡 m).tangent ∞ γ :=
    problem_5_6_radialCurve_smooth n m S v
  have hγ0 : γ 0 = v := by
    rcases v with ⟨x, u⟩
    simp [γ, problem_5_6_radialCurve]
  have hcomp : problem_5_6_energy n m S ∘ γ = fun t : ℝ => (1 + t) ^ 2 := by
    funext t
    exact problem_5_6_energy_radialCurve n m S v hv t
  have hvel :
      NormedSpace.fromTangentSpace ((problem_5_6_energy n m S ∘ γ) 0)
        (curve_velocity 𝓘(ℝ) (problem_5_6_energy n m S ∘ γ) 0) = 2 := by
    rw [hcomp, curve_velocity, mfderiv_eq_fderiv]
    change fderiv ℝ (fun t : ℝ => (1 + t) ^ 2) 0 1 = 2
    have hd := (((hasDerivAt_const (x := 0) (c := (1 : ℝ))).add
      (hasDerivAt_id (x := 0))).pow 2)
    have hfunpow : (fun t : ℝ => (1 + t) ^ 2) = (((fun _ : ℝ => (1 : ℝ)) + id) ^ 2) := by
      rfl
    rw [fderiv_eq_deriv_mul, hfunpow, hd.deriv]
    norm_num
  have hchain :
      mfderiv (𝓡 m).tangent 𝓘(ℝ) (problem_5_6_energy n m S) v z =
        curve_velocity 𝓘(ℝ) (problem_5_6_energy n m S ∘ γ) 0 := by
    have hc := composite_curve_velocity (J := Set.univ) (t₀ := 0)
      (F := problem_5_6_energy n m S) (γ := γ)
      (uniqueMDiffWithinAt_univ (I := 𝓘(ℝ)))
      ((problem_5_6_energy_smooth n m S hEmb.contMDiff).mdifferentiableAt (by simp))
      (hγ.mdifferentiableAt (by simp))
    rw [hγ0] at hc
    simpa [curve_velocityWithin, curve_velocity, z] using hc.symm
  let eout : TangentSpace 𝓘(ℝ) (problem_5_6_energy n m S v) ≃L[ℝ] ℝ :=
    NormedSpace.fromTangentSpace (𝕜 := ℝ) (problem_5_6_energy n m S v)
  have hvel' : eout (curve_velocity 𝓘(ℝ)
      (problem_5_6_energy n m S ∘ γ) 0) = 2 := by
    rw [Function.comp_apply, hγ0] at hvel
    simpa +instances [eout] using! hvel
  have hdz : eout (mfderiv (𝓡 m).tangent 𝓘(ℝ)
      (problem_5_6_energy n m S) v z) = 2 := by
    rw [hchain]
    exact hvel'
  intro y
  refine ⟨(eout y / 2) • z, ?_⟩
  apply eout.injective
  rw [map_smul, map_smul, hdz]
  simp [eout]

private lemma problem_5_6_unit_eq_level :
    unitTangentBundle n m S =
      (problem_5_6_energy n m S) ⁻¹' ({1} : Set ℝ) := by
  ext v
  change
    ‖NormedSpace.fromTangentSpace
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v).proj
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v).2‖ = 1 ↔
    ‖NormedSpace.fromTangentSpace
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v).proj
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v).2‖ ^ 2 = 1
  have hnonneg : 0 ≤ ‖NormedSpace.fromTangentSpace
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v).proj
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v).2‖ := norm_nonneg _
  constructor <;> intro h <;> nlinarith

/-- A local `C²` map induces a local `C¹` tangent map. -/
private lemma problem_5_6_tangentMap_contMDiffAt_of_contMDiffAt_two
    {E E' H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H] [TopologicalSpace H']
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
    [IsManifold I 2 M] [IsManifold J 2 N]
    {f : M → N} {x : M} (v : TangentSpace I x)
    (hf : ContMDiffAt I J 2 f x) :
    ContMDiffAt I.tangent J.tangent 1 (tangentMap I J f)
      (⟨x, v⟩ : TangentBundle I M) := by
  obtain ⟨u, hu, hfu⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := (2 : ℕ∞ω)) (by simp)).1 hf
  obtain ⟨s, hsu, hsopen, hxs⟩ := mem_nhds_iff.mp hu
  have hfs : ContMDiffOn I J 2 f s := hfu.mono hsu
  have hsUnique : UniqueMDiffOn I s := hsopen.uniqueMDiffOn
  have hwithin : ContMDiffOn I.tangent J.tangent 1
      (tangentMapWithin I J f s) (Bundle.TotalSpace.proj ⁻¹' s) :=
    hfs.contMDiffOn_tangentMapWithin (by norm_num) hsUnique
  have heq : Set.EqOn (tangentMapWithin I J f s) (tangentMap I J f)
      (Bundle.TotalSpace.proj ⁻¹' s) := by
    intro q hq
    exact tangentMapWithin_eq_tangentMap (hsopen.uniqueMDiffWithinAt hq)
      ((hfs q.proj hq).contMDiffAt (hsopen.mem_nhds hq) |>.mdifferentiableAt (by norm_num))
  have hs_nhds : Bundle.TotalSpace.proj ⁻¹' s ∈ 𝓝 (⟨x, v⟩ : TangentBundle I M) :=
    (FiberBundle.continuous_proj E (TangentSpace I)).continuousAt (hsopen.mem_nhds hxs)
  exact (hwithin.congr fun _ hy => (heq hy).symm).contMDiffAt hs_nhds

/-- The tangent map of an embedded Euclidean submanifold is an immersion. -/
private lemma problem_5_6_tangentMap_subtype_isImmersion
    (hEmb : IsSmoothEmbedding (𝓡 m) (𝓡 n) ∞
      ((↑) : S → EuclideanSpace ℝ (Fin n))) :
    IsImmersion (𝓡 m).tangent (𝓡 n).tangent ∞
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n))) := by
  let Tf := tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n))
  have hTf : ContMDiff (𝓡 m).tangent (𝓡 n).tangent ∞ Tf :=
    hEmb.contMDiff.contMDiff_tangentMap (by simp)
  apply (is_immersion_iff_forall_injective_mfderiv hTf).2
  intro q
  let h := hEmb.isImmersion.isImmersionAt q.proj
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) h.complement).comp
      h.equiv.symm.toContinuousLinearMap
  let r : EuclideanSpace ℝ (Fin n) → S := fun y => h.domChart.symm (L (h.codChart y))
  have hr_at (x : S) (hx : x ∈ h.domChart.source) :
      ContMDiffAt (𝓡 n) (𝓡 m) ∞ r (x : EuclideanSpace ℝ (Fin n)) := by
    have hcod : ContMDiffAt (𝓡 n) (𝓡 n) ∞ h.codChart (x : EuclideanSpace ℝ (Fin n)) :=
      contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas
        (h.source_subset_preimage_source hx)
    have hcoord : L (h.codChart (x : EuclideanSpace ℝ (Fin n))) = h.domChart x := by
      have hw := h.writtenInCharts_apply hx
      have hw' : h.codChart (x : EuclideanSpace ℝ (Fin n)) =
          h.equiv (h.domChart x, (0 : h.complement)) := by
        simpa [OpenPartialHomeomorph.extend_coe] using hw
      rw [hw']
      simp [L]
    have htarget : h.domChart x ∈ h.domChart.target := h.domChart.map_source hx
    have hsymm : ContMDiffAt (𝓡 m) (𝓡 m) ∞ h.domChart.symm (h.domChart x) :=
      contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas htarget
    exact hsymm.comp_of_eq (L.contMDiffAt.comp _ hcod) hcoord
  have hrf (x : S) (hx : x ∈ h.domChart.source) :
      r (x : EuclideanSpace ℝ (Fin n)) = x := by
    have hw := h.writtenInCharts_apply hx
    have hcoord : L (h.codChart (x : EuclideanSpace ℝ (Fin n))) = h.domChart x := by
      have hw' : h.codChart (x : EuclideanSpace ℝ (Fin n)) =
          h.equiv (h.domChart x, (0 : h.complement)) := by
        simpa [OpenPartialHomeomorph.extend_coe] using hw
      rw [hw']
      simp [L]
    change h.domChart.symm (L (h.codChart (x : EuclideanSpace ℝ (Fin n)))) = x
    rw [hcoord]
    exact h.domChart.left_inv hx
  have hqsrc : q.proj ∈ h.domChart.source := h.mem_domChart_source
  have hrq : ContMDiffAt (𝓡 n) (𝓡 m) ∞ r (q.proj : EuclideanSpace ℝ (Fin n)) :=
    hr_at q.proj hqsrc
  have hTr : MDifferentiableAt (𝓡 n).tangent (𝓡 m).tangent
      (tangentMap (𝓡 n) (𝓡 m) r) (Tf q) := by
    have hlocal := problem_5_6_tangentMap_contMDiffAt_of_contMDiffAt_two
      (I := 𝓡 n) (J := 𝓡 m) (v := (Tf q).2)
      (hrq.of_le (show (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from ENat.LEInfty.out))
    exact hlocal.mdifferentiableAt (by norm_num)
  have hTfDiff : MDifferentiableAt (𝓡 m).tangent (𝓡 n).tangent Tf q :=
    hTf.mdifferentiableAt (by simp)
  have hleft :
      (tangentMap (𝓡 n) (𝓡 m) r ∘ Tf) =ᶠ[𝓝 q]
        (id : TangentBundle (𝓡 m) S → TangentBundle (𝓡 m) S) := by
    have hopen : IsOpen (Bundle.TotalSpace.proj ⁻¹' h.domChart.source) :=
      h.domChart.open_source.preimage
        (FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin m)) (TangentSpace (𝓡 m)))
    apply (Set.EqOn.eventuallyEq_of_mem _ (hopen.mem_nhds hqsrc))
    intro z hz
    have hfr : (r ∘ ((↑) : S → EuclideanSpace ℝ (Fin n))) =ᶠ[𝓝 z.proj]
        (id : S → S) :=
      (Set.EqOn.eventuallyEq_of_mem (fun x hx => hrf x hx)
        (h.domChart.open_source.mem_nhds hz))
    have hrz := hr_at z.proj hz
    have hcomp := tangentMap_comp_at z
      (hrz.mdifferentiableAt (by simp))
      (hEmb.contMDiff.mdifferentiableAt (by simp))
    change tangentMap (𝓡 n) (𝓡 m) r
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) z) = z
    rw [← hcomp]
    have hcompDiff : MDifferentiableAt (𝓡 m) (𝓡 m)
        (r ∘ ((↑) : S → EuclideanSpace ℝ (Fin n))) z.proj :=
      (hrz.mdifferentiableAt (by simp)).comp z.proj
        (hEmb.contMDiff.mdifferentiableAt (by simp))
    have ht := tangentMapWithin_congr (I := 𝓡 m) (I' := 𝓡 m)
      (s := h.domChart.source)
      (f := r ∘ ((↑) : S → EuclideanSpace ℝ (Fin n))) (f₁ := id)
      (fun x hx => hrf x hx) z hz
    rw [tangentMapWithin_eq_tangentMap
      (h.domChart.open_source.uniqueMDiffWithinAt hz) hcompDiff,
      tangentMapWithin_eq_tangentMap
        (h.domChart.open_source.uniqueMDiffWithinAt hz) mdifferentiableAt_id] at ht
    simpa only [tangentMap_id, id_eq] using ht
  have hderiv_left :
      (mfderiv (𝓡 n).tangent (𝓡 m).tangent (tangentMap (𝓡 n) (𝓡 m) r) (Tf q)).comp
          (mfderiv (𝓡 m).tangent (𝓡 n).tangent Tf q) =
        ContinuousLinearMap.id ℝ _ := by
    rw [← mfderiv_comp q hTr hTfDiff, hleft.mfderiv_eq]
    exact mfderiv_id
  intro a b hab
  have hab' := congrArg
    (mfderiv (𝓡 n).tangent (𝓡 m).tangent (tangentMap (𝓡 n) (𝓡 m) r) (Tf q)) hab
  have ha := DFunLike.congr_fun hderiv_left a
  have hb := DFunLike.congr_fun hderiv_left b
  exact ha.symm.trans (hab'.trans hb)

/-- Near every image point, the tangent map has a continuous left inverse coming from the local
slice projection of the embedded submanifold. -/
private lemma problem_5_6_tangentMap_subtype_local_target_embedding
    (hEmb : IsSmoothEmbedding (𝓡 m) (𝓡 n) ∞
      ((↑) : S → EuclideanSpace ℝ (Fin n)))
    (q : TangentBundle (𝓡 m) S) :
    ∃ W : TopologicalSpace.Opens (TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n))),
      tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) q ∈ W ∧
      IsEmbedding ((W : Set _).restrictPreimage
        (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)))) := by
  let Tf := tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n))
  let h := hEmb.isImmersion.isImmersionAt q.proj
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) h.complement).comp
      h.equiv.symm.toContinuousLinearMap
  let r : EuclideanSpace ℝ (Fin n) → S := fun y => h.domChart.symm (L (h.codChart y))
  let V₀ : Set (EuclideanSpace ℝ (Fin n)) :=
    h.codChart.source ∩ (fun y => L (h.codChart y)) ⁻¹' h.domChart.target
  have hV₀open : IsOpen V₀ := by
    exact ((L.continuous.comp_continuousOn h.codChart.continuousOn).isOpen_inter_preimage
      h.codChart.open_source h.domChart.open_target)
  obtain ⟨V₁, hV₁open, hV₁pre⟩ :=
    hEmb.isEmbedding.isInducing.isOpen_iff.mp h.domChart.open_source
  let V : Set (EuclideanSpace ℝ (Fin n)) := V₀ ∩ V₁
  have hVopen : IsOpen V := hV₀open.inter hV₁open
  have hwritten (x : S) (hx : x ∈ h.domChart.source) :
      h.codChart (x : EuclideanSpace ℝ (Fin n)) =
        h.equiv (h.domChart x, (0 : h.complement)) := by
    simpa [OpenPartialHomeomorph.extend_coe] using h.writtenInCharts_apply hx
  have hcoord (x : S) (hx : x ∈ h.domChart.source) :
      L (h.codChart (x : EuclideanSpace ℝ (Fin n))) = h.domChart x := by
    rw [hwritten x hx]
    simp [L]
  have hF_V₀ (x : S) (hx : x ∈ h.domChart.source) :
      (x : EuclideanSpace ℝ (Fin n)) ∈ V₀ := by
    exact ⟨h.source_subset_preimage_source hx, by
      change L (h.codChart (x : EuclideanSpace ℝ (Fin n))) ∈ h.domChart.target
      rw [hcoord x hx]
      exact h.domChart.map_source hx⟩
  have hqV : (q.proj : EuclideanSpace ℝ (Fin n)) ∈ V := by
    refine ⟨hF_V₀ q.proj h.mem_domChart_source, ?_⟩
    rw [← Set.mem_preimage, hV₁pre]
    exact h.mem_domChart_source
  have hr_mem (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ V) :
      r y ∈ h.domChart.source := by
    exact h.domChart.map_target hy.1.2
  have hrf (x : S) (hx : x ∈ h.domChart.source) :
      r (x : EuclideanSpace ℝ (Fin n)) = x := by
    change h.domChart.symm (L (h.codChart (x : EuclideanSpace ℝ (Fin n)))) = x
    rw [hcoord x hx]
    exact h.domChart.left_inv hx
  have hrOn : ContMDiffOn (𝓡 n) (𝓡 m) ∞ r V := by
    intro y hy
    have hcod : ContMDiffAt (𝓡 n) (𝓡 n) ∞ h.codChart y :=
      contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hy.1.1
    have hsymm : ContMDiffAt (𝓡 m) (𝓡 m) ∞ h.domChart.symm (L (h.codChart y)) :=
      contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas hy.1.2
    have hL : ContMDiffAt (𝓡 n) (𝓡 m) ∞ L (h.codChart y) := by
      rw [contMDiffAt_iff_contDiffAt]
      exact L.contDiff.contDiffAt
    exact ((hsymm.comp _ hL).comp _ hcod).contMDiffWithinAt
  let W : TopologicalSpace.Opens (TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n))) :=
    ⟨Bundle.TotalSpace.proj ⁻¹' V,
      hVopen.preimage (FiberBundle.continuous_proj
        (EuclideanSpace ℝ (Fin n)) (TangentSpace (𝓡 n)))⟩
  have hTrOn : ContinuousOn (tangentMap (𝓡 n) (𝓡 m) r) W := by
    have hwithin := hrOn.continuousOn_tangentMapWithin
      (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from ENat.LEInfty.out) hVopen.uniqueMDiffOn
    apply hwithin.congr
    intro z hz
    exact (tangentMapWithin_eq_tangentMap (hVopen.uniqueMDiffWithinAt hz)
      ((hrOn z.proj hz).contMDiffAt (hVopen.mem_nhds hz) |>.mdifferentiableAt (by simp))).symm
  have hTrTf (z : TangentBundle (𝓡 m) S) (hz : z.proj ∈ h.domChart.source) :
      tangentMap (𝓡 n) (𝓡 m) r (Tf z) = z := by
    have hrz : ContMDiffAt (𝓡 n) (𝓡 m) ∞ r
        (z.proj : EuclideanSpace ℝ (Fin n)) := by
      have hFzV₀ := hF_V₀ z.proj hz
      have hcod : ContMDiffAt (𝓡 n) (𝓡 n) ∞ h.codChart
          (z.proj : EuclideanSpace ℝ (Fin n)) :=
        contMDiffAt_of_mem_maximalAtlas h.codChart_mem_maximalAtlas hFzV₀.1
      have hsymm : ContMDiffAt (𝓡 m) (𝓡 m) ∞ h.domChart.symm
          (L (h.codChart (z.proj : EuclideanSpace ℝ (Fin n)))) := by
        rw [hcoord z.proj hz]
        exact contMDiffAt_symm_of_mem_maximalAtlas h.domChart_mem_maximalAtlas
          (h.domChart.map_source hz)
      have hL : ContMDiffAt (𝓡 n) (𝓡 m) ∞ L
          (h.codChart (z.proj : EuclideanSpace ℝ (Fin n))) := by
        rw [contMDiffAt_iff_contDiffAt]
        exact L.contDiff.contDiffAt
      exact (hsymm.comp _ hL).comp _ hcod
    have hcomp := tangentMap_comp_at z
      (hrz.mdifferentiableAt (by simp))
      (hEmb.contMDiff.mdifferentiableAt (by simp))
    change tangentMap (𝓡 n) (𝓡 m) r
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) z) = z
    rw [← hcomp]
    have hcompDiff : MDifferentiableAt (𝓡 m) (𝓡 m)
        (r ∘ ((↑) : S → EuclideanSpace ℝ (Fin n))) z.proj :=
      (hrz.mdifferentiableAt (by simp)).comp z.proj
        (hEmb.contMDiff.mdifferentiableAt (by simp))
    have ht := tangentMapWithin_congr (I := 𝓡 m) (I' := 𝓡 m)
      (s := h.domChart.source)
      (f := r ∘ ((↑) : S → EuclideanSpace ℝ (Fin n))) (f₁ := id)
      (fun x hx => hrf x hx) z hz
    rw [tangentMapWithin_eq_tangentMap
      (h.domChart.open_source.uniqueMDiffWithinAt hz) hcompDiff,
      tangentMapWithin_eq_tangentMap
        (h.domChart.open_source.uniqueMDiffWithinAt hz) mdifferentiableAt_id] at ht
    simpa only [tangentMap_id, id_eq] using ht
  let inv : W → Tf ⁻¹' W := fun z => ⟨tangentMap (𝓡 n) (𝓡 m) r z.1, by
    have hrU : r z.1.proj ∈ h.domChart.source := hr_mem z.1.proj z.2
    change Tf (tangentMap (𝓡 n) (𝓡 m) r z) ∈ W
    change ((r z.1.proj : S) : EuclideanSpace ℝ (Fin n)) ∈ V
    refine ⟨hF_V₀ (r z.1.proj) hrU, ?_⟩
    rw [← Set.mem_preimage, hV₁pre]
    exact hrU⟩
  have hinv_cont : Continuous inv := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_restrict.mp hTrOn
  have hleftInv : Function.LeftInverse inv ((W : Set _).restrictPreimage Tf) := by
    intro z
    apply Subtype.ext
    exact hTrTf z.1 (by
      have hzV₁ : (z.1.proj : EuclideanSpace ℝ (Fin n)) ∈ V₁ := z.2.2
      rw [← Set.mem_preimage, hV₁pre] at hzV₁
      exact hzV₁)
  refine ⟨W, hqV, ?_⟩
  have hTfSmooth : ContMDiff (𝓡 m).tangent (𝓡 n).tangent ∞ Tf :=
    hEmb.contMDiff.contMDiff_tangentMap (by simp)
  exact hleftInv.isEmbedding hinv_cont hTfSmooth.continuous.restrictPreimage

private lemma problem_5_6_tangentMap_subtype_isEmbedding
    (hEmb : IsSmoothEmbedding (𝓡 m) (𝓡 n) ∞
      ((↑) : S → EuclideanSpace ℝ (Fin n))) :
    IsEmbedding
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n))) := by
  let Tf := tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n))
  have hTfSmooth : ContMDiff (𝓡 m).tangent (𝓡 n).tangent ∞ Tf :=
    hEmb.contMDiff.contMDiff_tangentMap (by simp)
  choose W hqW hW using fun q =>
    problem_5_6_tangentMap_subtype_local_target_embedding n m S hEmb q
  refine isEmbedding_of_iSup_eq_top_of_preimage_subset_range Tf hTfSmooth.continuous W ?_
      (fun q => Tf ⁻¹' (W q : Set _)) (fun _ => Subtype.val) ?_ ?_ ?_
  · intro y hy
    rcases hy with ⟨q, rfl⟩
    exact (show W q ≤ ⨆ i, W i from le_iSup W q) (hqW q)
  · intro q
    exact continuous_subtype_val
  · intro q z hz
    exact ⟨⟨z, hz⟩, rfl⟩
  · intro q
    have hrestrict := hW q
    simpa [Tf, Set.restrictPreimage, Function.comp_def] using
      IsEmbedding.subtypeVal.comp hrestrict

private lemma problem_5_6_tangentMap_subtype_isSmoothEmbedding
    (hEmb : IsSmoothEmbedding (𝓡 m) (𝓡 n) ∞
      ((↑) : S → EuclideanSpace ℝ (Fin n))) :
    IsSmoothEmbedding (𝓡 m).tangent (𝓡 n).tangent ∞
      (tangentMap (𝓡 m) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n))) :=
  ⟨problem_5_6_tangentMap_subtype_isImmersion n m S hEmb,
    problem_5_6_tangentMap_subtype_isEmbedding n m S hEmb⟩

-- Proof sketch: work in local slice coordinates for the embedded submanifold. There the tangent
-- bundle of `S` identifies with `U × ℝ^m`, and the unit condition cuts out `U × S^{m-1}`. The
-- standard sphere charts then supply a smooth `(2m - 1)`-manifold structure, and the canonical
-- inclusion into `Tℝ^n` is a smooth embedding.
/-- Problem 5-6: if `S ⊆ ℝ^n` is a smooth embedded `m`-manifold, then its intrinsic unit tangent
bundle admits a smooth `(2m - 1)`-manifold structure whose canonical inclusion into the ambient
tangent bundle `Tℝ^n` is a smooth embedding. -/
theorem unitTangentBundle_exists_isSmoothEmbedding :
    ∃ cs : ChartedSpace (EuclideanSpace ℝ (Fin (2 * m - 1))) (unitTangentBundle n m S),
      letI := cs
      ∃ hs : IsManifold (𝓡 (2 * m - 1)) (∞ : ℕ∞ω) (unitTangentBundle n m S),
        letI := hs
        IsSmoothEmbedding (𝓡 (2 * m - 1)) (𝓡 n).tangent (∞ : ℕ∞ω)
          (unitTangentBundle.inclusion n m S) := by
  let hEmb : IsSmoothEmbedding (𝓡 m) (𝓡 n) ∞
      ((↑) : S → EuclideanSpace ℝ (Fin n)) :=
    problem_5_6_isSmoothEmbedding_of_le (by simp)
      (inferInstance : IsEmbeddedSubmanifold (𝓡 n) (𝓡 m) S).isSmoothEmbedding_subtype_val
  have hTemb := problem_5_6_tangentMap_subtype_isEmbedding n m S hEmb
  haveI : T2Space
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) :=
    inferInstanceAs
      (T2Space (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
  haveI : SecondCountableTopology
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))) :=
    inferInstanceAs
      (SecondCountableTopology (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
  haveI : T2Space (TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n))) :=
    (tangentBundleModelSpaceHomeomorph (𝓡 n)).isEmbedding.t2Space
  haveI : SecondCountableTopology (TangentBundle (𝓡 n) (EuclideanSpace ℝ (Fin n))) :=
    (tangentBundleModelSpaceHomeomorph (𝓡 n)).isEmbedding.secondCountableTopology
  haveI : T2Space (TangentBundle (𝓡 m) S) := hTemb.t2Space
  haveI : SecondCountableTopology (TangentBundle (𝓡 m) S) := hTemb.secondCountableTopology
  by_cases hm : m = 0
  · subst hm
    have hEmpty : IsEmpty (unitTangentBundle n 0 S) := by
      refine ⟨fun v => ?_⟩
      have hvec : (v.1 : TangentBundle (𝓡 0) S).2 =
          (0 : EuclideanSpace ℝ (Fin 0)) := by
        apply Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0))
      have hnorm :
          ‖NormedSpace.fromTangentSpace
              (tangentMap (𝓡 0) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v.1).proj
              (tangentMap (𝓡 0) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v.1).2‖ = 1 :=
        v.2
      have hzero :
          (tangentMap (𝓡 0) (𝓡 n) ((↑) : S → EuclideanSpace ℝ (Fin n)) v.1).2 = 0 := by
        simp [tangentMap, hvec]
      have : (0 : ℝ) = 1 := by
        simpa [hzero, map_zero] using hnorm
      exact zero_ne_one this
    letI := ChartedSpace.empty (EuclideanSpace ℝ (Fin 0)) (unitTangentBundle n 0 S)
    refine ⟨inferInstance, inferInstance, ?_⟩
    refine ⟨⟨PUnit, inferInstance, inferInstance, fun x => (IsEmpty.false x).elim⟩, ?_⟩
    exact (IsOpenEmbedding.of_isEmpty (unitTangentBundle.inclusion n 0 S)).isEmbedding
  · have hRdim : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ
    have hnm : (1 : ℕ) ≤ 2 * m := by omega
    let instCS := Problem56SelfModel.euclideanChartedSpaceModelProd m
      (TangentBundle (𝓡 m) S)
    let instMan := Problem56SelfModel.euclideanChartedSpaceModelProd_isManifold m
      (TangentBundle (𝓡 m) S)
    let instCSR := Problem56SelfModel.euclideanChartedSpaceSelf (P := ℝ) (F := ℝ)
    let instManR := Problem56SelfModel.euclideanChartedSpaceSelf_isManifold (P := ℝ) (F := ℝ)
    letI : ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) (TangentBundle (𝓡 m) S) := instCS
    letI : IsManifold (𝓡 (2 * m)) ∞ (TangentBundle (𝓡 m) S) := instMan
    letI : ChartedSpace (EuclideanSpace ℝ (Fin (Module.finrank ℝ ℝ))) ℝ := instCSR
    letI : IsManifold (𝓡 (Module.finrank ℝ ℝ)) ∞ ℝ := instManR
    have hΦ :
        ContMDiff (𝓡 (2 * m)) (𝓡 (Module.finrank ℝ ℝ)) ∞
          (problem_5_6_energy n m S) := by
      letI := instCS
      letI := instMan
      letI := instCSR
      letI := instManR
      exact Problem56SelfModel.contMDiff_after_modelProd m
        (problem_5_6_energy_smooth n m S hEmb.contMDiff)
    have hc :
        IsRegularValue (𝓡 (2 * m)) (𝓡 (Module.finrank ℝ ℝ))
          (problem_5_6_energy n m S) 1 := by
      letI := instCS
      letI := instMan
      letI := instCSR
      letI := instManR
      exact Problem56SelfModel.isRegularValue_after_modelProd m
        (problem_5_6_energy_smooth n m S hEmb.contMDiff)
        (problem_5_6_energy_regular n m S hEmb)
    have hnm' : Module.finrank ℝ ℝ ≤ 2 * m := by
      rw [hRdim]
      exact hnm
    have hlevel :=
      LeeVerifiedLevelSets.regular_level_set_has_embedded_submanifold_structure
        (m := 2 * m) (n := Module.finrank ℝ ℝ) hΦ hc hnm'
    have hk : 2 * m - Module.finrank ℝ ℝ = 2 * m - 1 := by rw [hRdim]
    rw [hk] at hlevel
    rw [← problem_5_6_unit_eq_level n m S] at hlevel
    rcases hlevel with ⟨cs, hs, hsub⟩
    refine ⟨cs, hs, ?_⟩
    letI := cs
    letI := hs
    have hT := problem_5_6_tangentMap_subtype_isSmoothEmbedding n m S hEmb
    have hid : IsSmoothEmbedding (𝓡 (2 * m)) (𝓡 m).tangent ∞
        (id : TangentBundle (𝓡 m) S → TangentBundle (𝓡 m) S) :=
      Problem56SelfModel.id_isSmoothEmbedding_modelProd_to_tangent
        (k := m) (Q := TangentBundle (𝓡 m) S)
    have hfiber : IsSmoothEmbedding (𝓡 (2 * m - 1)) (𝓡 (2 * m)) ∞
        (Subtype.val : unitTangentBundle n m S → TangentBundle (𝓡 m) S) := hsub
    have hsub_id :
        IsSmoothEmbedding (𝓡 (2 * m - 1)) (𝓡 m).tangent ∞
          ((id : TangentBundle (𝓡 m) S → TangentBundle (𝓡 m) S) ∘
            (Subtype.val : unitTangentBundle n m S → TangentBundle (𝓡 m) S)) :=
      Manifold.IsSmoothEmbedding.comp (n := ∞) hid hfiber
    simpa [Function.comp, unitTangentBundle.inclusion] using
      Manifold.IsSmoothEmbedding.comp (n := ∞) hT hsub_id

end EmbeddedUnitTangentBundle
