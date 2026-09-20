import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool unavailable in this environment; local precedents used:
-- `Manifold.is_smooth_submersion_iff_forall_surjective_mfderiv` from
-- `Definition_4_21_extra_1` and `Manifold.IsSmoothSubmersion` from `Proposition_4_28`.

noncomputable section

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace Manifold

section

universe uK uE uE' uH uH' uM uN

variable {𝕜 : Type uK} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 E' H'}

/-- A smooth local section of `π : M → N` over an open subset `U ⊆ N` is a smooth map
`σ : U → M` whose composite with `π` is the identity on `U`. -/
def IsSmoothLocalSection (I : ModelWithCorners 𝕜 E H) (J : ModelWithCorners 𝕜 E' H')
    (π : M → N) (U : TopologicalSpace.Opens N) (σ : U → M) : Prop :=
  ContMDiff J I ∞ σ ∧ ∀ x : U, π (σ x) = x

namespace IsSmoothLocalSection

-- Proof sketch: evaluate the defining right-inverse equation in
-- `Manifold.IsSmoothLocalSection` at the chosen point of the open subset.
/-- A smooth local section satisfies the section equation at each point of its domain. -/
theorem apply_eq {π : M → N} {U : TopologicalSpace.Opens N} {σ : U → M}
    (hσ : IsSmoothLocalSection I J π U σ) (x : U) :
    π (σ x) = x :=
  hσ.2 x

end IsSmoothLocalSection

end

section

universe uE uE' uH uH' uM uN

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {J : ModelWithCorners ℝ E' H'} [IsManifold J ∞ N]

set_option linter.unusedSectionVars false

omit [FiniteDimensional ℝ E] in
/-- A surjective continuous linear map into a finite-dimensional space has a continuous-linear
right inverse. -/
theorem exists_continuousLinear_rightInverse {A : E →L[ℝ] E'}
    (hA : Function.Surjective A) :
    ∃ R : E' →L[ℝ] E, ∀ y : E', A (R y) = y := by
  obtain ⟨R₀, hR₀⟩ :=
    (A : E →ₗ[ℝ] E').exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA)
  refine ⟨R₀.toContinuousLinearMap, fun y => ?_⟩
  exact LinearMap.congr_fun hR₀ y

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Affine lifts `y ↦ a + R (y - b)` are `C^∞` with derivative `R`. -/
theorem hasFDerivAt_affineLift (a : E) (R : E' →L[ℝ] E) (b y : E') :
    HasFDerivAt (fun z : E' => a + R (z - b)) R y := by
  have h1 : HasFDerivAt (fun z : E' => z - b) (ContinuousLinearMap.id ℝ E') y :=
    (hasFDerivAt_id y).sub_const b
  have h2 : HasFDerivAt (fun z : E' => R (z - b)) R y := by
    have h := R.hasFDerivAt.comp y h1
    rwa [ContinuousLinearMap.comp_id] at h
  exact h2.const_add a

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
theorem contDiff_affineLift (a : E) (R : E' →L[ℝ] E) (b : E') :
    ContDiff ℝ ∞ (fun z : E' => a + R (z - b)) := by fun_prop

omit [FiniteDimensional ℝ E] in
/-- Euclidean local section theorem with smoothness on an open neighbourhood of `f a`. -/
theorem exists_contDiffOn_localSection_of_surjective_fderiv {f : E → E'} {a : E} {Ω : Set E}
    (hΩ : IsOpen Ω) (haΩ : a ∈ Ω) (hfΩ : ContDiffOn ℝ ∞ f Ω)
    (hsurj : Function.Surjective (fderiv ℝ f a)) :
    ∃ V : Set E', IsOpen V ∧ f a ∈ V ∧ ∃ σ : E' → E,
      ContDiffOn ℝ ∞ σ V ∧ σ (f a) = a ∧ MapsTo σ V Ω ∧ ∀ y ∈ V, f (σ y) = y := by
  set A := fderiv ℝ f a
  obtain ⟨R, hR⟩ := exists_continuousLinear_rightInverse hsurj
  set T : E' → E := fun y => a + R (y - f a)
  have hTb : T (f a) = a := by simp [T]
  have hTdiff : ContDiff ℝ ∞ T := contDiff_affineLift a R (f a)
  have hThas : HasFDerivAt T R (f a) := hasFDerivAt_affineLift a R (f a) (f a)
  set G : E' → E' := fun y => f (T y)
  have hΩT : IsOpen (T ⁻¹' Ω) := hΩ.preimage hTdiff.continuous
  have hfaΩT : f a ∈ T ⁻¹' Ω := by simpa [T] using haΩ
  have hGΩ : ContDiffOn ℝ ∞ G (T ⁻¹' Ω) :=
    hfΩ.comp hTdiff.contDiffOn (fun _ hy => hy)
  have hGAt : ContDiffAt ℝ ∞ G (f a) :=
    (hGΩ (f a) hfaΩT).contDiffAt (hΩT.mem_nhds hfaΩT)
  have hFAt : ContDiffAt ℝ ∞ f a := (hfΩ a haΩ).contDiffAt (hΩ.mem_nhds haΩ)
  have hFhas : HasFDerivAt f A a := (hFAt.differentiableAt (by simp)).hasFDerivAt
  let e : E' ≃L[ℝ] E' := ContinuousLinearEquiv.refl ℝ E'
  have hGhas : HasFDerivAt G (e : E' →L[ℝ] E') (f a) := by
    have hFhas' : HasFDerivAt f A (T (f a)) := by simpa [hTb] using hFhas
    have h := hFhas'.comp (f a) hThas
    have hid : A.comp R = (e : E' →L[ℝ] E') := by
      ext y
      exact hR y
    rwa [hid] at h
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have haInv : (fderiv ℝ G (f a)).IsInvertible := by
    have : fderiv ℝ G (f a) = (e : E' →L[ℝ] E') := hGhas.fderiv
    rw [this]
    exact ContinuousLinearMap.isInvertible_equiv
  obtain ⟨Ψ, hΨsrc, hΨΩ, -, hEq⟩ :=
    model_partialDiffeomorph_of_inverse_function_theorem
      (𝕜 := ℝ) (E := E') (F := E') (g := G) (a := f a) (Ω := T ⁻¹' Ω) (T := univ) (f' := e)
      (hΩT.mem_nhds hfaΩT) hGΩ (fun _ _ => trivial) hGAt hGhas hn haInv
  have hGfa : G (f a) = f a := by simp [G, T]
  have hΨfa : (Ψ : E' → E') (f a) = f a := (hEq hΨsrc).symm.trans hGfa
  have hfaV : f a ∈ Ψ.target := by
    rw [← hΨfa]
    exact Ψ.map_source hΨsrc
  refine ⟨Ψ.target, Ψ.open_target, hfaV, T ∘ Ψ.symm, ?_, ?_, ?_, ?_⟩
  · exact hTdiff.comp_contDiffOn Ψ.contMDiffOn_invFun.contDiffOn
  · have hleft : (Ψ.symm : E' → E') (f a) = f a := by
      nth_rw 1 [← hΨfa]
      exact Ψ.left_inv hΨsrc
    change T (Ψ.symm (f a)) = a
    rw [hleft, hTb]
  · intro y hy
    exact hΨΩ (Ψ.map_target hy)
  · intro y hy
    have hGy : G (Ψ.symm y) = y := by
      have hsrc : Ψ.symm y ∈ Ψ.source := Ψ.map_target hy
      exact (hEq hsrc).trans (Ψ.right_inv hy)
    simpa [Function.comp, G] using hGy

/-- A smooth map whose differential at `p` is surjective admits a smooth local section through
`p`, provided the source model is boundaryless (as in Lee's statement of Theorem 4.26). -/
theorem exists_smooth_local_section_of_surjective_mfderiv [I.Boundaryless] {π : M → N}
    (hπ : ContMDiff I J ∞ π) {p : M}
    (hsurj : Function.Surjective (mfderiv I J π p)) :
    ∃ U : TopologicalSpace.Opens N, ∃ hq : π p ∈ U, ∃ σ : U → M,
      IsSmoothLocalSection I J π U σ ∧ σ ⟨π p, hq⟩ = p := by
  set φ := extChartAt I p
  set ψ := extChartAt J (π p)
  set a : E := φ p
  set F : E → E' := writtenInExtChartAt I J p π
  have hFa : F a = ψ (π p) := by
    change ψ (π (φ.symm (φ p))) = ψ (π p)
    rw [φ.left_inv (mem_extChartAt_source (I := I) p)]
  have hΩ :
      ContDiffOn ℝ ∞ F
        (φ.target ∩ (π ∘ φ.symm) ⁻¹' ψ.source) :=
    writtenInExtChartAt_contDiffOn_of_contMDiff (I := I) (J := J) (f := π) (p := p) hπ
  have hΩ_open : IsOpen (φ.target ∩ (π ∘ φ.symm) ⁻¹' ψ.source) := by
    have hφt : IsOpen φ.target := isOpen_extChartAt_target (I := I) p
    have hcont : ContinuousOn (π ∘ φ.symm) φ.target :=
      hπ.continuous.comp_continuousOn
        (contMDiffOn_extChartAt_symm (I := I) (n := ∞) p).continuousOn
    exact hcont.isOpen_inter_preimage hφt (isOpen_extChartAt_source (I := J) (π p))
  have haΩ : a ∈ φ.target ∩ (π ∘ φ.symm) ⁻¹' ψ.source := by
    refine ⟨mem_extChartAt_target (I := I) p, ?_⟩
    change π (φ.symm a) ∈ ψ.source
    have : φ.symm a = p := extChartAt_to_inv (I := I) p
    rw [this]
    exact mem_extChartAt_source (I := J) (π p)
  have hFsurj : Function.Surjective (fderiv ℝ F a) := by
    have hmd : MDifferentiableAt I J π p := hπ.mdifferentiableAt (by simp)
    rw [mfderiv, if_pos hmd, I.range_eq_univ, fderivWithin_univ] at hsurj
    exact hsurj
  obtain ⟨W, hW_open, hψpW, σE, hσE, hσEa, hσEΩ, hσEsec⟩ :=
    exists_contDiffOn_localSection_of_surjective_fderiv
      (f := F) (a := a) hΩ_open haΩ hΩ hFsurj
  have hψcont : ContinuousAt ψ (π p) := continuousAt_extChartAt (I := J) (π p)
  have hψp_memW : ψ (π p) ∈ W := by simpa [hFa] using hψpW
  let U0 : Set N := ψ.source ∩ ψ ⁻¹' W
  have hU0_nhds : U0 ∈ 𝓝 (π p) :=
    Filter.inter_mem (extChartAt_source_mem_nhds (I := J) (π p))
      (hψcont.preimage_mem_nhds (hW_open.mem_nhds hψp_memW))
  obtain ⟨V, hV_sub, hV_open, hπpV⟩ := mem_nhds_iff.mp hU0_nhds
  let U : TopologicalSpace.Opens N := ⟨V, hV_open⟩
  have hq : π p ∈ U := hπpV
  let s : N → M := fun y => φ.symm (σE (ψ y))
  have hs_eq : s (π p) = p := by
    have hσa : σE (ψ (π p)) = a := by simpa [hFa] using hσEa
    change φ.symm (σE (ψ (π p))) = p
    rw [hσa]
    exact extChartAt_to_inv (I := I) p
  have hsec : ∀ y ∈ V, π (s y) = y := by
    intro y hy
    have hyU0 : y ∈ U0 := hV_sub hy
    have hyψ : y ∈ ψ.source := hyU0.1
    have hyW : ψ y ∈ W := hyU0.2
    have hΩy := hσEΩ hyW
    have hysource : π (s y) ∈ ψ.source := hΩy.2
    have hFeq : F (σE (ψ y)) = ψ y := hσEsec (ψ y) hyW
    have hFdef : F (σE (ψ y)) = ψ (π (s y)) := rfl
    refine ψ.injOn hysource hyψ ?_
    rw [← hFeq, hFdef]
  have hsmooth : ContMDiff J I ∞ (fun x : U => s x) := by
    intro x
    have hxU0 : (x : N) ∈ U0 := hV_sub x.2
    have hxψ : (x : N) ∈ ψ.source := hxU0.1
    have hxW : ψ (x : N) ∈ W := hxU0.2
    have hxφ : σE (ψ (x : N)) ∈ φ.target := (hσEΩ hxW).1
    refine (contMDiffAt_subtype_iff (I := J) (I' := I) (U := U) (f := s) (x := x)).mpr ?_
    have h1 : ContMDiffAt J 𝓘(ℝ, E') ∞ ψ (x : N) :=
      contMDiffAt_extChartAt' (I := J) (x := π p) (x' := (x : N)) (by
        simpa [ψ, extChartAt_source] using hxψ)
    have h2 : ContMDiffAt 𝓘(ℝ, E') 𝓘(ℝ, E) ∞ σE (ψ (x : N)) :=
      ((hσE (ψ (x : N)) hxW).contDiffAt (hW_open.mem_nhds hxW)).contMDiffAt
    have h3 : ContMDiffAt 𝓘(ℝ, E) I ∞ φ.symm (σE (ψ (x : N))) :=
      (contMDiffOn_extChartAt_symm (I := I) (n := ∞) p).contMDiffAt
        ((isOpen_extChartAt_target (I := I) p).mem_nhds hxφ)
    exact h3.comp (x : N) (h2.comp (x : N) h1)
  refine ⟨U, hq, fun x : U => s x, ⟨hsmooth, fun x => hsec x x.2⟩, ?_⟩
  simpa [s] using hs_eq

/-- If a smooth local section through `p` exists, then `mfderiv π p` is surjective. -/
theorem surjective_mfderiv_of_exists_smooth_local_section {π : M → N} {p : M}
    (hπ : ContMDiff I J ∞ π)
    (hsec : ∃ U : TopologicalSpace.Opens N, ∃ hq : π p ∈ U, ∃ σ : U → M,
      IsSmoothLocalSection I J π U σ ∧ σ ⟨π p, hq⟩ = p) :
    Function.Surjective (mfderiv I J π p) := by
  classical
  rcases hsec with ⟨U, hq, σ, hσ, hσp⟩
  let s : N → M := fun y => if hy : y ∈ (U : Set N) then σ ⟨y, hy⟩ else p
  have hs_restrict : (fun x : U => s x) = σ := by
    funext x
    simp [s, x.2]
  have hsAt : ContMDiffAt J I ∞ s (π p) :=
    (contMDiffAt_subtype_iff (I := J) (I' := I) (U := U) (f := s)
      (x := ⟨π p, hq⟩)).mp (by
        simpa [hs_restrict] using hσ.1 ⟨π p, hq⟩)
  have hsp : s (π p) = p := by
    simp [s, hq, hσp]
  have hπs : ∀ᶠ y in 𝓝 (π p), π (s y) = y := by
    filter_upwards [U.isOpen.mem_nhds hq] with y hy
    simp only [s, dif_pos hy]
    exact hσ.2 ⟨y, hy⟩
  have hs_mdiff : MDifferentiableAt J I s (π p) := hsAt.mdifferentiableAt (by simp)
  have hπ_mdiff : MDifferentiableAt I J π p := hπ.mdifferentiableAt (by simp)
  have hcomp :
      mfderiv J J (π ∘ s) (π p) =
        (mfderiv I J π (s (π p))).comp (mfderiv J I s (π p)) :=
    mfderiv_comp (π p) (by simpa [hsp] using hπ_mdiff) hs_mdiff
  have hid : mfderiv J J (π ∘ s) (π p) = ContinuousLinearMap.id ℝ (TangentSpace J (π p)) := by
    have hEq : (π ∘ s) =ᶠ[𝓝 (π p)] id := by
      filter_upwards [hπs] with y hy using hy
    rw [hEq.mfderiv_eq, mfderiv_id]
  have hright :
      (mfderiv I J π p).comp (mfderiv J I s (π p)) =
        ContinuousLinearMap.id ℝ (TangentSpace J (π p)) := by
    have hcomp' :
        mfderiv J J (π ∘ s) (π p) =
          (mfderiv I J π p).comp (mfderiv J I s (π p)) := by
      rw [← mfderiv_congr_point (I := I) (I' := J) (f := π) hsp]
      exact hcomp
    exact hcomp'.symm.trans hid
  intro v
  refine ⟨mfderiv J I s (π p) v, ?_⟩
  exact congrArg (fun L : TangentSpace J (π p) →L[ℝ] TangentSpace J (π p) => L v) hright

-- Proof sketch: for the forward implication, apply the rank theorem in local coordinates to write
-- `π` near each `p` as a coordinate projection and take the coordinate inclusion as a smooth local
-- section through `p`. For the reverse implication, differentiate the identity `π ∘ σ = id` at
-- `q = π p`; then `mfderiv I J π p ∘ mfderiv J I σ q = ContinuousLinearMap.id ℝ _`, so
-- `mfderiv I J π p` is surjective.
/-- Theorem 4.26 (Local Section Theorem): a smooth map between finite-dimensional smooth manifolds
is a smooth submersion exactly when each point of the source lies on a smooth local section
through its image. -/
theorem smooth_submersion_iff_exists_smooth_local_section_through_every_point [I.Boundaryless]
    {π : M → N} (hπ : ContMDiff I J ∞ π) :
    (∀ p : M, Function.Surjective (mfderiv I J π p)) ↔
      ∀ p : M, ∃ U : TopologicalSpace.Opens N, ∃ hq : π p ∈ U, ∃ σ : U → M,
        IsSmoothLocalSection I J π U σ ∧ σ ⟨π p, hq⟩ = p := by
  constructor
  · intro hsurj p
    exact exists_smooth_local_section_of_surjective_mfderiv hπ (hsurj p)
  · intro hsec p
    exact surjective_mfderiv_of_exists_smooth_local_section hπ (hsec p)

end

end Manifold
