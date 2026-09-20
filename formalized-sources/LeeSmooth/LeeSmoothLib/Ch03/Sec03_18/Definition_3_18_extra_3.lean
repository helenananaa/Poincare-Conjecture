import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import LeeSmoothLib.Ch03.Sec03_18.Definition_3_18_extra_1
import LeeSmoothLib.Ch03.Sec03_18.Definition_3_18_extra_2
import LeeSmoothLib.Ch03.Sec03_17.Proposition_3_23
import LeeSmoothLib.Ch03.Sec03_17.Proposition_3_24
open TopologicalSpace CategoryTheory
open scoped ContDiff Manifold

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "𝒪∞" => smoothSheafCommRing I 𝓘(ℝ) M ℝ

-- Domain sampling pass:
-- `source-facing`: curve classes modulo first-order agreement at the base point.
-- `core/canonical`: the germ ring `C^∞_[p](I)` and its derivation space `𝒟_[p](I)`.
-- `bridge/view`: a curve represents a germ derivation by matching all smooth-germ derivatives.

/-- A smooth curve based at `p`, specified on some open interval `(-r, r)` around `0`. -/
structure SmoothCurveAt (p : M) where
  /-- The positive radius of the interval on which the curve is assumed smooth. -/
  radius : Set.Ioi (0 : ℝ)
  /-- The underlying parametrized curve. -/
  toFun : ℝ → M
  /-- The curve starts at the base point `p` at time `0`. -/
  source : toFun 0 = p
  /-- The curve is smooth on the interval `(-radius, radius)`. -/
  smooth : ContMDiffOn 𝓘(ℝ) I ∞ toFun (Set.Ioo (-radius) radius)

/-- A based smooth curve can be used as an ordinary function `ℝ → M`. -/
instance {p : M} : CoeFun (SmoothCurveAt I p) (fun _ ↦ ℝ → M) := ⟨SmoothCurveAt.toFun⟩

namespace SmoothCurveAt

/-- The open interval on which a based smooth curve is assumed smooth. -/
def sourceSet {p : M} (γ : SmoothCurveAt I p) : Set ℝ :=
  Set.Ioo (-γ.radius) γ.radius

omit [IsManifold I ∞ M] in
@[simp] theorem zero_mem_sourceSet {p : M} (γ : SmoothCurveAt I p) : (0 : ℝ) ∈ γ.sourceSet := by
  constructor
  · exact neg_lt_zero.mpr γ.radius.2
  · exact γ.radius.2

omit [IsManifold I ∞ M] in
theorem uniqueMDiffWithinAt_sourceSet {p : M} (γ : SmoothCurveAt I p) :
    UniqueMDiffWithinAt 𝓘(ℝ) γ.sourceSet 0 :=
  isOpen_Ioo.uniqueMDiffWithinAt γ.zero_mem_sourceSet

/-- The tangent vector represented by a smooth curve based at `p`, computed within its defining
interval. -/
def tangentVector {p : M} (γ : SmoothCurveAt I p) : TangentSpace I p :=
  γ.source ▸ curve_velocityWithin I γ γ.sourceSet 0

/-- The derivative at `0` obtained by testing a based smooth curve against an ambient real-valued
function. -/
def testDerivative {p : M} (γ : SmoothCurveAt I p) (F : M → ℝ) : ℝ :=
  derivWithin (F ∘ γ) γ.sourceSet 0

end SmoothCurveAt

/-- Auxiliary representative-level datum: a smooth ambient extension near `p` of a local smooth
test function on `U`. -/
def IsLocalExtensionAt (p : M) {U : Opens M}
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) (F : M → ℝ) : Prop :=
  p ∈ U ∧ ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ ContMDiffOn I 𝓘(ℝ) ∞ F V ∧
    ∀ x : U, x.1 ∈ V → F x = f x

namespace SmoothCurveAt

/-- A based smooth curve has germ derivative `r` on `φ : C^∞_[p](I)` if every local representative
of `φ` and every smooth ambient extension near `p` have derivative `r` at `0` along the curve. -/
def HasGermDerivative {p : M} (γ : SmoothCurveAt I p) (φ : C^∞_[p](I)) (r : ℝ) : Prop :=
  ∀ ⦃U : Opens M⦄ (hpU : p ∈ U) (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯),
    𝒪∞.presheaf.germ U p hpU f = φ →
      ∀ ⦃F : M → ℝ⦄, IsLocalExtensionAt I p f F →
        testDerivative I γ F = r

omit [IsManifold I ∞ M] in
section

/-- Extend a section on an open set by an arbitrary value off that set.  Only its behavior on the
open set is used below. -/
private noncomputable def sectionExtension {U : Opens M}
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) : M → ℝ :=
  Subtype.val.extend f 0

private theorem sectionExtension_apply {U : Opens M}
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) (x : M) (hx : x ∈ U) :
    sectionExtension I f x = f ⟨x, hx⟩ := by
  exact Subtype.val_injective.extend_apply f 0 ⟨x, hx⟩

private theorem sectionExtension_isLocalExtensionAt {p : M} {U : Opens M}
    (hpU : p ∈ U) (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) :
    IsLocalExtensionAt I p f (sectionExtension I f) := by
  refine ⟨hpU, U, U.2, hpU, ?_, ?_⟩
  · intro x hx
    apply ContMDiffAt.contMDiffWithinAt
    rw [← contMDiffAt_subtype_iff (U := U) (x := ⟨x, hx⟩)]
    exact (f.contMDiff.contMDiffAt).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y ↦ sectionExtension_apply I f y.1 y.2)
  · intro x hx
    exact sectionExtension_apply I f x.1 hx

private theorem testDerivative_eq_of_extensions {p : M} (γ : SmoothCurveAt I p)
    {U V : Opens M} (hpU : p ∈ U) (hpV : p ∈ V)
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) (g : C^∞⟮I, V; 𝓘(ℝ), ℝ⟯)
    (hgerm : 𝒪∞.presheaf.germ U p hpU f = 𝒪∞.presheaf.germ V p hpV g)
    {F G : M → ℝ} (hF : IsLocalExtensionAt I p f F)
    (hG : IsLocalExtensionAt I p g G) :
    testDerivative I γ F = testDerivative I γ G := by
  rcases hF with ⟨_, A, hAopen, hpA, _, hFA⟩
  rcases hG with ⟨_, B, hBopen, hpB, _, hGB⟩
  rcases (smoothSheafCommRing.germ_eq_iff (I := I) hpU hpV f g).1 hgerm with
    ⟨W, hpW, iWU, iWV, hfg⟩
  have hlocal : ∀ x : M, x ∈ (W : Set M) ∩ A ∩ B → F x = G x := by
    intro x hx
    have hxW : x ∈ W := hx.1.1
    have hxU : x ∈ U := (leOfHom iWU) hxW
    have hxV : x ∈ V := (leOfHom iWV) hxW
    have hsections : f ⟨x, hxU⟩ = g ⟨x, hxV⟩ := by
      change (𝒪∞.presheaf.map iWU.op f : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯) =
        𝒪∞.presheaf.map iWV.op g at hfg
      have h := congrArg (fun s : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ ↦ s ⟨x, hxW⟩) hfg
      exact h
    exact (hFA ⟨x, hxU⟩ hx.1.2).trans <| hsections.trans (hGB ⟨x, hxV⟩ hx.2).symm
  have hN : (W : Set M) ∩ A ∩ B ∈ nhds p :=
    IsOpen.mem_nhds (W.2.inter hAopen |>.inter hBopen) ⟨⟨hpW, hpA⟩, hpB⟩
  have hγcont : ContinuousAt γ 0 :=
    (γ.smooth.contMDiffAt (isOpen_Ioo.mem_nhds γ.zero_mem_sourceSet)).continuousAt
  have hpre : γ ⁻¹' ((W : Set M) ∩ A ∩ B) ∈ nhds (0 : ℝ) := by
    apply hγcont.preimage_mem_nhds
    simpa [γ.source] using hN
  have heq : (F ∘ γ) =ᶠ[nhds (0 : ℝ)] (G ∘ γ) :=
    Filter.mem_of_superset hpre fun t ht ↦ hlocal (γ t) ht
  exact heq.derivWithin_eq_of_nhds

private theorem extension_comp_differentiableWithinAt {p : M} (γ : SmoothCurveAt I p)
    {U : Opens M} {f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯} {F : M → ℝ}
    (hF : IsLocalExtensionAt I p f F) :
    DifferentiableWithinAt ℝ (F ∘ γ) γ.sourceSet 0 := by
  rcases hF with ⟨_, V, hVopen, hpV, hFsmooth, _⟩
  have hFat : MDifferentiableAt I 𝓘(ℝ) F p :=
    (hFsmooth.contMDiffAt (hVopen.mem_nhds hpV)).mdifferentiableAt (by simp)
  have hγat : MDifferentiableAt 𝓘(ℝ) I γ 0 :=
    (γ.smooth.contMDiffAt (isOpen_Ioo.mem_nhds γ.zero_mem_sourceSet)).mdifferentiableAt
      (by simp)
  exact ((hFat.comp_of_eq 0 hγat γ.source).differentiableAt).differentiableWithinAt

private theorem existsUnique_hasGermDerivative {p : M} (γ : SmoothCurveAt I p)
    (φ : C^∞_[p](I)) : ∃! r : ℝ, HasGermDerivative I γ φ r := by
  rcases 𝒪∞.presheaf.exists_germ_eq φ with ⟨U, hpU, f, hf⟩
  let F : M → ℝ := sectionExtension I f
  let r : ℝ := testDerivative I γ F
  have hF : IsLocalExtensionAt I p f F := sectionExtension_isLocalExtensionAt I hpU f
  refine ⟨r, ?_, ?_⟩
  · intro V hpV g hg G hG
    simpa [r] using
      (testDerivative_eq_of_extensions I γ hpU hpV f g (hf.trans hg.symm)
        (F := F) (G := G) hF hG).symm
  · intro y hy
    exact (hy hpU f hf hF).symm

/-- The derivative of a smooth germ along a based smooth curve. -/
private noncomputable def germDerivative {p : M} (γ : SmoothCurveAt I p)
    (φ : C^∞_[p](I)) : ℝ :=
  (existsUnique_hasGermDerivative I γ φ).choose

private theorem hasGermDerivative_germDerivative {p : M} (γ : SmoothCurveAt I p)
    (φ : C^∞_[p](I)) : HasGermDerivative I γ φ (germDerivative I γ φ) :=
  (existsUnique_hasGermDerivative I γ φ).choose_spec.1

private theorem eq_germDerivative_of_hasGermDerivative {p : M} (γ : SmoothCurveAt I p)
    {φ : C^∞_[p](I)} {r : ℝ} (hr : HasGermDerivative I γ φ r) :
    r = germDerivative I γ φ :=
  (existsUnique_hasGermDerivative I γ φ).unique hr
    (hasGermDerivative_germDerivative I γ φ)

private theorem isLocalExtensionAt_restrict {p : M} {U W : Opens M}
    (hpW : p ∈ W) (iWU : W ⟶ U) (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) {F : M → ℝ}
    (hF : IsLocalExtensionAt I p f F) :
    IsLocalExtensionAt I p (𝒪∞.presheaf.map iWU.op f) F := by
  rcases hF with ⟨_, A, hAopen, hpA, hFsmooth, hFA⟩
  refine ⟨hpW, A ∩ (W : Set M), hAopen.inter W.2, ⟨hpA, hpW⟩,
    hFsmooth.mono Set.inter_subset_left, ?_⟩
  intro x hx
  have hxU : x.1 ∈ U := (leOfHom iWU) x.2
  change F x.1 = f ⟨x.1, hxU⟩
  exact hFA ⟨x.1, hxU⟩ hx.1

private theorem IsLocalExtensionAt.add {p : M} {U : Opens M}
    {f g : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯} {F G : M → ℝ}
    (hF : IsLocalExtensionAt I p f F) (hG : IsLocalExtensionAt I p g G) :
    IsLocalExtensionAt I p (f + g) (F + G) := by
  rcases hF with ⟨hpU, A, hAopen, hpA, hFsmooth, hFA⟩
  rcases hG with ⟨_, B, hBopen, hpB, hGsmooth, hGB⟩
  refine ⟨hpU, A ∩ B, hAopen.inter hBopen, ⟨hpA, hpB⟩,
    (hFsmooth.mono Set.inter_subset_left).add (hGsmooth.mono Set.inter_subset_right), ?_⟩
  intro x hx
  exact congrArg₂ (· + ·) (hFA x hx.1) (hGB x hx.2)

private theorem IsLocalExtensionAt.smul {p : M} {U : Opens M}
    {f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯} {F : M → ℝ}
    (hF : IsLocalExtensionAt I p f F) (c : ℝ) :
    IsLocalExtensionAt I p (c • f) (c • F) := by
  rcases hF with ⟨hpU, A, hAopen, hpA, hFsmooth, hFA⟩
  have hc : ContMDiffOn I 𝓘(ℝ) ∞ (fun _ : M ↦ c) A := contMDiffOn_const
  refine ⟨hpU, A, hAopen, hpA, ?_, ?_⟩
  · apply (hc.mul hFsmooth).congr
    intro x _
    change c • F x = c * F x
    simp [smul_eq_mul]
  intro x hx
  exact congrArg (c • ·) (hFA x hx)

private theorem IsLocalExtensionAt.mul {p : M} {U : Opens M}
    {f g : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯} {F G : M → ℝ}
    (hF : IsLocalExtensionAt I p f F) (hG : IsLocalExtensionAt I p g G) :
    IsLocalExtensionAt I p (f * g) (F * G) := by
  rcases hF with ⟨hpU, A, hAopen, hpA, hFsmooth, hFA⟩
  rcases hG with ⟨_, B, hBopen, hpB, hGsmooth, hGB⟩
  refine ⟨hpU, A ∩ B, hAopen.inter hBopen, ⟨hpA, hpB⟩,
    (hFsmooth.mono Set.inter_subset_left).mul (hGsmooth.mono Set.inter_subset_right), ?_⟩
  intro x hx
  exact congrArg₂ (· * ·) (hFA x hx.1) (hGB x hx.2)

private theorem germ_add {p : M} {U : Opens M} (hpU : p ∈ U)
    (f g : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) :
    𝒪∞.presheaf.germ U p hpU (f + g) =
      𝒪∞.presheaf.germ U p hpU f + 𝒪∞.presheaf.germ U p hpU g := by
  change ((𝒪∞.presheaf.germ U p hpU).hom) (f + g) =
    ((𝒪∞.presheaf.germ U p hpU).hom) f + ((𝒪∞.presheaf.germ U p hpU).hom) g
  exact map_add _ f g

private theorem germ_mul {p : M} {U : Opens M} (hpU : p ∈ U)
    (f g : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) :
    𝒪∞.presheaf.germ U p hpU (f * g) =
      𝒪∞.presheaf.germ U p hpU f * 𝒪∞.presheaf.germ U p hpU g := by
  change ((𝒪∞.presheaf.germ U p hpU).hom) (f * g) =
    ((𝒪∞.presheaf.germ U p hpU).hom) f * ((𝒪∞.presheaf.germ U p hpU).hom) g
  exact map_mul _ f g

private theorem germ_algebraMap {p : M} {U : Opens M} (hpU : p ∈ U) (c : ℝ) :
    𝒪∞.presheaf.germ U p hpU (algebraMap ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ c) =
      algebraMap ℝ C^∞_[p](I) c := by
  let iTop : U ⟶ (⊤ : Opens M) := homOfLE le_top
  refine (smoothSheafCommRing.germ_eq_iff (I := I) hpU (by simp)
    (algebraMap ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ c)
    (algebraMap ℝ C^∞⟮I, (⊤ : Opens M); 𝓘(ℝ), ℝ⟯ c)).2 ?_
  refine ⟨U, hpU, 𝟙 U, iTop, ?_⟩
  apply ContMDiffMap.ext
  intro x
  rfl

private theorem germ_smul {p : M} {U : Opens M} (hpU : p ∈ U) (c : ℝ)
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) :
    𝒪∞.presheaf.germ U p hpU (c • f) = c • 𝒪∞.presheaf.germ U p hpU f := by
  change ((𝒪∞.presheaf.germ U p hpU).hom)
      ((algebraMap ℝ C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ c) * f) =
    (algebraMap ℝ C^∞_[p](I) c) * ((𝒪∞.presheaf.germ U p hpU).hom f)
  rw [map_mul, germ_algebraMap I hpU c]

private theorem germDerivative_add {p : M} (γ : SmoothCurveAt I p)
    (φ ψ : C^∞_[p](I)) :
    germDerivative I γ (φ + ψ) = germDerivative I γ φ + germDerivative I γ ψ := by
  rcases 𝒪∞.presheaf.exists_germ_eq φ with ⟨U, hpU, f, hf⟩
  rcases 𝒪∞.presheaf.exists_germ_eq ψ with ⟨V, hpV, g, hg⟩
  let W : Opens M := U ⊓ V
  have hpW : p ∈ W := ⟨hpU, hpV⟩
  let iWU : W ⟶ U := Opens.infLELeft U V
  let iWV : W ⟶ V := Opens.infLERight U V
  let fW : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ := 𝒪∞.presheaf.map iWU.op f
  let gW : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ := 𝒪∞.presheaf.map iWV.op g
  let F : M → ℝ := sectionExtension I f
  let G : M → ℝ := sectionExtension I g
  have hF : IsLocalExtensionAt I p f F := sectionExtension_isLocalExtensionAt I hpU f
  have hG : IsLocalExtensionAt I p g G := sectionExtension_isLocalExtensionAt I hpV g
  have hFW : IsLocalExtensionAt I p fW F :=
    isLocalExtensionAt_restrict I hpW iWU f hF
  have hGW : IsLocalExtensionAt I p gW G :=
    isLocalExtensionAt_restrict I hpW iWV g hG
  have hfW : 𝒪∞.presheaf.germ W p hpW fW = φ := by
    exact (𝒪∞.presheaf.germ_res_apply iWU p hpW f).trans hf
  have hgW : 𝒪∞.presheaf.germ W p hpW gW = ψ := by
    exact (𝒪∞.presheaf.germ_res_apply iWV p hpW g).trans hg
  have hsum : 𝒪∞.presheaf.germ W p hpW (fW + gW) = φ + ψ := by
    rw [germ_add I hpW, hfW, hgW]
  have hsumDeriv :=
    hasGermDerivative_germDerivative I γ (φ + ψ) hpW (fW + gW) hsum
      (IsLocalExtensionAt.add (I := I) hFW hGW)
  have hφDeriv := hasGermDerivative_germDerivative I γ φ hpU f hf hF
  have hψDeriv := hasGermDerivative_germDerivative I γ ψ hpV g hg hG
  have hdiffF := extension_comp_differentiableWithinAt I γ hF
  have hdiffG := extension_comp_differentiableWithinAt I γ hG
  have hadd : testDerivative I γ (F + G) =
      testDerivative I γ F + testDerivative I γ G := by
    change derivWithin (fun t ↦ F (γ t) + G (γ t)) γ.sourceSet 0 =
      derivWithin (F ∘ γ) γ.sourceSet 0 + derivWithin (G ∘ γ) γ.sourceSet 0
    exact derivWithin_fun_add hdiffF hdiffG
  calc
    germDerivative I γ (φ + ψ) = testDerivative I γ (F + G) := hsumDeriv.symm
    _ = testDerivative I γ F + testDerivative I γ G := hadd
    _ = germDerivative I γ φ + germDerivative I γ ψ := congrArg₂ (· + ·) hφDeriv hψDeriv

private theorem germDerivative_smul {p : M} (γ : SmoothCurveAt I p)
    (c : ℝ) (φ : C^∞_[p](I)) :
    germDerivative I γ (c • φ) = c • germDerivative I γ φ := by
  rcases 𝒪∞.presheaf.exists_germ_eq φ with ⟨U, hpU, f, hf⟩
  let fU : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ := f
  have hfU : 𝒪∞.presheaf.germ U p hpU fU = φ := hf
  let F : M → ℝ := sectionExtension I fU
  have hF : IsLocalExtensionAt I p fU F := sectionExtension_isLocalExtensionAt I hpU fU
  have hcφ : 𝒪∞.presheaf.germ U p hpU (c • fU) = c • φ := by
    rw [germ_smul I hpU, hfU]
  have hscaledDeriv :=
    hasGermDerivative_germDerivative I γ (c • φ) hpU (c • fU) hcφ
      (IsLocalExtensionAt.smul (I := I) hF c)
  have hφDeriv := hasGermDerivative_germDerivative I γ φ hpU fU hfU hF
  have hdiffF := extension_comp_differentiableWithinAt I γ hF
  have hsmul : testDerivative I γ (c • F) = c • testDerivative I γ F := by
    change derivWithin (fun t ↦ c • F (γ t)) γ.sourceSet 0 =
      c • derivWithin (F ∘ γ) γ.sourceSet 0
    exact derivWithin_fun_const_smul c hdiffF
  calc
    germDerivative I γ (c • φ) = testDerivative I γ (c • F) := hscaledDeriv.symm
    _ = c • testDerivative I γ F := hsmul
    _ = c • germDerivative I γ φ := congrArg (c • ·) hφDeriv

private theorem extension_value_eq_eval {p : M} {U : Opens M} (hpU : p ∈ U)
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) (φ : C^∞_[p](I))
    (hf : 𝒪∞.presheaf.germ U p hpU f = φ) {F : M → ℝ}
    (hF : IsLocalExtensionAt I p f F) :
    F p = smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ p φ := by
  rcases hF with ⟨_, A, _, hpA, _, hFA⟩
  calc
    F p = f ⟨p, hpU⟩ := hFA ⟨p, hpU⟩ hpA
    _ = smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ p
        (𝒪∞.presheaf.germ U p hpU f) :=
      (smoothSheafCommRing.eval_germ U p hpU f).symm
    _ = smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ p φ := congrArg _ hf

private theorem germDerivative_mul {p : M} (γ : SmoothCurveAt I p)
    (φ ψ : C^∞_[p](I)) :
    germDerivative I γ (φ * ψ) =
      φ • germDerivative I γ ψ + ψ • germDerivative I γ φ := by
  rcases 𝒪∞.presheaf.exists_germ_eq φ with ⟨U, hpU, f, hf⟩
  rcases 𝒪∞.presheaf.exists_germ_eq ψ with ⟨V, hpV, g, hg⟩
  let W : Opens M := U ⊓ V
  have hpW : p ∈ W := ⟨hpU, hpV⟩
  let iWU : W ⟶ U := Opens.infLELeft U V
  let iWV : W ⟶ V := Opens.infLERight U V
  let fW : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ := 𝒪∞.presheaf.map iWU.op f
  let gW : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ := 𝒪∞.presheaf.map iWV.op g
  let F : M → ℝ := sectionExtension I f
  let G : M → ℝ := sectionExtension I g
  have hF : IsLocalExtensionAt I p f F := sectionExtension_isLocalExtensionAt I hpU f
  have hG : IsLocalExtensionAt I p g G := sectionExtension_isLocalExtensionAt I hpV g
  have hFW : IsLocalExtensionAt I p fW F :=
    isLocalExtensionAt_restrict I hpW iWU f hF
  have hGW : IsLocalExtensionAt I p gW G :=
    isLocalExtensionAt_restrict I hpW iWV g hG
  have hfW : 𝒪∞.presheaf.germ W p hpW fW = φ := by
    exact (𝒪∞.presheaf.germ_res_apply iWU p hpW f).trans hf
  have hgW : 𝒪∞.presheaf.germ W p hpW gW = ψ := by
    exact (𝒪∞.presheaf.germ_res_apply iWV p hpW g).trans hg
  have hprod : 𝒪∞.presheaf.germ W p hpW (fW * gW) = φ * ψ := by
    rw [germ_mul I hpW, hfW, hgW]
  have hprodDeriv :=
    hasGermDerivative_germDerivative I γ (φ * ψ) hpW (fW * gW) hprod
      (IsLocalExtensionAt.mul (I := I) hFW hGW)
  have hφDeriv := hasGermDerivative_germDerivative I γ φ hpU f hf hF
  have hψDeriv := hasGermDerivative_germDerivative I γ ψ hpV g hg hG
  have hdiffF := extension_comp_differentiableWithinAt I γ hF
  have hdiffG := extension_comp_differentiableWithinAt I γ hG
  have hmul : testDerivative I γ (F * G) =
      testDerivative I γ F * G p + F p * testDerivative I γ G := by
    change derivWithin (fun t ↦ F (γ t) * G (γ t)) γ.sourceSet 0 =
      derivWithin (F ∘ γ) γ.sourceSet 0 * G p +
        F p * derivWithin (G ∘ γ) γ.sourceSet 0
    calc
      derivWithin (fun t ↦ F (γ t) * G (γ t)) γ.sourceSet 0 =
          derivWithin (F ∘ γ) γ.sourceSet 0 * G (γ 0) +
            F (γ 0) * derivWithin (G ∘ γ) γ.sourceSet 0 :=
        derivWithin_fun_mul hdiffF hdiffG
      _ = derivWithin (F ∘ γ) γ.sourceSet 0 * G p +
            F p * derivWithin (G ∘ γ) γ.sourceSet 0 := by rw [γ.source]
  have hFp := extension_value_eq_eval I hpU f φ hf hF
  have hGp := extension_value_eq_eval I hpV g ψ hg hG
  calc
    germDerivative I γ (φ * ψ) = testDerivative I γ (F * G) := hprodDeriv.symm
    _ = testDerivative I γ F * G p + F p * testDerivative I γ G := hmul
    _ = (smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ p φ) * germDerivative I γ ψ +
        (smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ p ψ) * germDerivative I γ φ := by
      rw [hφDeriv, hψDeriv, hFp, hGp]
      ring
    _ = φ • germDerivative I γ ψ + ψ • germDerivative I γ φ := by
      rfl

/-- The germ derivation induced by differentiation along a based smooth curve. -/
private noncomputable def inducedDerivation {p : M} (γ : SmoothCurveAt I p) : 𝒟_[p](I) :=
  Derivation.mk'
    { toFun := germDerivative I γ
      map_add' := germDerivative_add I γ
      map_smul' := germDerivative_smul I γ }
    (germDerivative_mul I γ)

private theorem inducedDerivation_apply {p : M} (γ : SmoothCurveAt I p)
    (φ : C^∞_[p](I)) : inducedDerivation I γ φ = germDerivative I γ φ :=
  rfl

/-- A based smooth curve represents the germ derivation `v` when the curve's derivative relation on
smooth germs is exactly evaluation by `v`. -/
def RepresentsDerivation {p : M} (γ : SmoothCurveAt I p) (v : 𝒟_[p](I)) : Prop :=
  ∀ φ : C^∞_[p](I), ∀ r : ℝ, HasGermDerivative I γ φ r ↔ v φ = r

/-- A germ derivation represented by a based smooth curve is unique. -/
theorem representsDerivation_unique {p : M} {γ : SmoothCurveAt I p} {v₁ v₂ : 𝒟_[p](I)}
    (hv₁ : SmoothCurveAt.RepresentsDerivation I γ v₁)
    (hv₂ : SmoothCurveAt.RepresentsDerivation I γ v₂) :
    v₁ = v₂ := by
  ext φ
  have hγ : HasGermDerivative I γ φ (v₁ φ) := (hv₁ φ (v₁ φ)).2 rfl
  exact (hv₂ φ (v₁ φ)).1 hγ |>.symm

/-- Every based smooth curve induces a germ derivation on the smooth-germ ring at the base point. -/
theorem exists_representingDerivation {p : M} (γ : SmoothCurveAt I p) :
    ∃ v : 𝒟_[p](I), SmoothCurveAt.RepresentsDerivation I γ v := by
  refine ⟨inducedDerivation I γ, ?_⟩
  intro φ r
  constructor
  · intro hr
    exact (eq_germDerivative_of_hasGermDerivative I γ hr).symm
  · intro hr
    change germDerivative I γ φ = r at hr
    simpa only [hr] using hasGermDerivative_germDerivative I γ φ

end

end SmoothCurveAt

/-- Two based smooth curves are equivalent when they represent the same germ derivation at `p`. -/
def SmoothCurveEqv {p : M} (γ₁ γ₂ : SmoothCurveAt I p) : Prop :=
  ∃ v : 𝒟_[p](I),
    SmoothCurveAt.RepresentsDerivation I γ₁ v ∧
      SmoothCurveAt.RepresentsDerivation I γ₂ v

omit [IsManifold I ∞ M] in
/-- Reflexivity of the smooth-curve velocity relation. -/
theorem smoothCurveEqv_refl {p : M} (γ : SmoothCurveAt I p) : SmoothCurveEqv I γ γ := by
  rcases SmoothCurveAt.exists_representingDerivation I γ with ⟨v, hv⟩
  exact ⟨v, hv, hv⟩

omit [IsManifold I ∞ M] in
/-- Symmetry of the smooth-curve velocity relation. -/
theorem smoothCurveEqv_symm {p : M} {γ₁ γ₂ : SmoothCurveAt I p}
    (h : SmoothCurveEqv I γ₁ γ₂) : SmoothCurveEqv I γ₂ γ₁ := by
  rcases h with ⟨v, hv₁, hv₂⟩
  exact ⟨v, hv₂, hv₁⟩

omit [IsManifold I ∞ M] in
/-- Transitivity of the smooth-curve velocity relation. -/
theorem smoothCurveEqv_trans {p : M} {γ₁ γ₂ γ₃ : SmoothCurveAt I p}
    (h₁ : SmoothCurveEqv I γ₁ γ₂) (h₂ : SmoothCurveEqv I γ₂ γ₃) :
    SmoothCurveEqv I γ₁ γ₃ := by
  rcases h₁ with ⟨v₁, hγ₁, hγ₂₁⟩
  rcases h₂ with ⟨v₂, hγ₂₂, hγ₃⟩
  have hv : v₁ = v₂ :=
    SmoothCurveAt.representsDerivation_unique I hγ₂₁ hγ₂₂
  exact ⟨v₁, hγ₁, hv ▸ hγ₃⟩

/-- The setoid on based smooth curves coming from equality of the represented germ derivation at
time `0`. -/
def smoothCurveSetoid (p : M) : Setoid (SmoothCurveAt I p) where
  r := SmoothCurveEqv I
  iseqv := ⟨smoothCurveEqv_refl I, smoothCurveEqv_symm I, smoothCurveEqv_trans I⟩

/-- Definition 3.18-extra-3: the curve-velocity classes at `p` are equivalence classes of based
smooth curves under equality of the germ derivation they represent at `0`. -/
def CurveVelocityClass (p : M) :=
  Quotient (smoothCurveSetoid I p)

private theorem tangent_transport_mfderiv_eq {p : M} {γ : ℝ → M}
    (hγ : γ 0 = p) (F : M → ℝ) (ξ : TangentSpace I (γ 0)) :
    mfderiv I 𝓘(ℝ) F p (hγ ▸ ξ) = mfderiv I 𝓘(ℝ) F (γ 0) ξ := by
  cases hγ
  rfl

private theorem testDerivative_eq_mfderiv_tangentVector {p : M}
    (γ : SmoothCurveAt I p) {U : Opens M} {f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯}
    {F : M → ℝ} (hF : IsLocalExtensionAt I p f F) :
    SmoothCurveAt.testDerivative I γ F =
      mfderiv I 𝓘(ℝ) F p γ.tangentVector := by
  let J : Set ℝ := γ.sourceSet
  have hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0 := γ.uniqueMDiffWithinAt_sourceSet
  have hγmd : MDifferentiableWithinAt 𝓘(ℝ) I γ J 0 :=
    γ.smooth.mdifferentiableOn (by simp) 0 γ.zero_mem_sourceSet
  rcases hF with ⟨_, V, hVopen, hpV, hFsmooth, _⟩
  have hFat : MDifferentiableAt I 𝓘(ℝ) F p :=
    (hFsmooth.contMDiffAt (hVopen.mem_nhds hpV)).mdifferentiableAt (by simp)
  have hFat0 : MDifferentiableAt I 𝓘(ℝ) F (γ 0) := by
    simpa only [γ.source] using hFat
  have hcomp :
      curve_velocityWithin 𝓘(ℝ) (F ∘ γ) J 0 =
        mfderiv I 𝓘(ℝ) F (γ 0) (curve_velocityWithin I γ J 0) :=
    composite_curve_velocity hJ hFat0 hγmd
  have htest : SmoothCurveAt.testDerivative I γ F =
      curve_velocityWithin 𝓘(ℝ) (F ∘ γ) J 0 := by
    unfold SmoothCurveAt.testDerivative curve_velocityWithin
    rw [mfderivWithin_eq_fderivWithin]
    exact fderivWithin_derivWithin.symm
  have htransport :
      mfderiv I 𝓘(ℝ) F p γ.tangentVector =
        mfderiv I 𝓘(ℝ) F (γ 0) (curve_velocityWithin I γ J 0) := by
    simpa only [SmoothCurveAt.tangentVector, J] using
      tangent_transport_mfderiv_eq (I := I) γ.source F
        (curve_velocityWithin I γ γ.sourceSet 0)
  exact htest.trans <| hcomp.trans htransport.symm

private theorem testDerivative_chartLinear_eq_tangentVector {p : M}
    (γ : SmoothCurveAt I p) (L : E →L[ℝ] ℝ) :
    SmoothCurveAt.testDerivative I γ (fun x ↦ L (extChartAt I p x)) =
      L (mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p γ.tangentVector) := by
  let J : Set ℝ := γ.sourceSet
  let η : ℝ → E := (extChartAt I p) ∘ γ
  have hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0 := γ.uniqueMDiffWithinAt_sourceSet
  have hγmd : MDifferentiableWithinAt 𝓘(ℝ) I γ J 0 :=
    γ.smooth.mdifferentiableOn (by simp) 0 γ.zero_mem_sourceSet
  have hchart : MDifferentiableAt I (𝓘(ℝ, E)) (extChartAt I p) (γ 0) := by
    simpa only [γ.source] using
      (contMDiffAt_extChartAt (I := I) (n := ∞) (x := p)).mdifferentiableAt (by simp)
  have hchartVel :
      curve_velocityWithin (𝓘(ℝ, E)) η J 0 =
        mfderiv I (𝓘(ℝ, E)) (extChartAt I p) (γ 0)
          (curve_velocityWithin I γ J 0) := by
    simpa only [η] using composite_curve_velocity hJ hchart hγmd
  have htransport :
      mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p γ.tangentVector =
        mfderiv I (𝓘(ℝ, E)) (extChartAt I p) (γ 0)
          (curve_velocityWithin I γ J 0) := by
    simpa only [SmoothCurveAt.tangentVector, J] using
      tangent_transport_mfderiv_extChartAt_eq (I := I) (p := p) γ.source
        (curve_velocityWithin I γ γ.sourceSet 0)
  have hηmd : MDifferentiableWithinAt 𝓘(ℝ) (𝓘(ℝ, E)) η J 0 :=
    hchart.comp_mdifferentiableWithinAt 0 hγmd
  have hLVel :
      curve_velocityWithin 𝓘(ℝ) (L ∘ η) J 0 =
        L (curve_velocityWithin (𝓘(ℝ, E)) η J 0) := by
    have h := composite_curve_velocity hJ
      ((L.contMDiffAt (n := ∞)).mdifferentiableAt (by simp)) hηmd
    simpa only [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv] using! h
  have htest :
      SmoothCurveAt.testDerivative I γ (fun x ↦ L (extChartAt I p x)) =
        curve_velocityWithin 𝓘(ℝ) (L ∘ η) J 0 := by
    unfold SmoothCurveAt.testDerivative curve_velocityWithin
    rw [mfderivWithin_eq_fderivWithin]
    exact fderivWithin_derivWithin.symm
  calc
    SmoothCurveAt.testDerivative I γ (fun x ↦ L (extChartAt I p x)) =
        curve_velocityWithin 𝓘(ℝ) (L ∘ η) J 0 := htest
    _ = L (curve_velocityWithin (𝓘(ℝ, E)) η J 0) := hLVel
    _ = L (mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p γ.tangentVector) := by
      rw [hchartVel, ← htransport]

section Boundaryless

variable [BoundarylessManifold I M]

/-- Every tangent vector on a boundaryless smooth manifold is represented by a based smooth curve
through the base point on some open interval around `0`. -/
theorem exists_smoothCurveAt_tangentVector_eq (p : M) (v : TangentSpace I p) :
    ∃ γ : SmoothCurveAt I p, γ.tangentVector = v := by
  rcases exists_open_interval_curve_with_velocity_of_isInteriorPoint p v
      BoundarylessManifold.isInteriorPoint with
    ⟨r, γ, hγsmooth, hγ0, hγv⟩
  refine ⟨⟨r, γ, hγ0, hγsmooth⟩, ?_⟩
  simpa [SmoothCurveAt.tangentVector, SmoothCurveAt.sourceSet] using hγv

/-- Equivalent smooth curves based at `p` determine the same tangent vector. -/
theorem smoothCurveAt_tangentVector_eq_of_eqv {p : M} (γ₁ γ₂ : SmoothCurveAt I p)
    (hγ : SmoothCurveEqv I γ₁ γ₂) : γ₁.tangentVector = γ₂.tangentVector := by
  rcases hγ with ⟨v, hv₁, hv₂⟩
  apply (isInvertible_mfderiv_extChartAt (I := I) (x := p) (y := p)
    (mem_extChartAt_source (I := I) p)).injective
  let w₁ : E := mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p γ₁.tangentVector
  let w₂ : E := mfderiv I (𝓘(ℝ, E)) (extChartAt I p) p γ₂.tangentVector
  suffices w₁ = w₂ by exact this
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2
  intro L
  let U : Opens M := ⟨(chartAt H p).source, (chartAt H p).open_source⟩
  have hpU : p ∈ U := mem_chart_source H p
  let F : M → ℝ := fun x ↦ L (extChartAt I p x)
  have hFOn : ContMDiffOn I 𝓘(ℝ) ∞ F U := by
    exact L.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt (I := I) (n := ∞) (x := p))
  let f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun x ↦ F x.1,
      hFOn.comp_contMDiff contMDiff_subtype_val (fun x ↦ x.2)⟩
  have hF : IsLocalExtensionAt I p f F := by
    refine ⟨hpU, U, U.2, hpU, hFOn, ?_⟩
    intro x _
    rfl
  let φ : C^∞_[p](I) := 𝒪∞.presheaf.germ U p hpU f
  have hd₁ := SmoothCurveAt.hasGermDerivative_germDerivative I γ₁ φ hpU f rfl hF
  have hd₂ := SmoothCurveAt.hasGermDerivative_germDerivative I γ₂ φ hpU f rfl hF
  have hvd₁ : v φ = SmoothCurveAt.germDerivative I γ₁ φ :=
    (hv₁ φ (SmoothCurveAt.germDerivative I γ₁ φ)).1
      (SmoothCurveAt.hasGermDerivative_germDerivative I γ₁ φ)
  have hvd₂ : v φ = SmoothCurveAt.germDerivative I γ₂ φ :=
    (hv₂ φ (SmoothCurveAt.germDerivative I γ₂ φ)).1
      (SmoothCurveAt.hasGermDerivative_germDerivative I γ₂ φ)
  have htest : SmoothCurveAt.testDerivative I γ₁ F =
      SmoothCurveAt.testDerivative I γ₂ F :=
    hd₁.trans <| hvd₁.symm.trans <| hvd₂.trans hd₂.symm
  simpa only [F, testDerivative_chartLinear_eq_tangentVector I] using htest

private theorem smoothCurveEqv_of_tangentVector_eq {p : M}
    (γ₁ γ₂ : SmoothCurveAt I p) (hγ : γ₁.tangentVector = γ₂.tangentVector) :
    SmoothCurveEqv I γ₁ γ₂ := by
  rcases SmoothCurveAt.exists_representingDerivation I γ₁ with ⟨v, hv₁⟩
  refine ⟨v, hv₁, ?_⟩
  intro φ r
  rw [← hv₁ φ r]
  constructor
  · intro h₂ U hpU f hf F hF
    have htest : SmoothCurveAt.testDerivative I γ₁ F =
        SmoothCurveAt.testDerivative I γ₂ F := by
      rw [testDerivative_eq_mfderiv_tangentVector I γ₁ hF,
        testDerivative_eq_mfderiv_tangentVector I γ₂ hF, hγ]
    exact htest.trans (h₂ hpU f hf hF)
  · intro h₁ U hpU f hf F hF
    have htest : SmoothCurveAt.testDerivative I γ₁ F =
        SmoothCurveAt.testDerivative I γ₂ F := by
      rw [testDerivative_eq_mfderiv_tangentVector I γ₁ hF,
        testDerivative_eq_mfderiv_tangentVector I γ₂ hF, hγ]
    exact htest.symm.trans (h₁ hpU f hf hF)

/-- The canonical map from local smooth-curve classes at `p` to the tangent space at `p`. -/
def curveVelocityClassToTangentSpace (p : M) : CurveVelocityClass I p → TangentSpace I p :=
  Quotient.lift (fun γ : SmoothCurveAt I p ↦ γ.tangentVector)
    (fun γ₁ γ₂ hγ ↦ smoothCurveAt_tangentVector_eq_of_eqv I γ₁ γ₂ hγ)

/-- The canonical map from local smooth-curve classes at `p` to the tangent space at `p` is a
bijection. -/
theorem curveVelocityClassToTangentSpace_bijective (p : M) :
    Function.Bijective (curveVelocityClassToTangentSpace I p) := by
  constructor
  · intro x y hxy
    induction x, y using Quotient.inductionOn₂ with
    | _ γ₁ γ₂ =>
        apply Quotient.sound
        exact smoothCurveEqv_of_tangentVector_eq I γ₁ γ₂ hxy
  · intro v
    rcases exists_smoothCurveAt_tangentVector_eq I p v with ⟨γ, hγ⟩
    refine ⟨Quotient.mk (smoothCurveSetoid I p) γ, ?_⟩
    exact hγ

/-- The local smooth-curve realization of tangent vectors at `p` is canonically equivalent to the
usual tangent space. -/
noncomputable def curveVelocityClassEquivTangentSpace (p : M) :
    CurveVelocityClass I p ≃ TangentSpace I p :=
  Equiv.ofBijective (curveVelocityClassToTangentSpace I p)
    (curveVelocityClassToTangentSpace_bijective I p)

@[simp] theorem curveVelocityClassEquivTangentSpace_apply {p : M} (x : CurveVelocityClass I p) :
    curveVelocityClassEquivTangentSpace I p x = curveVelocityClassToTangentSpace I p x := rfl

end Boundaryless
