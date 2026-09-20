import LeeSmoothLib.External.SardMoreira.ContDiffMoreiraHolder
import LeeSmoothLib.External.SardMoreira.LinearAlgebra

noncomputable section

open scoped Topology unitInterval

namespace HasStrictFDerivAt

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

@[irreducible, simps +simpRhs pt]
def implicitFunctionDataOfComplementedKerRange (f : E → F) (f' : E →L[𝕜] F) {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) :
    have := hrange.isClosed.completeSpace_coe
    ImplicitFunctionData 𝕜 E f'.range f'.ker := by
  haveI := hrange.isClosed.completeSpace_coe
  have hrange_apply (x) : hrange.choose (f' x) = ⟨f' x, by simp⟩ :=
    hrange.choose_spec ⟨f' x, by simp⟩
  have hker_eq : (hrange.choose ∘L f').ker = f'.ker := by
    ext x
    simp_all
  have hrange_eq : (hrange.choose ∘L f').range = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨_, x, rfl⟩
    use x
    simp_all
  let φ := implicitFunctionDataOfComplemented (hrange.choose ∘ f) (hrange.choose ∘L f')
    (hrange.choose.hasStrictFDerivAt.comp a hf) hrange_eq (by rwa [hker_eq])
  refine
    { __ := φ,
      rightFun := hker.choose
      rightDeriv := hker.choose
      range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
      hasStrictFDerivAt_rightFun := hker.choose.hasStrictFDerivAt
      isCompl_ker := ?_ }
  simpa only [φ, implicitFunctionDataOfComplemented, hker_eq]
    using LinearMap.isCompl_of_proj hker.choose_spec

def implicitToOpenPartialHomeomorphOfComplementedKerRange (f : E → F) (f' : E →L[𝕜] F) {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) :
    OpenPartialHomeomorph E (f'.range × f'.ker) :=
  have := hrange.isClosed.completeSpace_coe
  (hf.implicitFunctionDataOfComplementedKerRange f f' hker hrange).toOpenPartialHomeomorph

@[simp]
theorem mem_implicitToOpenPartialHomeomorphOfComplementedKerRange_source
    {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) :
    a ∈ (hf.implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hker hrange).source := by
  letI := hrange.isClosed.completeSpace_coe
  let φ : ImplicitFunctionData 𝕜 E f'.range f'.ker :=
    hf.implicitFunctionDataOfComplementedKerRange f f' hker hrange
  convert φ.pt_mem_toOpenPartialHomeomorph_source
  · rfl
  · simp only [φ, implicitFunctionDataOfComplementedKerRange, implicitFunctionDataOfComplemented]

theorem implicitToOpenPartialHomeomorphOfComplementedKerRange_apply {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) (x : E) :
    implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange x =
      (hrange.choose (f x), hker.choose x) := by
  -- `simp [implicitToOpenPartialHomeomorphOfComplementedKerRange,
  --  implicitFunctionDataOfComplementedKerRange]` works but it's much slower
  simp only [implicitToOpenPartialHomeomorphOfComplementedKerRange,
    implicitFunctionDataOfComplementedKerRange, implicitFunctionDataOfComplemented,
    Function.comp_apply, ImplicitFunctionData.toOpenPartialHomeomorph_apply]

theorem coe_implicitToOpenPartialHomeomorphOfComplementedKerRange {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) :
    implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange =
      fun x ↦ (hrange.choose (f x), hker.choose x) :=
  funext <| implicitToOpenPartialHomeomorphOfComplementedKerRange_apply hf hker hrange

theorem isInvertible_fderiv_implicitToOpenPartialHomeomorphOfComplementedKerRange
    {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) :
    (fderiv 𝕜 (hf.implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hker hrange)
      a).IsInvertible := by
  letI := hrange.isClosed.completeSpace_coe
  rw [hf.coe_implicitToOpenPartialHomeomorphOfComplementedKerRange hker hrange]
  have hderiv :
      HasStrictFDerivAt (fun x ↦ (hrange.choose (f x), hker.choose x))
        ((hrange.choose ∘L f').prod (hker.choose : E →L[𝕜] f'.ker)) a :=
    (hrange.choose.hasStrictFDerivAt.comp a hf).prodMk hker.choose.hasStrictFDerivAt
  have hrange_eq : (hrange.choose ∘L f').range = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨_, x, rfl⟩
    refine ⟨x, ?_⟩
    exact hrange.choose_spec ⟨f' x, by simp⟩
  have hker_range : (hker.choose : E →L[𝕜] f'.ker).range = ⊤ :=
    LinearMap.range_eq_of_proj hker.choose_spec
  have hker_eq : (hrange.choose ∘L f').ker = f'.ker := by
    ext x
    constructor
    · intro hx
      have hx0 : hrange.choose (f' x) = 0 := by simpa using hx
      have hspec := hrange.choose_spec ⟨f' x, by simp⟩
      have : (⟨f' x, by simp⟩ : f'.range) = 0 := by
        rw [← hspec, hx0]
      simpa using congrArg Subtype.val this
    · intro hx
      have : f' x = 0 := by simpa using hx
      simp [this]
  have hcompl : IsCompl (hrange.choose ∘L f').ker hker.choose.ker := by
    rw [hker_eq]
    exact LinearMap.isCompl_of_proj hker.choose_spec
  let e :=
    (hrange.choose ∘L f').equivProdOfSurjectiveOfIsCompl
      (hker.choose : E →L[𝕜] f'.ker) hrange_eq hker_range hcompl
  have hderiv' :
      HasStrictFDerivAt (fun x ↦ (hrange.choose (f x), hker.choose x)) (e : E →L[𝕜] _) a := by
    convert hderiv
    ext x <;> simp [e]
  rw [hderiv'.hasFDerivAt.fderiv]
  exact ContinuousLinearMap.isInvertible_equiv

@[simp]
theorem implicitToOpenPartialHomeomorphOfComplementedKerRange_apply_fst {f : E → F} {f' : E →L[𝕜] F}
    {a : E} (hf : HasStrictFDerivAt f f' a) (hker : f'.ker.ClosedComplemented)
    (hrange : f'.range.ClosedComplemented) (x : E) :
    (implicitToOpenPartialHomeomorphOfComplementedKerRange f f' hf hker hrange x).fst =
      hrange.choose (f x) := by
  simp [implicitToOpenPartialHomeomorphOfComplementedKerRange_apply]

end HasStrictFDerivAt
