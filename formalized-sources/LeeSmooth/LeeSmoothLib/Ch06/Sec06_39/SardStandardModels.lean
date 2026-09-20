import LeeSmoothLib.External.SardMoreira.MainTheorem
import LeeSmoothLib.Ch01.Sec01_06.Definition_1_6_extra_1
import LeeSmoothLib.Ch05.Sec05_30.Definition_5_30_extra_2
import LeeSmoothLib.Ch05.Sec05_35.Proposition_5_37
import LeeSmoothLib.Ch06.Sec06_38.Definition_6_38_extra_2

noncomputable section

open MeasureTheory
open Manifold
open scoped ContDiff Manifold Topology

namespace SardStandardModels

/-!
This file is deliberately separate from `Theorem_6_10` and from the strict-core port.  The
ambient Moreira theorem is used directly here.  In particular, no theorem saying that arbitrary
pointwise `ContDiffWithinAt ℝ ∞` data extends across a model boundary is introduced.
-/

universe u v

section Ambient

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- The local extension datum needed to apply the ambient Moreira theorem on a model range. -/
abbrev HasLocalAmbientExtension
    (r s : Set E) (f : E → F) : Prop :=
  ∀ x ∈ s, ∃ U : Set E, IsOpen U ∧ x ∈ U ∧
    ∃ g : E → F, ContDiffOn ℝ ∞ g U ∧ Set.EqOn g f (U ∩ r)

/--
An ambient Sard endpoint for a marked subset of a model range.

The extension premise is explicit on purpose.  It is exactly what is needed to compare the
within derivative of `f` with the ordinary derivative of a local ambient extension.  The proof is
the countable-subtype-neighborhood argument, with the actual nullity supplied by
`External.SardMoreira.MainTheorem`.
-/
theorem ambientCriticalImage_measureZero_of_localAmbientExtension
    {I : ModelWithCorners ℝ E H} {s : Set E} {f : E → F}
    (μ : Measure F) [μ.IsAddHaarMeasure]
    (hst : s ⊆ Set.range I)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderivWithin ℝ f (Set.range I) x))
    (hExt : HasLocalAmbientExtension (Set.range I) s f) :
    μ (f '' s) = 0 := by
  classical
  let u : s → Set E := fun x => Classical.choose (hExt x.1 x.2)
  let g : s → E → F :=
    fun x => Classical.choose (Classical.choose_spec (hExt x.1 x.2)).2.2
  have hu_open : ∀ x : s, IsOpen (u x) := by
    intro x
    exact (Classical.choose_spec (hExt x.1 x.2)).1
  have hu_mem : ∀ x : s, x.1 ∈ u x := by
    intro x
    exact (Classical.choose_spec (hExt x.1 x.2)).2.1
  have hg : ∀ x : s, ContDiffOn ℝ ∞ (g x) (u x) := by
    intro x
    exact (Classical.choose_spec (Classical.choose_spec (hExt x.1 x.2)).2.2).1
  have heq : ∀ x : s, Set.EqOn (g x) f (u x ∩ Set.range I) := by
    intro x
    exact (Classical.choose_spec (Classical.choose_spec (hExt x.1 x.2)).2.2).2
  have hlocal : ∀ x ∈ s, ∃ v ∈ 𝓝[s] x, μ (f '' v) = 0 := by
    intro x hx
    let xs : s := ⟨x, hx⟩
    let U := u xs
    let gg := g xs
    have hcritg : ∀ y ∈ U ∩ s, ¬ Function.Surjective (fderiv ℝ gg y) := by
      intro y hy hsurj
      have hyR : y ∈ Set.range I := hst hy.2
      have hEqAt : gg y = f y := heq xs ⟨hy.1, hyR⟩
      have hEqDeriv : fderivWithin ℝ gg (Set.range I) y =
          fderivWithin ℝ f (Set.range I) y := by
        have hev : gg =ᶠ[𝓝[Set.range I] y] f := by
          filter_upwards [mem_nhdsWithin_of_mem_nhds ((hu_open xs).mem_nhds hy.1),
            self_mem_nhdsWithin] with z hzU hzR
          exact heq xs ⟨hzU, hzR⟩
        exact hev.fderivWithin_eq hEqAt
      have hDerivAmbient : fderiv ℝ gg y = fderivWithin ℝ f (Set.range I) y := by
        rw [← hEqDeriv]
        have hggDiff : DifferentiableAt ℝ gg y :=
          ((hg xs).contDiffAt ((hu_open xs).mem_nhds hy.1)).differentiableAt
            (by simp : (∞ : WithTop ℕ∞) ≠ 0)
        exact (fderivWithin_eq_fderiv (f := gg)
          (I.uniqueDiffOn.uniqueDiffWithinAt hyR) hggDiff).symm
      exact hcrit y hy.2 (by simpa [hDerivAmbient] using hsurj)
    have hz : μ (gg '' {y ∈ U | ¬ Function.Surjective (fderiv ℝ gg y)}) = 0 :=
      addHaar_image_critical_eq_zero_of_contDiffOn (hu_open xs) (hg xs) μ
    have hsub : gg '' (U ∩ s) ⊆
        gg '' {y ∈ U | ¬ Function.Surjective (fderiv ℝ gg y)} := by
      intro z hz'
      rcases hz' with ⟨y, hy, rfl⟩
      exact ⟨y, ⟨hy.1, hcritg y hy⟩, rfl⟩
    have hzero_g : μ (gg '' (U ∩ s)) = 0 := measure_mono_null hsub hz
    have hEqImage : f '' (U ∩ s) = gg '' (U ∩ s) := by
      apply Set.EqOn.image_eq
      intro y hy
      exact (heq xs ⟨hy.1, hst hy.2⟩).symm
    refine ⟨U ∩ s, ?_, ?_⟩
    ·
      rw [Set.inter_comm]
      simpa [U, xs] using (inter_mem_nhdsWithin s
        ((hu_open xs).mem_nhds (hu_mem xs)))
    · rw [hEqImage]
      exact hzero_g
  let V : s → Set s := fun x =>
    Subtype.val ⁻¹' (Classical.choose (hlocal x.1 x.2))
  have hV_nhds : ∀ x : s, V x ∈ 𝓝 x := by
    intro x
    exact preimage_coe_mem_nhds_subtype.2 (Classical.choose_spec (hlocal x.1 x.2)).1
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  have hsub : f '' s ⊆ ⋃ x ∈ t, f '' (Classical.choose (hlocal x.1 x.2)) := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    let xs : s := ⟨x, hx⟩
    have hxs_cover : xs ∈ ⋃ x ∈ t, V x := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    exact ⟨x, by simpa [V] using hxp, rfl⟩
  exact measure_mono_null hsub <|
    (measure_biUnion_null_iff ht_countable).2 fun x hx =>
      (Classical.choose_spec (hlocal x.1 x.2)).2

end Ambient

section SelfModel

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Unconditional Sard nullity for a finite-dimensional real self-model. -/
theorem finiteDimensionalSelfModel_criticalImage_measureZero
    {f : E → F} (hf : ContDiff ℝ ∞ f)
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 := by
  exact addHaar_image_critical_eq_zero_of_contDiff hf μ

end SelfModel

section HalfSpace

variable {n k : ℕ} [NeZero n]

/--
Unconditional Sard nullity for an open subset of the standard real half-space.

The criticality predicate is written for the ambient coordinate representative
`z ↦ f ((𝓡∂ n).symm z)` and its derivative within the closed half-space.  Thus the conclusion is
about the actual subtype image `f '' ...`, while the proof applies the ambient theorem locally.
The hypothesis is `ContMDiffOn` on the whole open set, not merely pointwise smoothness at each
point; this preserves the order of the quantifiers needed by the Seeley extension step.
-/
theorem halfSpace_criticalImage_measureZero
    {U : Set (EuclideanHalfSpace n)}
    {f : EuclideanHalfSpace n → EuclideanSpace ℝ (Fin k)}
    (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡∂ n) (𝓡 k) ∞ f U)
    (μ : Measure (EuclideanSpace ℝ (Fin k)))
    [μ.IsAddHaarMeasure] :
    μ (f '' {x ∈ U | ¬ Function.Surjective
      (fderivWithin ℝ
        (fun z : EuclideanSpace ℝ (Fin n) ↦ f ((𝓡∂ n).symm z))
        (Set.range (𝓡∂ n)) x.1)}) = 0 := by
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k) :=
    fun z ↦ f ((𝓡∂ n).symm z)
  let C : Set (EuclideanHalfSpace n) :=
    {x ∈ U | ¬ Function.Surjective (fderivWithin ℝ F (Set.range (𝓡∂ n)) x.1)}
  let s : Set (EuclideanSpace ℝ (Fin n)) := (𝓡∂ n) '' C
  have hCont : ContDiffOn ℝ ∞ F ((𝓡∂ n) '' U) := by
    exact (contMDiffOn_halfSpace_iff_contDiffOn_image (U := U) (f := f)).mp hf
  have hExtSubtype : ∀ x ∈ U,
      ∃ V : Set (EuclideanSpace ℝ (Fin n)),
        IsOpen V ∧ x.1 ∈ V ∧ ((𝓡∂ n) ⁻¹' V) ⊆ U ∧
        ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin k),
          ContDiffOn ℝ ∞ g V ∧
          Set.EqOn (fun z : EuclideanHalfSpace n ↦ g z.1) f ((𝓡∂ n) ⁻¹' V) := by
    exact forall_exists_smoothAmbientExtension_of_contDiffOn_halfSpace_image
      (U := U) (f := f) hU hCont
  have hst : s ⊆ Set.range (𝓡∂ n) := by
    intro z hz
    rcases hz with ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  have hcrit' : ∀ z ∈ s, ¬ Function.Surjective
      (fderivWithin ℝ F (Set.range (𝓡∂ n)) z) := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact hx.2
  have hExt : HasLocalAmbientExtension (Set.range (𝓡∂ n)) s F := by
    intro z hz
    rcases hz with ⟨x, hxC, rfl⟩
    rcases hExtSubtype x hxC.1 with ⟨V, hV, hxV, hVU, g, hg, hEq⟩
    refine ⟨V, hV, hxV, g, hg, ?_⟩
    exact (eqOn_halfSpace_preimage_iff_eqOn_range_inter
      (f := f) (V := V) (g := g)).mp hEq
  have hzero : μ (F '' s) = 0 :=
    ambientCriticalImage_measureZero_of_localAmbientExtension
      (I := 𝓡∂ n) μ hst hcrit' hExt
  have himage : f '' C = F '' s := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨(𝓡∂ n) x, ⟨x, hx, rfl⟩, ?_⟩
      simp [F]
    · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simp [F]
  rw [himage]
  exact hzero

end HalfSpace

section SelfManifold

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold (𝓘(ℝ, E)) ∞ M] [T2Space M] [SecondCountableTopology M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace F N]
  [IsManifold (𝓘(ℝ, F)) ∞ N] [T2Space N] [SecondCountableTopology N]

private theorem selfModel_coordinateRepresentative_hasFDerivWithinAt
    {Φ : M → N} (hΦ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ Φ)
    {e : OpenPartialHomeomorph N F}
    (he : e ∈ IsManifold.maximalAtlas (𝓘(ℝ, F)) ∞ N)
    {p x : M} (hx : x ∈ (extChartAt (𝓘(ℝ, E)) p).source)
    (hy : Φ x ∈ e.source) :
    HasFDerivWithinAt
      (e.extend (𝓘(ℝ, F)) ∘ Φ ∘ (extChartAt (𝓘(ℝ, E)) p).symm)
      ((mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) (e.extend (𝓘(ℝ, F))) (Φ x)) ∘L
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x) ∘L
        (mfderivWithin (𝓘(ℝ, E)) (𝓘(ℝ, E))
          (extChartAt (𝓘(ℝ, E)) p).symm Set.univ
          ((extChartAt (𝓘(ℝ, E)) p) x)))
      Set.univ ((extChartAt (𝓘(ℝ, E)) p) x) := by
  let φ := extChartAt (𝓘(ℝ, E)) p
  let ψ := e.extend (𝓘(ℝ, F))
  have hφleft : φ.symm (φ x) = x := φ.left_inv hx
  have hxTarget : φ x ∈ φ.target := φ.map_source hx
  have hφdiff :
      MDifferentiableWithinAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm Set.univ (φ x) := by
    simpa [φ] using (mdifferentiableWithinAt_extChartAt_symm hxTarget)
  have hΦdiff : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x :=
    hΦ.contMDiffAt.mdifferentiableAt (by simp)
  have hΦdiff' :
      HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ (φ.symm (φ x))
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x) := by
    rw [show φ.symm (φ x) = x by exact hφleft]
    exact hΦdiff.hasMFDerivAt
  have hψdiff : MDifferentiableAt (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x) := by
    exact mdifferentiableAt_extend_of_mem_maximalAtlas he hy
  have hψdiff' :
      HasMFDerivAt (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ (φ.symm (φ x)))
        (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)) := by
    rw [show Φ (φ.symm (φ x)) = Φ x by rw [hφleft]]
    exact hψdiff.hasMFDerivAt
  have hΦcomp :
      HasMFDerivWithinAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) (Φ ∘ φ.symm) Set.univ (φ x)
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x) ∘L
          (mfderivWithin (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm Set.univ (φ x))) := by
    exact hΦdiff'.comp_hasMFDerivWithinAt (φ x) hφdiff.hasMFDerivWithinAt
  have hcoord :
      HasMFDerivWithinAt (𝓘(ℝ, E)) (𝓘(ℝ, F)) (ψ ∘ Φ ∘ φ.symm) Set.univ (φ x)
        ((mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)) ∘L
          (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x) ∘L
          (mfderivWithin (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm Set.univ (φ x))) := by
    simpa [Function.comp] using hψdiff'.comp_hasMFDerivWithinAt (φ x) hΦcomp
  simpa [φ, ψ, Function.comp] using hcoord.hasFDerivWithinAt

private theorem selfModel_coordinateRepresentative_not_surjective
    {Φ : M → N} (hΦ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ Φ)
    {e : OpenPartialHomeomorph N F}
    (he : e ∈ IsManifold.maximalAtlas (𝓘(ℝ, F)) ∞ N)
    {p x : M} (hx : x ∈ (extChartAt (𝓘(ℝ, E)) p).source)
    (hy : Φ x ∈ e.source)
    (hcrit : ¬ Function.Surjective
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x)) :
    ¬ Function.Surjective
      (fderivWithin ℝ
        (e.extend (𝓘(ℝ, F)) ∘ Φ ∘ (extChartAt (𝓘(ℝ, E)) p).symm)
        Set.univ ((extChartAt (𝓘(ℝ, E)) p) x)) := by
  let φ := extChartAt (𝓘(ℝ, E)) p
  let ψ := e.extend (𝓘(ℝ, F))
  have hφleft : φ.symm (φ x) = x := φ.left_inv hx
  have hcoord := selfModel_coordinateRepresentative_hasFDerivWithinAt hΦ he hx hy
  have hformula :
      fderivWithin ℝ (ψ ∘ Φ ∘ φ.symm) Set.univ (φ x) =
        (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)) ∘L
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x) ∘L
          (mfderivWithin (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm Set.univ (φ x)) := by
    have hEq := (uniqueDiffOn_univ.uniqueDiffWithinAt (by simp)).eq
      hcoord hcoord.differentiableWithinAt.hasFDerivWithinAt
    simpa [ψ, φ, hφleft] using hEq.symm
  have hψinv :
      (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)).IsInvertible := by
    exact isInvertible_mfderiv_extend_of_mem_maximalAtlas he hy
  intro hsurj
  have hcomp : Function.Surjective
      ((mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)) ∘L
        (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x) ∘L
        (mfderivWithin (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm Set.univ (φ x))) := by
    rw [← hformula]
    exact hsurj
  apply hcrit
  intro y
  obtain ⟨z, hz⟩ := hcomp
    ((mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)) y)
  refine ⟨(mfderivWithin (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm Set.univ (φ x)) z, ?_⟩
  change
    (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x))
        ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x)
          ((mfderivWithin (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm Set.univ (φ x)) z)) =
      (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)) y at hz
  have hA :
      (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x)
        ((mfderivWithin (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm Set.univ (φ x)) z) = y := by
    calc
      _ = (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)).inverse
          ((mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x))
            ((mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x)
              ((mfderivWithin (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ.symm Set.univ (φ x)) z))) := by
            rw [hψinv.inverse_apply_self]
      _ = (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)).inverse
          ((mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)) y) := by
            exact congrArg
              (fun w ↦
                (mfderiv (𝓘(ℝ, F)) (𝓘(ℝ, F)) ψ (Φ x)).inverse w)
              hz
      _ = y := hψinv.inverse_apply_self y
  exact hA

/-- Unconditional Sard nullity for smooth maps between finite-dimensional manifolds whose model
spaces are the standard real self-models.  The proof is chartwise: a source chart piece is open in
the Euclidean model, ambient Sard is applied to its coordinate representative, and a countable
source-chart cover assembles the target-chart image. -/
theorem criticalValues_has_measure_zero_in_manifold_of_contMDiff_selfModel
    {Φ : M → N} (hΦ : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, F)) ∞ Φ) :
    has_measure_zero_in_manifold (𝓘(ℝ, F))
      {y : N | IsCriticalValue (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ y} := by
  classical
  intro μ hμ e he
  letI : μ.IsAddHaarMeasure := hμ
  let s : Set M :=
    {x : M | IsCriticalPoint (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ x ∧ Φ x ∈ e.source}
  let V : s → Set s := fun p ↦
    Subtype.val ⁻¹' (extChartAt (𝓘(ℝ, E)) p.1).source
  have hV_nhds : ∀ p : s, V p ∈ 𝓝 p := by
    intro p
    exact preimage_coe_mem_nhds_subtype.2 <|
      mem_nhdsWithin_of_mem_nhds
        (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) p.1)
  obtain ⟨t, ht_countable, ht_cover⟩ := LindelofSpace.elim_nhds_subcover V hV_nhds
  let sourceSet : s → Set M := fun p ↦
    (extChartAt (𝓘(ℝ, E)) p.1).source ∩ Φ ⁻¹' e.source
  let sourcePiece : s → Set E := fun p ↦
    (extChartAt (𝓘(ℝ, E)) p.1) '' sourceSet p
  let rep : s → E → F := fun p ↦
    e.extend (𝓘(ℝ, F)) ∘ Φ ∘ (extChartAt (𝓘(ℝ, E)) p.1).symm
  have hpiece_zero : ∀ p ∈ t,
      μ (rep p '' {z ∈ sourcePiece p | ¬ Function.Surjective
        (fderiv ℝ (rep p) z)}) = 0 := by
    intro p hp
    have hsourceSet_open : IsOpen (sourceSet p) := by
      exact (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) p.1).inter
        (e.open_source.preimage hΦ.continuous)
    have hsource_subset : sourceSet p ⊆
        (chartAt E p.1).source := by
      intro x hx
      simpa [sourceSet, extChartAt_source] using hx.1
    have hmapsTo : Set.MapsTo Φ (sourceSet p) e.source := by
      intro x hx
      exact hx.2
    have hsourcePiece_open : IsOpen (sourcePiece p) := by
      have hsourcePiece_eq : sourcePiece p = (chartAt E p.1) '' sourceSet p := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, rfl⟩
      rw [hsourcePiece_eq]
      exact (chartAt E p.1).isOpen_image_of_subset_source hsourceSet_open
        hsource_subset
    have hrep_contDiff : ContDiffOn ℝ ∞ (rep p) (sourcePiece p) := by
      exact
        (contMDiffOn_iff_of_mem_maximalAtlas'
          (show chartAt E p.1 ∈ IsManifold.maximalAtlas (𝓘(ℝ, E)) ∞ M from
            IsManifold.chart_mem_maximalAtlas p.1)
          he hsource_subset hmapsTo).1 <|
          hΦ.contMDiffOn.mono (Set.subset_univ _)
    exact addHaar_image_critical_eq_zero_of_contDiffOn
      hsourcePiece_open hrep_contDiff μ
  have hsubset :
      (e.extend (𝓘(ℝ, F)) ''
        ({y : N | IsCriticalValue (𝓘(ℝ, E)) (𝓘(ℝ, F)) Φ y} ∩ e.source)) ⊆
        ⋃ p ∈ t, rep p '' {z ∈ sourcePiece p | ¬ Function.Surjective
          (fderiv ℝ (rep p) z)} := by
    intro z hz
    rcases hz with ⟨y, hy, rfl⟩
    rcases (isCriticalValue_iff_exists_critical_point Φ y).1 hy.1 with
      ⟨x, rfl, hcrit⟩
    let xs : s := ⟨x, ⟨hcrit, hy.2⟩⟩
    have hxs_cover : xs ∈ ⋃ p ∈ t, V p := by
      rw [ht_cover]
      simp
    rcases Set.mem_iUnion₂.1 hxs_cover with ⟨p, hp, hxp⟩
    have hx_source : x ∈ (extChartAt (𝓘(ℝ, E)) p.1).source := by
      simpa [V] using hxp
    refine Set.mem_iUnion₂.2 ⟨p, hp, ?_⟩
    refine ⟨(extChartAt (𝓘(ℝ, E)) p.1) x, ?_, ?_⟩
    · refine ⟨⟨x, ⟨hx_source, hy.2⟩, rfl⟩, ?_⟩
      simpa [rep, mfderivWithin_univ] using
        (selfModel_coordinateRepresentative_not_surjective
          hΦ he hx_source hy.2 hcrit)
    · change (e.extend (𝓘(ℝ, F)))
        (Φ ((extChartAt (𝓘(ℝ, E)) p.1).symm
          ((extChartAt (𝓘(ℝ, E)) p.1) x))) =
        (e.extend (𝓘(ℝ, F))) (Φ x)
      rw [(extChartAt (𝓘(ℝ, E)) p.1).left_inv hx_source]
  exact measure_mono_null hsubset <|
    (measure_biUnion_null_iff ht_countable).2 hpiece_zero

end SelfManifold

end SardStandardModels
