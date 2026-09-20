import LeeSmoothLib.Ch04.Sec04_22.Theorem_4_5
import LeeSmoothLib.Ch05.Sec05_37.BoundaryPreimageCharts
import LeeSmoothLib.Ch05.Sec05_37.CInfinityNeatSliceAtlas
import LeeSmoothLib.Ch05.Sec05_37.BoundaryRegularPreimageChart

/-!
# Interior neat-slice charts for Problem 5-23

At an interior fibre point of a `C∞` map from a standard half-space manifold, the preferred
extended chart is an ordinary Euclidean chart on an open neighbourhood.  The inverse function
theorem therefore applies without a Seeley extension.  The resulting Euclidean local diffeomorphism
is arranged so that the free-first (normal) coordinate equals `1` at the base point, then shrunk
so that both this coordinate and the original normal coordinate stay positive.  Restriction to the
closed half-space is then automatic, and the preferred half-space chart transcribes the local
diffeomorphism into a `C∞` neat-slice chart.

This is the interior pointwise leaf.  The boundary leaf is handled separately.
-/

open Set ChartedSpace
open scoped ContDiff Manifold Topology

noncomputable section

namespace Manifold
namespace InteriorRegularPreimageChart

open BoundaryPreimageCharts

universe uM uN

variable {n m : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold (𝓡 m) ∞ N]

local notation "I∂" => 𝓡∂ (n + 1)
local notation "Jm" => 𝓡 m
local notation "Eₙ" => EuclideanSpace ℝ (Fin (n + 1))
local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Hk" => EuclideanSpace ℝ (Fin ((n - m) + 1))

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-! ### Euclidean open half-space geometry -/

theorem isOpen_openHalfSpace {k : ℕ} [NeZero k] :
    IsOpen {z : EuclideanSpace ℝ (Fin k) | 0 < z 0} :=
  isOpen_lt continuous_const
    (PiLp.continuous_apply 2 (fun _ : Fin k => ℝ) 0)

theorem interiorChartTarget_subset_openHalfSpace
    (p : M) (hp : I∂.IsInteriorPoint p) :
    interiorChartTarget (n := n) p hp ⊆ {z : Eₙ | 0 < z 0} := by
  have hopen := isOpen_interiorChartTarget (n := n) p hp
  have hsub : interiorChartTarget (n := n) p hp ⊆ range I∂ :=
    (interiorChartTarget_subset (n := n) p hp).trans
      (extChartAt_target_subset_range (I := I∂) p)
  have hinter := interior_maximal hsub hopen
  simpa [interior_range_modelWithCornersEuclideanHalfSpace] using hinter

theorem dim_cast_free (hmn : m ≤ n) : n + 1 - m = n - m + 1 := by omega

/-- Identify the complementary factor produced by `exists_rank_coordinates` with the free factor
used by `standardConcatEquiv`. -/
def freeCoordCast (hmn : m ≤ n) :
    EuclideanSpace ℝ (Fin (n + 1 - m)) ≃L[ℝ] Hk :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Fin.castOrderIso (dim_cast_free (n := n) (m := m) hmn)).toEquiv).toContinuousLinearEquiv

theorem standardConcatEquiv_add_unit (hmn : m ≤ n)
    (u : Hk) (v : Eₘ) :
    standardConcatEquiv n m hmn (u, v) +
        standardConcatEquiv n m hmn (EuclideanSpace.single 0 1, 0) =
      standardConcatEquiv n m hmn (u + EuclideanSpace.single 0 1, v) := by
  rw [← map_add]
  simp

theorem standardConcatEquiv_unit_zero (hmn : m ≤ n) :
    standardConcatEquiv n m hmn (EuclideanSpace.single 0 1, 0) 0 = 1 := by
  simpa [EuclideanSpace.single_apply] using
    standardConcatEquiv_apply_zero n m hmn (EuclideanSpace.single 0 1) 0

/-! ### Euclidean IFT straightening at an interior fibre point -/

/-- Euclidean local diffeomorphism produced by the inverse function theorem at an interior
regular fibre point, already shifted so that the free-first coordinate equals `1` at the base
point and already restricted to the open half-space. -/
structure InteriorEuclideanStraightening
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) where
  Ψ : OpenPartialHomeomorph Eₙ Eₙ
  mem_source : extChartAt I∂ p p ∈ Ψ.source
  source_subset_openHalf : Ψ.source ⊆ {z : Eₙ | 0 < z 0}
  target_subset_openHalf : Ψ.target ⊆ {z : Eₙ | 0 < z 0}
  source_subset_interiorChart :
    Ψ.source ⊆ interiorChartTarget (n := n) p hpInterior
  source_subset_codomain :
    Ψ.source ⊆
      (F ∘ (extChartAt I∂ p).symm) ⁻¹' (extChartAt Jm (F p)).source
  contDiffOn_toFun : ContDiffOn ℝ ∞ Ψ Ψ.source
  contDiffOn_invFun : ContDiffOn ℝ ∞ Ψ.symm Ψ.target
  fiber_iff : ∀ z ∈ Ψ.source,
    ((standardConcatEquiv n m hmn).symm (Ψ z)).2 = 0 ↔
      F ((extChartAt I∂ p).symm z) = c

/-- Inverse-function-theorem construction of the Euclidean straightening at an interior
regular fibre point. -/
theorem exists_interiorEuclideanStraightening
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    Nonempty (InteriorEuclideanStraightening hmn hF hpInterior hFp hpSurj) := by
  let A : Eₙ →L[ℝ] Eₘ := mfderiv I∂ Jm F p
  unfold TangentSpace at A
  have hArank : Module.finrank ℝ A.range = m := by
    rw [LinearMap.range_eq_top.mpr hpSurj, finrank_top]
    simp
  obtain ⟨hrm, hrn, d0, cLin, hcoord⟩ := exists_rank_coordinates A hArank
  let dY := freeCoordCast (n := n) (m := m) hmn
  let d : Eₙ ≃L[ℝ] (Eₘ × Hk) :=
    d0.trans ((ContinuousLinearEquiv.refl ℝ Eₘ).prodCongr dY)
  let g : Eₙ → Eₘ := writtenInExtChartAt I∂ Jm p F
  let a : Eₙ := extChartAt I∂ p p
  let b : Eₘ := extChartAt Jm (F p) (F p)
  let Ω0 : Set Eₙ :=
    interiorChartTarget (n := n) p hpInterior ∩
      (F ∘ (extChartAt I∂ p).symm) ⁻¹' (extChartAt Jm (F p)).source
  let affine : (Eₘ × Hk) → Eₙ := fun w ↦ d.symm w + a
  let Ω : Set (Eₘ × Hk) := affine ⁻¹' Ω0
  let qfun : (Eₘ × Hk) → Eₘ := fun w ↦ (cLin (g (affine w) - b)).1
  let G : (Eₘ × Hk) → (Eₘ × Hk) := fun w ↦ (qfun w, w.2)
  have hΩ0_target : interiorChartTarget (n := n) p hpInterior ∈ nhds a :=
    (isOpen_interiorChartTarget (n := n) p hpInterior).mem_nhds
      (mem_interiorChartTarget (n := n) p hpInterior)
  have hΩ0_source :
      (F ∘ (extChartAt I∂ p).symm) ⁻¹' (extChartAt Jm (F p)).source ∈ nhds a := by
    convert extChartAt_preimage_mem_nhds (I := I∂) (x := p)
      (hF.continuous.continuousAt.preimage_mem_nhds
        (extChartAt_source_mem_nhds (I := Jm) (F p))) using 1 <;>
      ext x <;> rfl
  have hΩ0 : Ω0 ∈ nhds a := Filter.inter_mem hΩ0_target hΩ0_source
  have haffine_cont : Continuous affine := d.symm.continuous.add continuous_const
  have haffine_zero : affine 0 = a := by simp [affine]
  have hΩ : Ω ∈ nhds (0 : Eₘ × Hk) := by
    have hΩ0' : Ω0 ∈ nhds (affine 0) := by simpa [haffine_zero] using hΩ0
    simpa [Ω] using haffine_cont.continuousAt.preimage_mem_nhds hΩ0'
  have hgΩ0 : ContDiffOn ℝ ∞ g
      ((extChartAt I∂ p).target ∩
        (F ∘ (extChartAt I∂ p).symm) ⁻¹' (extChartAt Jm (F p)).source) := by
    simpa [g] using
      writtenInExtChartAt_contDiffOn_of_contMDiff
        (I := I∂) (J := Jm) (n := ∞) (f := F) (p := p) hF
  have hΩ0_subset_ext :
      Ω0 ⊆ (extChartAt I∂ p).target ∩
        (F ∘ (extChartAt I∂ p).symm) ⁻¹' (extChartAt Jm (F p)).source :=
    inter_subset_inter_left _
      (interiorChartTarget_subset (n := n) p hpInterior)
  have hgΩ0' : ContDiffOn ℝ ∞ g Ω0 := hgΩ0.mono hΩ0_subset_ext
  have haffine_smooth : ContDiff ℝ ∞ affine := d.symm.contDiff.add contDiff_const
  have hqΩ : ContDiffOn ℝ ∞ qfun Ω := by
    have hgin : ContDiffOn ℝ ∞ (fun w ↦ g (affine w)) Ω :=
      hgΩ0'.comp haffine_smooth.contDiffOn (fun _ hw ↦ hw)
    have hsub : ContDiffOn ℝ ∞ (fun w ↦ g (affine w) - b) Ω :=
      hgin.sub contDiffOn_const
    have hccomp : ContDiffOn ℝ ∞ (fun w ↦ cLin (g (affine w) - b)) Ω :=
      cLin.contDiff.contDiffOn.comp hsub (fun _ _ ↦ mem_univ _)
    exact contDiffOn_fst.comp hccomp (fun _ _ ↦ mem_univ _)
  have hgDeriv : HasFDerivAt g A a := by
    simpa [g, A, a] using
      writtenInExtChartAt_hasFDerivAt_of_isInteriorPoint
        (I := I∂) (J := Jm) (f := F) (p := p) hpInterior
        (hF.contMDiffAt.mdifferentiableAt (by simp)).hasMFDerivAt
  have haffineDeriv :
      HasFDerivAt affine (d.symm : (Eₘ × Hk) →L[ℝ] Eₙ) 0 := by
    simpa [affine] using d.symm.hasFDerivAt.add_const a
  -- Derivative of `qfun` in the original rank coordinates, transported along `dY`.
  have hcoord' : ∀ w : Eₘ × Hk, (cLin (A (d.symm w))).1 = w.1 := by
    intro w
    -- `d.symm (x, y) = d0.symm (x, dY.symm y)`, and `hcoord` projects onto the first factor.
    have hw : d.symm w = d0.symm (w.1, dY.symm w.2) := rfl
    have h0 := hcoord (d0.symm (w.1, dY.symm w.2))
    have hA : A (d.symm w) = A (d0.symm (w.1, dY.symm w.2)) := by rw [hw]
    have hdw : d0 (d0.symm (w.1, dY.symm w.2)) = (w.1, dY.symm w.2) := by simp
    have : (cLin (A (d0.symm (w.1, dY.symm w.2)))).1 = w.1 := by
      simpa [hdw] using congrArg Prod.fst h0
    simpa [hA] using this
  let q' : (Eₘ × Hk) →L[ℝ] Eₘ :=
    (ContinuousLinearMap.fst ℝ Eₘ (EuclideanSpace ℝ (Fin (m - m)))).comp
      ((cLin : Eₘ →L[ℝ] (Eₘ × EuclideanSpace ℝ (Fin (m - m)))).comp
        (A.comp (d.symm : (Eₘ × Hk) →L[ℝ] Eₙ)))
  have hqDeriv : HasFDerivAt qfun q' 0 := by
    have hgDeriv' : HasFDerivAt g A (affine 0) := by simpa [haffine_zero] using hgDeriv
    have h1 := hgDeriv'.comp (0 : Eₘ × Hk) haffineDeriv
    have h2 := h1.sub_const b
    have h3 := cLin.hasFDerivAt.comp (0 : Eₘ × Hk) h2
    have h4 := h3.fst
    simpa [qfun, affine, q', Function.comp_def] using h4
  have hnormal : ∀ w : Eₘ × Hk, q' w = w.1 := by
    intro w
    simpa [q'] using hcoord' w
  let Lderiv : (Eₘ × Hk) →L[ℝ] (Eₘ × Hk) :=
    q'.prod (ContinuousLinearMap.snd ℝ Eₘ Hk)
  have hGDerivL : HasFDerivAt G Lderiv 0 := by
    simpa [G, Lderiv] using
      hqDeriv.prodMk (hasFDerivAt_snd (𝕜 := ℝ) (E := Eₘ) (F := Hk))
  have hL_apply : ∀ w : Eₘ × Hk, Lderiv w = w := by
    intro w
    change (q' w, w.2) = w
    rw [hnormal]
  have hGDeriv : HasFDerivAt G (ContinuousLinearMap.id ℝ (Eₘ × Hk)) 0 := by
    have heq : Lderiv = ContinuousLinearMap.id ℝ (Eₘ × Hk) :=
      ContinuousLinearMap.ext hL_apply
    rwa [heq] at hGDerivL
  have hGΩ : ContDiffOn ℝ ∞ G Ω := by
    simpa [G] using hqΩ.prodMk contDiffOn_snd
  have hGAt : ContDiffAt ℝ ∞ G 0 := hGΩ.contDiffAt hΩ
  have hGInv : (fderiv ℝ G 0).IsInvertible := by
    rw [hGDeriv.fderiv]
    exact ⟨ContinuousLinearEquiv.refl ℝ (Eₘ × Hk), rfl⟩
  obtain ⟨ΨG, h0ΨG, hΨGΩ, _hΨGtarget, hΨGeq⟩ :=
    model_partialDiffeomorph_of_inverse_function_theorem
      (𝕜 := ℝ) (E := Eₘ × Hk) (F := Eₘ × Hk)
      (g := G) (a := 0) (Ω := Ω) (T := Set.univ)
      (f' := ContinuousLinearEquiv.refl ℝ (Eₘ × Hk))
      hΩ hGΩ (fun _ _ ↦ mem_univ _) hGAt hGDeriv (by simp) hGInv
  have hgbase : g a = b := by
    simp only [g, a, b, writtenInExtChartAt, Function.comp_apply]
    rw [(extChartAt I∂ p).left_inv (mem_extChartAt_source (I := I∂) p)]
  have hqzero : qfun 0 = 0 := by
    have : cLin (g (affine 0) - b) = 0 := by
      simp [haffine_zero, hgbase]
    simpa [qfun] using congrArg Prod.fst this
  have hGzero : G 0 = 0 := by simp [G, hqzero]
  have hΨGzero : ΨG 0 = 0 := by
    rw [← hΨGeq h0ΨG, hGzero]
  let unitFree : Hk := EuclideanSpace.single 0 1
  let e1 : Eₙ := standardConcatEquiv n m hmn (unitFree, 0)
  let center : Eₙ ≃ₘ[ℝ] (Eₘ × Hk) :=
    centeredLinearDiffeomorph d a
  let swapXY : (Eₘ × Hk) ≃ₘ[ℝ] (Hk × Eₘ) :=
    (ContinuousLinearEquiv.prodComm ℝ Eₘ Hk).toDiffeomorph
  let concat : (Hk × Eₘ) ≃ₘ[ℝ] Eₙ :=
    (standardConcatEquiv n m hmn).toDiffeomorph
  let shift : Eₙ ≃ₘ[ℝ] Eₙ :=
    centeredLinearDiffeomorph (ContinuousLinearEquiv.refl ℝ Eₙ) (-e1)
  let ΨP : PartialDiffeomorph 𝓘(ℝ, Eₙ) 𝓘(ℝ, Eₙ) Eₙ Eₙ ∞ :=
    (((center.toPartialDiffeomorph.trans ΨG).trans
      swapXY.toPartialDiffeomorph).trans
      concat.toPartialDiffeomorph).trans
      shift.toPartialDiffeomorph
  have haΨP : a ∈ ΨP.source := by
    refine ⟨⟨⟨⟨Set.mem_univ _, ?_⟩, Set.mem_univ _⟩, Set.mem_univ _⟩, Set.mem_univ _⟩
    change d (a - a) ∈ ΨG.source
    simpa using h0ΨG
  have hΨP_apply : ∀ z ∈ ΨP.source,
      ΨP z = standardConcatEquiv n m hmn
        ((ΨG (d (z - a))).2, (ΨG (d (z - a))).1) + e1 := by
    intro z _
    change _ - -e1 = _
    simp only [sub_neg_eq_add]
    rfl
  have hΨP_eqG : ∀ z ∈ ΨP.source,
      ΨG (d (z - a)) = G (d (z - a)) := by
    intro z hz
    have hzΨG : d (z - a) ∈ ΨG.source := hz.1.1.1.2
    exact (hΨGeq hzΨG).symm
  have haffine_d : ∀ z, affine (d (z - a)) = z := by
    intro z
    simp [affine]
  have hfiber_unrestricted : ∀ z ∈ ΨP.source,
      ((standardConcatEquiv n m hmn).symm (ΨP z)).2 = 0 ↔
        F ((extChartAt I∂ p).symm z) = c := by
    intro z hz
    have hΨGeq' := hΨP_eqG z hz
    have happly := hΨP_apply z hz
    have hlin :
        ΨP z =
          standardConcatEquiv n m hmn
            ((G (d (z - a))).2 + unitFree, (G (d (z - a))).1) := by
      rw [happly, hΨGeq']
      simpa [e1, G] using
        (standardConcatEquiv_add_unit (n := n) (m := m) hmn
          ((G (d (z - a))).2) ((G (d (z - a))).1))
    have hcomp :
        ((standardConcatEquiv n m hmn).symm (ΨP z)).2 = (G (d (z - a))).1 := by
      have := congrArg (fun w ↦ (standardConcatEquiv n m hmn).symm w) hlin
      simpa using congrArg Prod.snd this
    have hq : (G (d (z - a))).1 = qfun (d (z - a)) := rfl
    have hΩz : d (z - a) ∈ Ω := by
      have hzΨG : d (z - a) ∈ ΨG.source := by
        have hz' := hz
        simp [ΨP] at hz'
        exact hz'.1.1.1.2
      exact hΨGΩ hzΨG
    have hzΩ0 : z ∈ Ω0 := by
      change affine (d (z - a)) ∈ Ω0 at hΩz
      rw [haffine_d z] at hΩz
      exact hΩz
    have hgz : g z = extChartAt Jm (F p) (F ((extChartAt I∂ p).symm z)) := by
      simp only [g, writtenInExtChartAt, Function.comp_apply]
    have hinj :
        g z = b ↔ F ((extChartAt I∂ p).symm z) = c := by
      have hFsrc : F ((extChartAt I∂ p).symm z) ∈ (extChartAt Jm (F p)).source := hzΩ0.2
      have hcSrc : F p ∈ (extChartAt Jm (F p)).source :=
        mem_extChartAt_source (I := Jm) (F p)
      constructor
      · intro hg
        have hchart : extChartAt Jm (F p) (F ((extChartAt I∂ p).symm z)) =
            extChartAt Jm (F p) (F p) := by
          simpa [hgz, b] using hg
        have hpoint := (extChartAt Jm (F p)).injOn hFsrc hcSrc hchart
        exact hpoint.trans hFp
      · intro hFeq
        have hpoint : F ((extChartAt I∂ p).symm z) = F p := hFeq.trans hFp.symm
        calc
          g z = extChartAt Jm (F p) (F ((extChartAt I∂ p).symm z)) := hgz
          _ = extChartAt Jm (F p) (F p) := congrArg (extChartAt Jm (F p)) hpoint
          _ = b := rfl
    have hqiff : qfun (d (z - a)) = 0 ↔ g z = b := by
      have haff : affine (d (z - a)) = z := haffine_d z
      have hqeq : qfun (d (z - a)) = (cLin (g z - b)).1 := by
        change (cLin (g (affine (d (z - a))) - b)).1 = _
        rw [haff]
      have hZ : ∀ t : EuclideanSpace ℝ (Fin (m - m)), t = 0 := by
        intro t
        ext i
        have hi : i.val < 0 := by simpa [Nat.sub_self] using i.isLt
        omega
      rw [hqeq]
      constructor
      · intro hq0
        have hc0 : cLin (g z - b) = 0 := by
          apply Prod.ext
          · exact hq0
          · simp [hZ]
        exact sub_eq_zero.mp ((cLin.map_eq_zero_iff).mp hc0)
      · intro hg
        simp [hg]
    constructor
    · intro hzero
      exact hinj.1 (hqiff.mp (by simpa [hcomp, hq] using hzero))
    · intro hFeq
      simpa [hcomp, hq] using hqiff.mpr (hinj.2 hFeq)
  -- Restrict so that both original and new normal coordinates stay positive.
  let Ψ0 : OpenPartialHomeomorph Eₙ Eₙ := ΨP.toOpenPartialHomeomorph
  have hcontΨ0 : ContinuousOn Ψ0 Ψ0.source := Ψ0.continuousOn
  have hopen_pos : IsOpen {z : Eₙ | 0 < z 0} := isOpen_openHalfSpace
  have hΨa : Ψ0 a = e1 := by
    have happly := hΨP_apply a haΨP
    have hG0 : ΨG (d (a - a)) = 0 := by
      simpa using hΨGzero
    change ΨP a = e1
    rw [happly, hG0]
    simp [e1]
  have he1pos : 0 < e1 0 := by
    change 0 < standardConcatEquiv n m hmn (unitFree, 0) 0
    rw [standardConcatEquiv_unit_zero (n := n) (m := m) hmn]
    norm_num
  have ha_pos_new : a ∈ Ψ0 ⁻¹' {z : Eₙ | 0 < z 0} := by
    change 0 < Ψ0 a 0
    simpa [hΨa] using he1pos
  have hSopen : IsOpen
      (Ψ0.source ∩ {z : Eₙ | 0 < z 0} ∩ Ψ0 ⁻¹' {z : Eₙ | 0 < z 0}) := by
    have h1 := Ψ0.open_source.inter hopen_pos
    have h2 := hcontΨ0.isOpen_inter_preimage Ψ0.open_source hopen_pos
    convert h1.inter h2 using 1
    ext z
    constructor
    · rintro ⟨⟨hz, hzpos⟩, hznew⟩
      exact ⟨⟨hz, hzpos⟩, ⟨hz, hznew⟩⟩
    · rintro ⟨⟨hz, hzpos⟩, ⟨_, hznew⟩⟩
      exact ⟨⟨hz, hzpos⟩, hznew⟩
  let S : Set Eₙ := Ψ0.source ∩ {z : Eₙ | 0 < z 0} ∩ Ψ0 ⁻¹' {z : Eₙ | 0 < z 0}
  have haS : a ∈ S := by
    refine ⟨⟨haΨP, ?_⟩, ha_pos_new⟩
    exact interiorChartTarget_subset_openHalfSpace (n := n) p hpInterior
      (mem_interiorChartTarget (n := n) p hpInterior)
  let Ψ : OpenPartialHomeomorph Eₙ Eₙ := Ψ0.restrOpen S hSopen
  have hΨsource : Ψ.source = S := by
    simp [Ψ, OpenPartialHomeomorph.restrOpen_source, S, Set.inter_assoc]
  refine ⟨{
    Ψ := Ψ
    mem_source := by
      change a ∈ Ψ.source
      simpa [hΨsource] using haS
    source_subset_openHalf := by
      intro z hz
      have : z ∈ S := by simpa [hΨsource] using hz
      exact this.1.2
    target_subset_openHalf := by
      intro w hw
      have hw' : w ∈ Ψ0.target ∧ Ψ0.symm w ∈ S := by
        simpa [Ψ, OpenPartialHomeomorph.restrOpen, hSopen.interior_eq] using hw
      have : Ψ0.symm w ∈ Ψ0 ⁻¹' {z : Eₙ | 0 < z 0} := hw'.2.2
      have hw0 : Ψ0 (Ψ0.symm w) = w := Ψ0.right_inv hw'.1
      have : 0 < Ψ0 (Ψ0.symm w) 0 := this
      simpa [hw0] using this
    source_subset_interiorChart := by
      intro z hz
      have hzS : z ∈ S := by simpa [hΨsource] using hz
      have hzΨP : z ∈ ΨP.source := hzS.1.1
      have hzΩ : d (z - a) ∈ Ω := by
        have hz' := hzΨP
        simp [ΨP] at hz'
        exact hΨGΩ hz'.1.1.1.2
      have hzΩ0 : z ∈ Ω0 := by
        change affine (d (z - a)) ∈ Ω0 at hzΩ
        rw [haffine_d z] at hzΩ
        exact hzΩ
      exact hzΩ0.1
    source_subset_codomain := by
      intro z hz
      have hzS : z ∈ S := by simpa [hΨsource] using hz
      have hzΨP : z ∈ ΨP.source := hzS.1.1
      have hzΩ : d (z - a) ∈ Ω := by
        have hz' := hzΨP
        simp [ΨP] at hz'
        exact hΨGΩ hz'.1.1.1.2
      have hzΩ0 : z ∈ Ω0 := by
        change affine (d (z - a)) ∈ Ω0 at hzΩ
        rw [haffine_d z] at hzΩ
        exact hzΩ
      exact hzΩ0.2
    contDiffOn_toFun := by
      have hΨP : ContDiffOn ℝ ∞ Ψ0 Ψ0.source :=
        (contMDiffOn_iff_contDiffOn (E := Eₙ) (E' := Eₙ) (n := ∞)).mp
          ΨP.contMDiffOn_toFun
      refine hΨP.mono ?_
      intro z hz
      have : z ∈ S := by simpa [hΨsource] using hz
      exact this.1.1
    contDiffOn_invFun := by
      have hΨP : ContDiffOn ℝ ∞ Ψ0.symm Ψ0.target :=
        (contMDiffOn_iff_contDiffOn (E := Eₙ) (E' := Eₙ) (n := ∞)).mp
          ΨP.contMDiffOn_invFun
      intro w hw
      have hw' : w ∈ Ψ0.target ∧ Ψ0.symm w ∈ S := by
        simpa [Ψ, OpenPartialHomeomorph.restrOpen, hSopen.interior_eq] using hw
      exact (hΨP w hw'.1).mono (by
        intro y hy
        have hy' : y ∈ Ψ0.target ∧ Ψ0.symm y ∈ S := by
          simpa [Ψ, OpenPartialHomeomorph.restrOpen] using hy
        exact hy'.1)
    fiber_iff := by
      intro z hz
      have hzS : z ∈ S := by simpa [hΨsource] using hz
      have hzΨP : z ∈ ΨP.source := hzS.1.1
      have : Ψ z = ΨP z := by
        change Ψ0 z = ΨP z
        rfl
      simpa [this] using hfiber_unrestricted z hzΨP
  }⟩

/-
/-! ### Half-space restriction and preferred-chart transcription -/

variable {F : M → N} {c : N}

/-- Restrict the Euclidean straightening to the closed half-space.  Both domains already lie
in the open half-space, so the restriction is a half-space local homeomorphism with no
Seeley extension. -/
def interiorHalfSpaceDiffeo
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    OpenPartialHomeomorph (EuclideanHalfSpace (n + 1)) (EuclideanHalfSpace (n + 1)) :=
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  let hpres :=
    halfSpace_preserved_of_subset_interior (k := n + 1) D.Ψ
      D.source_subset_openHalf D.target_subset_openHalf
  restrictToHalfSpace D.Ψ hpres.1 hpres.2

theorem interiorHalfSpaceDiffeo_source
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    (interiorHalfSpaceDiffeo hmn hF hpInterior hFp hpSurj).source =
      {z : EuclideanHalfSpace (n + 1) | z.1 ∈
        (Classical.choice
          (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)).Ψ.source} :=
  rfl

/-- Preferred-chart transcription of the Euclidean interior straightening. -/
def interiorAmbientChart
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
  (chartAt (EuclideanHalfSpace (n + 1)) p).trans
    (interiorHalfSpaceDiffeo hmn hF hpInterior hFp hpSurj)

theorem mem_interiorAmbientChart_source
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    p ∈ (interiorAmbientChart hmn hF hpInterior hFp hpSurj).source := by
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  rw [interiorAmbientChart, OpenPartialHomeomorph.trans_source]
  refine ⟨mem_chart_source (EuclideanHalfSpace (n + 1)) p, ?_⟩
  change (chartAt (EuclideanHalfSpace (n + 1)) p p).1 ∈ D.Ψ.source
  have : (chartAt (EuclideanHalfSpace (n + 1)) p).extend I∂ p = extChartAt I∂ p p := rfl
  simpa [OpenPartialHomeomorph.extend_coe, ModelWithCorners.coe] using D.mem_source

theorem extChartAt_halfSpace_coe
    (y z : EuclideanHalfSpace (n + 1)) :
    extChartAt I∂ y z = z.1 := by
  rw [extChartAt_coe, chartAt_self_eq, OpenPartialHomeomorph.refl_apply]
  rfl

theorem interiorAmbientChart_apply
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p))
    {x : M}
    (hx : x ∈ (interiorAmbientChart hmn hF hpInterior hFp hpSurj).source) :
    ((interiorAmbientChart hmn hF hpInterior hFp hpSurj) x).1 =
      (Classical.choice
        (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)).Ψ
        (extChartAt I∂ p x) := by
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  let hpres :=
    halfSpace_preserved_of_subset_interior (k := n + 1) D.Ψ
      D.source_subset_openHalf D.target_subset_openHalf
  have hx' :
      x ∈ (chartAt (EuclideanHalfSpace (n + 1)) p).source ∧
        (chartAt (EuclideanHalfSpace (n + 1)) p x).1 ∈ D.Ψ.source := by
    simpa [interiorAmbientChart, interiorHalfSpaceDiffeo, OpenPartialHomeomorph.trans_source]
      using hx
  have happly :=
    restrictToHalfSpace_apply (k := n + 1) D.Ψ hpres.1 hpres.2 hx'.2
  have htrans :
      interiorAmbientChart hmn hF hpInterior hFp hpSurj x =
        restrictToHalfSpace D.Ψ hpres.1 hpres.2
          (chartAt (EuclideanHalfSpace (n + 1)) p x) := by
    rw [interiorAmbientChart, OpenPartialHomeomorph.trans_apply]
    · rfl
    · simpa [interiorHalfSpaceDiffeo] using hx
  rw [htrans, happly]
  simp [extChartAt, OpenPartialHomeomorph.extend_coe]

theorem interiorAmbientChart_symm_extend
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p))
    {z : EuclideanHalfSpace (n + 1)}
    (hz : z ∈ (interiorAmbientChart hmn hF hpInterior hFp hpSurj).target) :
    extChartAt I∂ p
        ((interiorAmbientChart hmn hF hpInterior hFp hpSurj).symm z) =
      (Classical.choice
        (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)).Ψ.symm z.1 := by
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  let hpres :=
    halfSpace_preserved_of_subset_interior (k := n + 1) D.Ψ
      D.source_subset_openHalf D.target_subset_openHalf
  let e := chartAt (EuclideanHalfSpace (n + 1)) p
  let ΨH := restrictToHalfSpace D.Ψ hpres.1 hpres.2
  have hz' : z ∈ (e.trans ΨH).target := by
    simpa [interiorAmbientChart, interiorHalfSpaceDiffeo] using hz
  rw [OpenPartialHomeomorph.trans_target] at hz'
  have hΨH : ΨH.symm z ∈ e.target := hz'.2
  have hzΨ : z.1 ∈ D.Ψ.target := by
    simpa [ΨH] using hz'.1
  have hΨHapply : (ΨH.symm z).1 = D.Ψ.symm z.1 := by
    have := restrictToHalfSpace_apply (k := n + 1)
      (Ψ := D.Ψ.symm) ?_ ?_ hzΨ
    · -- `restrictToHalfSpace` of `Ψ.symm` is `ΨH.symm` on the target.
      change (restrictToHalfSpace D.Ψ hpres.1 hpres.2).symm z = _
      simp [restrictToHalfSpace, hzΨ]
      rfl
    · intro w hw hw0
      exact (hpres.2 w hw hw0)
    · intro w hw hw0
      exact (hpres.1 w hw hw0)
  -- Use the identity `extChartAt p (e.symm w) = w.1` on `e.target`.
  have hcoe :
      extChartAt I∂ p (e.symm (ΨH.symm z)) = (ΨH.symm z).1 := by
    have : e.symm (ΨH.symm z) ∈ e.source := e.map_target hΨH
    rw [extChartAt, OpenPartialHomeomorph.extend_coe]
    change (e (e.symm (ΨH.symm z))).1 = (ΨH.symm z).1
    rw [e.right_inv hΨH]
  have hsymm :
      (interiorAmbientChart hmn hF hpInterior hFp hpSurj).symm z =
        e.symm (ΨH.symm z) := by
    rw [interiorAmbientChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    rw [OpenPartialHomeomorph.trans_apply]
    · rfl
    · simpa [interiorHalfSpaceDiffeo] using hz
  rw [hsymm, hcoe, hΨHapply]

theorem interiorAmbientChart_contMDiffOn
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    ContMDiffOn I∂ I∂ ∞
      (interiorAmbientChart hmn hF hpInterior hFp hpSurj)
      (interiorAmbientChart hmn hF hpInterior hFp hpSurj).source := by
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  let Φ := interiorAmbientChart hmn hF hpInterior hFp hpSurj
  have hs : Φ.source ⊆ (extChartAt I∂ p).source := by
    intro x hx
    simpa [Φ, interiorAmbientChart, OpenPartialHomeomorph.trans_source, extChartAt_source]
      using hx.1
  have hmaps : MapsTo Φ Φ.source (extChartAt I∂ (Φ p)).source := by
    intro x hx
    simp [extChartAt, chartAt_self_eq]
  rw [contMDiffOn_iff_of_subset_source' (I := I∂) (I' := I∂) (x := p) (y := Φ p) hs hmaps]
  have hcomp :
      EqOn (extChartAt I∂ (Φ p) ∘ Φ ∘ (extChartAt I∂ p).symm) D.Ψ
        (extChartAt I∂ p '' Φ.source) := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hxSrc : x ∈ (extChartAt I∂ p).source := hs hx
    have hleft : (extChartAt I∂ p).symm (extChartAt I∂ p x) = x :=
      (extChartAt I∂ p).left_inv hxSrc
    simp only [Function.comp_apply, hleft, extChartAt_halfSpace_coe]
    exact interiorAmbientChart_apply hmn hF hpInterior hFp hpSurj hx
  refine (D.contDiffOn_toFun.mono ?_).congr hcomp
  intro z hz
  rcases hz with ⟨x, hx, rfl⟩
  have hx' :
      x ∈ (chartAt (EuclideanHalfSpace (n + 1)) p).source ∧
        (chartAt (EuclideanHalfSpace (n + 1)) p x).1 ∈ D.Ψ.source := by
    simpa [Φ, interiorAmbientChart, interiorHalfSpaceDiffeo,
      OpenPartialHomeomorph.trans_source] using hx
  simpa [extChartAt, OpenPartialHomeomorph.extend_coe] using hx'.2

theorem interiorAmbientChart_symm_contMDiffOn
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    ContMDiffOn I∂ I∂ ∞
      (interiorAmbientChart hmn hF hpInterior hFp hpSurj).symm
      (interiorAmbientChart hmn hF hpInterior hFp hpSurj).target := by
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  let Φ := interiorAmbientChart hmn hF hpInterior hFp hpSurj
  have hs : Φ.target ⊆ (extChartAt I∂ (Φ p)).source := by
    intro z hz
    simp [extChartAt, chartAt_self_eq]
  have hmaps : MapsTo Φ.symm Φ.target (extChartAt I∂ p).source := by
    intro z hz
    have hzSrc : Φ.symm z ∈ Φ.source := Φ.symm.map_source hz
    simpa [Φ, interiorAmbientChart, OpenPartialHomeomorph.trans_source, extChartAt_source]
      using hzSrc.1
  rw [contMDiffOn_iff_of_subset_source' (I := I∂) (I' := I∂) (x := Φ p) (y := p) hs hmaps]
  have hcomp :
      EqOn (extChartAt I∂ p ∘ Φ.symm ∘ (extChartAt I∂ (Φ p)).symm) D.Ψ.symm
        (extChartAt I∂ (Φ p) '' Φ.target) := by
    intro w hw
    rcases hw with ⟨z, hz, rfl⟩
    have : (extChartAt I∂ (Φ p)).symm (extChartAt I∂ (Φ p) z) = z := by
      have : z ∈ (extChartAt I∂ (Φ p)).source := by simp [extChartAt, chartAt_self_eq]
      exact (extChartAt I∂ (Φ p)).left_inv this
    simp only [Function.comp_apply, this, extChartAt_halfSpace_coe]
    exact interiorAmbientChart_symm_extend hmn hF hpInterior hFp hpSurj hz
  refine (D.contDiffOn_invFun.mono ?_).congr hcomp
  intro w hw
  rcases hw with ⟨z, hz, rfl⟩
  simpa [extChartAt_halfSpace_coe] using
    (by
      have hz' : z ∈
          ((chartAt (EuclideanHalfSpace (n + 1)) p).trans
            (interiorHalfSpaceDiffeo hmn hF hpInterior hFp hpSurj)).target := by
        simpa [Φ, interiorAmbientChart] using hz
      rw [OpenPartialHomeomorph.trans_target] at hz'
      simpa [interiorHalfSpaceDiffeo] using hz'.1)

theorem interiorAmbientChart_mem_maximalAtlas
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    interiorAmbientChart hmn hF hpInterior hFp hpSurj ∈
      IsManifold.maximalAtlas I∂ ∞ M :=
  (interiorAmbientChart hmn hF hpInterior hFp hpSurj).mem_maximalAtlas_of_contMDiffOn
    (interiorAmbientChart_contMDiffOn hmn hF hpInterior hFp hpSurj)
    (interiorAmbientChart_symm_contMDiffOn hmn hF hpInterior hFp hpSurj)

theorem interiorAmbientChart_image_eq
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    let Φ := interiorAmbientChart hmn hF hpInterior hFp hpSurj
    Φ '' ((F ⁻¹' {c}) ∩ Φ.source) =
      neatHalfSpaceSlice Φ.target (standardConcatEquiv n m hmn) := by
  intro Φ
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  ext z
  constructor
  · rintro ⟨x, ⟨hxS, hxSrc⟩, rfl⟩
    refine ⟨Φ.map_source hxSrc, ?_⟩
    change ((standardConcatEquiv n m hmn).symm (Φ x).1).2 = 0
    have hxExt : x ∈ (extChartAt I∂ p).source := by
      simpa [Φ, interiorAmbientChart, OpenPartialHomeomorph.trans_source, extChartAt_source]
        using hxSrc.1
    have hΨ : extChartAt I∂ p x ∈ D.Ψ.source := by
      have hx' :
          x ∈ (chartAt (EuclideanHalfSpace (n + 1)) p).source ∧
            (chartAt (EuclideanHalfSpace (n + 1)) p x).1 ∈ D.Ψ.source := by
        simpa [Φ, interiorAmbientChart, interiorHalfSpaceDiffeo,
          OpenPartialHomeomorph.trans_source] using hxSrc
      simpa [extChartAt, OpenPartialHomeomorph.extend_coe] using hx'.2
    have happly := interiorAmbientChart_apply hmn hF hpInterior hFp hpSurj hxSrc
    have hiff := D.fiber_iff (extChartAt I∂ p x) hΨ
    have hleft : (extChartAt I∂ p).symm (extChartAt I∂ p x) = x :=
      (extChartAt I∂ p).left_inv hxExt
    have : ((standardConcatEquiv n m hmn).symm (D.Ψ (extChartAt I∂ p x))).2 = 0 :=
      hiff.mpr (by simpa [hleft] using hxS)
    simpa [happly] using this
  · intro hz
    have hzT : z ∈ Φ.target := hz.1
    have hcomp : ((standardConcatEquiv n m hmn).symm z.1).2 = 0 := hz.2
    let x := Φ.symm z
    have hxSrc : x ∈ Φ.source := Φ.symm.map_source hzT
    refine ⟨x, ⟨?_, hxSrc⟩, Φ.right_inv hzT⟩
    have hΨ : D.Ψ.symm z.1 ∈ D.Ψ.source := by
      have hz' : z ∈
          ((chartAt (EuclideanHalfSpace (n + 1)) p).trans
            (interiorHalfSpaceDiffeo hmn hF hpInterior hFp hpSurj)).target := by
        simpa [Φ, interiorAmbientChart] using hzT
      rw [OpenPartialHomeomorph.trans_target] at hz'
      have : z.1 ∈ D.Ψ.target := by simpa [interiorHalfSpaceDiffeo] using hz'.1
      exact D.Ψ.map_target this
    have hΨz : D.Ψ (D.Ψ.symm z.1) = z.1 := by
      have hz' : z ∈
          ((chartAt (EuclideanHalfSpace (n + 1)) p).trans
            (interiorHalfSpaceDiffeo hmn hF hpInterior hFp hpSurj)).target := by
        simpa [Φ, interiorAmbientChart] using hzT
      rw [OpenPartialHomeomorph.trans_target] at hz'
      exact D.Ψ.right_inv (by simpa [interiorHalfSpaceDiffeo] using hz'.1)
    have hiff := D.fiber_iff (D.Ψ.symm z.1) hΨ
    have hext := interiorAmbientChart_symm_extend hmn hF hpInterior hFp hpSurj hzT
    have : ((standardConcatEquiv n m hmn).symm (D.Ψ (D.Ψ.symm z.1))).2 = 0 := by
      simpa [hΨz] using hcomp
    have hFeq : F ((extChartAt I∂ p).symm (D.Ψ.symm z.1)) = c :=
      hiff.mp this
    have : (extChartAt I∂ p).symm (extChartAt I∂ p x) = x := by
      have hxExt : x ∈ (extChartAt I∂ p).source := by
        simpa [Φ, interiorAmbientChart, OpenPartialHomeomorph.trans_source, extChartAt_source]
          using hxSrc.1
      exact (extChartAt I∂ p).left_inv hxExt
    simpa [x, hext, this] using hFeq

end InteriorRegularPreimageChart

open InteriorRegularPreimageChart

/-- Interior pointwise neat-slice chart.  All source/point hypotheses are included, so a later
assembly step can simply select this chart at each interior fibre point.  The only derivative
hypothesis is actual surjectivity at `p`; the global boundary-regularity predicate is not used. -/
def interiorRegularPreimageChart
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff (𝓡∂ (n + 1)) (𝓡 m) ∞ F)
    {p : M} (hpInterior : (𝓡∂ (n + 1)).IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv (𝓡∂ (n + 1)) (𝓡 m) F p)) :
    CInfinityNeatSliceChart (d := n) (k := n - m) (q := m) (F ⁻¹' {c}) where
  ambientChart :=
    interiorAmbientChart hmn hF hpInterior hFp hpSurj
  ambient_mem_maximalAtlas :=
    interiorAmbientChart_mem_maximalAtlas hmn hF hpInterior hFp hpSurj
  equiv := standardConcatEquiv n m hmn
  normal_eq := fun u v ↦ standardConcatEquiv_apply_zero n m hmn u v
  image_eq := interiorAmbientChart_image_eq hmn hF hpInterior hFp hpSurj

theorem interiorRegularPreimageChart_mem_source
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff (𝓡∂ (n + 1)) (𝓡 m) ∞ F)
    {p : M} (hpInterior : (𝓡∂ (n + 1)).IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv (𝓡∂ (n + 1)) (𝓡 m) F p)) :
    p ∈ (interiorRegularPreimageChart hmn hF hpInterior hFp hpSurj).ambientChart.source :=
  mem_interiorAmbientChart_source hmn hF hpInterior hFp hpSurj

/-- Fibre-point spelling used by later assembly: the ambient source membership is packaged
with the chart. -/
def interiorRegularPreimageChart_of_mem_fiber
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff (𝓡∂ (n + 1)) (𝓡 m) ∞ F)
    (p : F ⁻¹' {c}) (hpInterior : (𝓡∂ (n + 1)).IsInteriorPoint p.1)
    (hpSurj : Function.Surjective (mfderiv (𝓡∂ (n + 1)) (𝓡 m) F p.1)) :
    CInfinityNeatSliceChart (d := n) (k := n - m) (q := m) (F ⁻¹' {c}) :=
  interiorRegularPreimageChart hmn hF hpInterior p.2 hpSurj

theorem interiorRegularPreimageChart_of_mem_fiber_mem_source
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff (𝓡∂ (n + 1)) (𝓡 m) ∞ F)
    (p : F ⁻¹' {c}) (hpInterior : (𝓡∂ (n + 1)).IsInteriorPoint p.1)
    (hpSurj : Function.Surjective (mfderiv (𝓡∂ (n + 1)) (𝓡 m) F p.1)) :
    p.1 ∈ (interiorRegularPreimageChart_of_mem_fiber hmn hF p hpInterior hpSurj).ambientChart.source :=
  interiorRegularPreimageChart_mem_source hmn hF hpInterior p.2 hpSurj

-/

open BoundaryPreimageCharts

variable {F : M → N} {c : N}

theorem extChartAt_eq_chartAt_coe (p x : M) :
    extChartAt I∂ p x = (chartAt (EuclideanHalfSpace (n + 1)) p x).1 := by
  rw [extChartAt_coe]
  rfl

def interiorHalfSpaceDiffeo
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    OpenPartialHomeomorph (EuclideanHalfSpace (n + 1)) (EuclideanHalfSpace (n + 1)) :=
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  let hpres := halfSpace_preserved_of_subset_interior (k := n + 1) D.Ψ
    D.source_subset_openHalf D.target_subset_openHalf
  restrictToHalfSpace D.Ψ hpres.1 hpres.2

def interiorAmbientChart
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    OpenPartialHomeomorph M (EuclideanHalfSpace (n + 1)) :=
  (chartAt (EuclideanHalfSpace (n + 1)) p).trans
    (interiorHalfSpaceDiffeo hmn hF hpInterior hFp hpSurj)

theorem mem_interiorAmbientChart_source
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    p ∈ (interiorAmbientChart hmn hF hpInterior hFp hpSurj).source := by
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  rw [interiorAmbientChart, OpenPartialHomeomorph.trans_source]
  refine ⟨mem_chart_source (EuclideanHalfSpace (n + 1)) p, ?_⟩
  change (chartAt (EuclideanHalfSpace (n + 1)) p p).1 ∈ D.Ψ.source
  rw [← extChartAt_eq_chartAt_coe p p]
  exact D.mem_source

theorem interiorAmbientChart_apply
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p))
    {x : M}
    (hx : x ∈ (interiorAmbientChart hmn hF hpInterior hFp hpSurj).source) :
    ((interiorAmbientChart hmn hF hpInterior hFp hpSurj) x).1 =
      (Classical.choice
        (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)).Ψ
        (extChartAt I∂ p x) := by
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  let hpres := halfSpace_preserved_of_subset_interior (k := n + 1) D.Ψ
    D.source_subset_openHalf D.target_subset_openHalf
  have hx' :
      x ∈ (chartAt (EuclideanHalfSpace (n + 1)) p).source ∧
        (chartAt (EuclideanHalfSpace (n + 1)) p x).1 ∈ D.Ψ.source := by
    rw [interiorAmbientChart, OpenPartialHomeomorph.trans_source] at hx
    refine ⟨hx.1, ?_⟩
    simpa [interiorHalfSpaceDiffeo, BoundaryPreimageCharts.restrictToHalfSpace_source]
      using hx.2
  have happly := restrictToHalfSpace_apply (k := n + 1) D.Ψ hpres.1 hpres.2 hx'.2
  change ((interiorHalfSpaceDiffeo hmn hF hpInterior hFp hpSurj)
      ((chartAt (EuclideanHalfSpace (n + 1)) p) x)).1 = _
  change (restrictToHalfSpace D.Ψ hpres.1 hpres.2
      ((chartAt (EuclideanHalfSpace (n + 1)) p) x)).1 = _
  rw [happly]
  congr 1

theorem interiorAmbientChart_symm_extend
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p))
    {z : EuclideanHalfSpace (n + 1)}
    (hz : z ∈ (interiorAmbientChart hmn hF hpInterior hFp hpSurj).target) :
    extChartAt I∂ p
        ((interiorAmbientChart hmn hF hpInterior hFp hpSurj).symm z) =
      (Classical.choice
        (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)).Ψ.symm z.1 := by
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  let hpres := halfSpace_preserved_of_subset_interior (k := n + 1) D.Ψ
    D.source_subset_openHalf D.target_subset_openHalf
  let e := chartAt (EuclideanHalfSpace (n + 1)) p
  let ΨH := restrictToHalfSpace D.Ψ hpres.1 hpres.2
  have hz' : z ∈ (e.trans ΨH).target := by
    simpa [interiorAmbientChart, interiorHalfSpaceDiffeo] using hz
  rw [OpenPartialHomeomorph.trans_target] at hz'
  have hzD : z.1 ∈ D.Ψ.target := by
    simpa [ΨH, BoundaryPreimageCharts.restrictToHalfSpace] using hz'.1
  have hsymm :
      (interiorAmbientChart hmn hF hpInterior hFp hpSurj).symm z =
        e.symm (ΨH.symm z) := by
    rw [interiorAmbientChart, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    rw [OpenPartialHomeomorph.trans_apply]
    rfl
  have hext : extChartAt I∂ p (e.symm (ΨH.symm z)) = (ΨH.symm z).1 := by
    rw [extChartAt_coe]
    change (e (e.symm (ΨH.symm z))).1 = (ΨH.symm z).1
    exact congrArg Subtype.val (e.right_inv hz'.2)
  have hhalf : (ΨH.symm z).1 = D.Ψ.symm z.1 := by
    simp [ΨH, BoundaryPreimageCharts.restrictToHalfSpace, hzD]
  rw [hsymm, hext, hhalf]

theorem interiorAmbientChart_mem_maximalAtlas
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    interiorAmbientChart hmn hF hpInterior hFp hpSurj ∈
      IsManifold.maximalAtlas I∂ ∞ M := by
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  let hpres := halfSpace_preserved_of_subset_interior (k := n + 1) D.Ψ
    D.source_subset_openHalf D.target_subset_openHalf
  let Φ := restrictToHalfSpace D.Ψ hpres.1 hpres.2
  have hΦgroup : Φ ∈ contDiffGroupoid ∞ I∂ := by
    exact BoundaryRegularPreimageChart.restrictToHalfSpace_mem_contDiffGroupoid
      hpres.1 hpres.2 D.contDiffOn_toFun D.contDiffOn_invFun
  have hΦ : ContMDiffOn I∂ I∂ ∞ Φ Φ.source :=
    contMDiffOn_of_mem_contDiffGroupoid hΦgroup
  have hΦsymm : ContMDiffOn I∂ I∂ ∞ Φ.symm Φ.target :=
    contMDiffOn_of_mem_contDiffGroupoid ((contDiffGroupoid ∞ I∂).symm hΦgroup)
  have heMax : (chartAt (EuclideanHalfSpace (n + 1)) p) ∈
      IsManifold.maximalAtlas I∂ ∞ M := IsManifold.chart_mem_maximalAtlas (I := I∂) p
  have he : ContMDiffOn I∂ I∂ ∞
      (chartAt (EuclideanHalfSpace (n + 1)) p)
      (chartAt (EuclideanHalfSpace (n + 1)) p).source :=
    contMDiffOn_of_mem_maximalAtlas heMax
  have heSymm : ContMDiffOn I∂ I∂ ∞
      (chartAt (EuclideanHalfSpace (n + 1)) p).symm
      (chartAt (EuclideanHalfSpace (n + 1)) p).target :=
    contMDiffOn_symm_of_mem_maximalAtlas heMax
  apply (interiorAmbientChart hmn hF hpInterior hFp hpSurj).mem_maximalAtlas_of_contMDiffOn
  · change ContMDiffOn I∂ I∂ ∞ (Φ ∘ chartAt (EuclideanHalfSpace (n + 1)) p)
      ((chartAt (EuclideanHalfSpace (n + 1)) p).source ∩
        (chartAt (EuclideanHalfSpace (n + 1)) p) ⁻¹' Φ.source)
    exact hΦ.comp (he.mono inter_subset_left) (fun _ hx ↦ hx.2)
  · change ContMDiffOn I∂ I∂ ∞
      ((chartAt (EuclideanHalfSpace (n + 1)) p).symm ∘ Φ.symm)
      (Φ.target ∩ Φ.symm ⁻¹' (chartAt (EuclideanHalfSpace (n + 1)) p).target)
    exact heSymm.comp (hΦsymm.mono inter_subset_left) (fun _ hx ↦ hx.2)

theorem interiorAmbientChart_image_eq
    (hmn : m ≤ n) (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    let Φ := interiorAmbientChart hmn hF hpInterior hFp hpSurj
    Φ '' ((F ⁻¹' {c}) ∩ Φ.source) =
      neatHalfSpaceSlice Φ.target (standardConcatEquiv n m hmn) := by
  intro Φ
  let D := Classical.choice
    (exists_interiorEuclideanStraightening hmn hF hpInterior hFp hpSurj)
  ext z
  constructor
  · rintro ⟨x, ⟨hxF, hxΦ⟩, rfl⟩
    refine ⟨Φ.map_source hxΦ, ?_⟩
    have hxD : extChartAt I∂ p x ∈ D.Ψ.source := by
      have hx' := hxΦ
      rw [extChartAt_eq_chartAt_coe p x]
      simpa [Φ, interiorAmbientChart, OpenPartialHomeomorph.trans_source,
        interiorHalfSpaceDiffeo,
        BoundaryPreimageCharts.restrictToHalfSpace_source,
        D] using hx'.2
    have hiff := D.fiber_iff (extChartAt I∂ p x) hxD
    have hxExt : (extChartAt I∂ p).symm (extChartAt I∂ p x) = x := by
      apply (extChartAt I∂ p).left_inv
      simpa [Φ, interiorAmbientChart, OpenPartialHomeomorph.trans_source,
        extChartAt_source] using hxΦ.1
    have hfiber : F ((extChartAt I∂ p).symm (extChartAt I∂ p x)) = c := by
      rw [hxExt]
      exact hxF
    have hzero := hiff.mpr hfiber
    have happly := interiorAmbientChart_apply hmn hF hpInterior hFp hpSurj hxΦ
    change ((standardConcatEquiv n m hmn).symm (Φ x).1).2 = 0
    rw [happly]
    simpa using hzero
  · intro hz
    let x := Φ.symm z
    have hxΦ : x ∈ Φ.source := Φ.symm.map_source hz.1
    refine ⟨x, ⟨?_, hxΦ⟩, Φ.right_inv hz.1⟩
    have hxD : extChartAt I∂ p x ∈ D.Ψ.source := by
      have hx' := hxΦ
      rw [extChartAt_eq_chartAt_coe p x]
      simpa [Φ, interiorAmbientChart, OpenPartialHomeomorph.trans_source,
        interiorHalfSpaceDiffeo,
        BoundaryPreimageCharts.restrictToHalfSpace_source,
        D] using hx'.2
    have hzD : z.1 ∈ D.Ψ.target := by
      have hz' := hz.1
      simpa [Φ, interiorAmbientChart, OpenPartialHomeomorph.trans_target,
        interiorHalfSpaceDiffeo,
        BoundaryPreimageCharts.restrictToHalfSpace] using hz'.1
    have hDsrc : D.Ψ.symm z.1 ∈ D.Ψ.source := D.Ψ.map_target hzD
    have hzero : ((standardConcatEquiv n m hmn).symm (D.Ψ (D.Ψ.symm z.1))).2 = 0 := by
      simpa [D.Ψ.right_inv hzD] using hz.2
    have hFeq := (D.fiber_iff (D.Ψ.symm z.1) hDsrc).mp hzero
    have hExt := interiorAmbientChart_symm_extend hmn hF hpInterior hFp hpSurj hz.1
    have hxExt : (extChartAt I∂ p).symm (extChartAt I∂ p x) = x := by
      apply (extChartAt I∂ p).left_inv
      simpa [Φ, interiorAmbientChart, OpenPartialHomeomorph.trans_source,
        extChartAt_source] using hxΦ.1
    have hExt' : extChartAt I∂ p x = D.Ψ.symm z.1 := by
      simpa [x, hExt]
    rw [← hExt'] at hFeq
    rw [hxExt] at hFeq
    exact hFeq

def interiorRegularPreimageChart
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    CInfinityNeatSliceChart (d := n) (k := n - m) (q := m) (F ⁻¹' {c}) where
  ambientChart := interiorAmbientChart hmn hF hpInterior hFp hpSurj
  ambient_mem_maximalAtlas := interiorAmbientChart_mem_maximalAtlas hmn hF hpInterior hFp hpSurj
  equiv := standardConcatEquiv n m hmn
  normal_eq := fun u v ↦ standardConcatEquiv_apply_zero n m hmn u v
  image_eq := interiorAmbientChart_image_eq hmn hF hpInterior hFp hpSurj

theorem interiorRegularPreimageChart_mem_source
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff I∂ Jm ∞ F)
    {p : M} (hpInterior : I∂.IsInteriorPoint p) (hFp : F p = c)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p)) :
    p ∈ (interiorRegularPreimageChart hmn hF hpInterior hFp hpSurj).ambientChart.source :=
  mem_interiorAmbientChart_source hmn hF hpInterior hFp hpSurj

def interiorRegularPreimageChart_of_mem_fiber
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff I∂ Jm ∞ F)
    (p : F ⁻¹' {c}) (hpInterior : I∂.IsInteriorPoint p.1)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p.1)) :
    CInfinityNeatSliceChart (d := n) (k := n - m) (q := m) (F ⁻¹' {c}) :=
  interiorRegularPreimageChart hmn hF hpInterior p.2 hpSurj

theorem interiorRegularPreimageChart_of_mem_fiber_mem_source
    {F : M → N} {c : N} (hmn : m ≤ n)
    (hF : ContMDiff I∂ Jm ∞ F)
    (p : F ⁻¹' {c}) (hpInterior : I∂.IsInteriorPoint p.1)
    (hpSurj : Function.Surjective (mfderiv I∂ Jm F p.1)) :
    p.1 ∈ (interiorRegularPreimageChart_of_mem_fiber hmn hF p hpInterior hpSurj).ambientChart.source :=
  interiorRegularPreimageChart_mem_source hmn hF hpInterior p.2 hpSurj

end InteriorRegularPreimageChart

end Manifold
