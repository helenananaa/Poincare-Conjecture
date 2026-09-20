import LeeSmoothLib.Ch01.Sec01_06.WithinTaylorSums
import LeeSmoothLib.Ch01.Sec01_06.SeeleyCutoffJets
import LeeSmoothLib.Ch01.Sec01_06.SeeleyMoments
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
Series of cutoff-weighted Seeley jets on a closed lower half-ball.

The uncut off-boundary formula that ignores cutoff derivatives is false (see
`SeeleyCutoffJets`). This file glues each Leibniz term field to zero off its
support, sums the jets under the proved weighted summability, differentiates
the sum within the closed half-ball, and matches the original field on the
flat boundary by the infinite moment identities.
-/

noncomputable section

open Set Filter Metric Function Finset
open scoped Topology ContDiff InnerProductSpace

namespace LeeSmooth.SeeleyExtension

universe u v
variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

private lemma nat_le_infty (m : ℕ) : (m : ℕ∞ω) ≤ ∞ := by
  exact WithTop.coe_le_coe.2 (le_top : (m : ℕ∞) ≤ ⊤)

private lemma nat_lt_infty (m : ℕ) : (m : ℕ∞ω) < ∞ :=
  lt_of_le_of_ne (nat_le_infty m) (by simp)

/-- Uniformly majorized Taylor fields on a closed convex set with nonempty interior
may be summed, and the sum remains a Taylor field. Differentiation of the jet
series is taken within the set via the interior (where ambient derivatives exist)
and `hasFDerivWithinAt_closure_of_tendsto_fderiv` at the boundary. -/
private lemma hasFTaylorSeriesUpToOn_tsum
    {s : Set E} (hs_closed : IsClosed s) (hs_conv : Convex ℝ s)
    (hs_int : (interior s).Nonempty)
    {f : ℕ → E → F}
    {p : ℕ → E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ i, HasFTaylorSeriesUpToOn ∞ (f i) (p i) s)
    (hbound : ∀ m : ℕ, ∃ u : ℕ → ℝ, Summable u ∧ ∀ i x, x ∈ s → ‖p i x m‖ ≤ u i) :
    HasFTaylorSeriesUpToOn ∞ (fun x => ∑' i, f i x)
      (fun x m => ∑' i, p i x m) s := by
  classical
  choose u hu hb using hbound
  exact LeeSmooth.WithinTaylorSums.hasFTaylorSeriesUpToOn_tsum hs_conv hp hu hb

variable {n : ℕ} [NeZero n]

private lemma uniqueDiffOn_seeleyLowerHalfBall
    {x : EuclideanSpace ℝ (Fin n)} {d : ℝ} (hd : 0 < d) (hx0 : x 0 = 0) :
    UniqueDiffOn ℝ (seeleyLowerHalfBall (n := n) x d) :=
  uniqueDiffOn_closedBall_inter_closedLowerHalfSpace (by linarith : 0 < d / 4) hx0

private lemma interior_seeleyLowerHalfBall_nonempty
    {x : EuclideanSpace ℝ (Fin n)} {d : ℝ} (hd : 0 < d) (hx0 : x 0 = 0) :
    (interior (seeleyLowerHalfBall (n := n) x d)).Nonempty := by
  let y : EuclideanSpace ℝ (Fin n) := x - (d / 8) • EuclideanSpace.single 0 (1 : ℝ)
  refine ⟨y, ?_⟩
  rw [seeleyLowerHalfBall, interior_inter, interior_closedBall x (by linarith : d / 4 ≠ 0)]
  constructor
  · have hsub : y - x = -((d / 8) • EuclideanSpace.single 0 (1 : ℝ)) := by
      simp [y]
    rw [mem_ball, dist_eq_norm, hsub, norm_neg, norm_smul, PiLp.norm_single]
    simp [Real.norm_eq_abs, abs_of_pos hd]
    linarith
  · rw [mem_interior]
    refine ⟨{z : EuclideanSpace ℝ (Fin n) | z 0 < 0}, ?_, ?_, ?_⟩
    · intro z hz
      change z 0 ≤ 0
      exact le_of_lt hz
    · exact isOpen_Iio.preimage (EuclideanSpace.proj (0 : Fin n)).continuous
    · change y 0 < 0
      simp [y, hx0]
      linarith

private lemma isCompact_upperSlice
    (x : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    IsCompact (closedBall x d ∩ closedUpperHalfSpace (n := n)) :=
  (isCompact_closedBall x d).inter_right isClosed_closedUpperHalfSpace

/-- Ambient iterated derivatives of the spatial cutoff vanish wherever the cutoff
argument is at least `2`. -/
private lemma seeleyCutoffOnSpace_iteratedFDeriv_eq_zero
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) (m : ℕ) {z : EuclideanSpace ℝ (Fin n)}
    (hz : 2 ≤ seeleyCutoffCLM (n := n) j ε z) :
    iteratedFDeriv ℝ m (seeleyCutoffOnSpace (n := n) j ε) z = 0 := by
  have hcomp :
      iteratedFDeriv ℝ m (seeleyCutoffOnSpace (n := n) j ε) z =
        (iteratedFDeriv ℝ m seeleyCutoff
          (seeleyCutoffCLM (n := n) j ε z)).compContinuousLinearMap
          fun _ => seeleyCutoffCLM (n := n) j ε := by
    convert
      (seeleyCutoffCLM (n := n) j ε).iteratedFDeriv_comp_right
        seeleyCutoff_contDiff_infty z (nat_le_infty m) using 1 <;> rfl
  rw [hcomp]
  have hder : iteratedDeriv m seeleyCutoff (seeleyCutoffCLM (n := n) j ε z) = 0 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simpa [iteratedDeriv_zero] using seeleyCutoff_eq_zero hz
    · exact seeleyCutoff_iteratedDeriv_eq_zero_of_ge_two hm hz
  have hF : iteratedFDeriv ℝ m seeleyCutoff (seeleyCutoffCLM (n := n) j ε z) = 0 := by
    rw [iteratedFDeriv_eq_equiv_comp, Function.comp_apply, hder, map_zero]
  rw [hF]
  ext
  simp

private lemma seeleyCutoffOnSpace_iteratedFDerivWithin_eq_zero
    {x : EuclideanSpace ℝ (Fin n)} {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) (hx0 : x 0 = 0)
    (j m : ℕ) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε)
    (hL : 2 ≤ seeleyCutoffCLM (n := n) j ε z) :
    iteratedFDerivWithin ℝ m (seeleyCutoffOnSpace (n := n) j ε)
      (seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε) z = 0 := by
  have hχ : ContDiff ℝ ∞ (seeleyCutoffOnSpace (n := n) j ε) :=
    seeleyCutoff_contDiff_infty.comp (seeleyCutoffCLM (n := n) j ε).contDiff
  have hχm : ContDiffAt ℝ m (seeleyCutoffOnSpace (n := n) j ε) z :=
    (hχ.of_le (nat_le_infty m)).contDiffAt
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    (uniqueDiffOn_lower_inter_support hd hε hx0 j) hχm hz]
  exact seeleyCutoffOnSpace_iteratedFDeriv_eq_zero j hε m hL

/-- The unweighted Leibniz field of one cutoff-weighted reflected term. -/
private def seeleyUnweightedLeibnizTaylor (j : ℕ) (ε : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → F)
    (p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F)
    (z : EuclideanSpace ℝ (Fin n)) :
    FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F :=
  (ftaylorSeries ℝ (fun q : ℝ × F => q.1 • q.2)
    (seeleyCutoffOnSpace (n := n) j ε z,
      f (seeleyReflectionMap j z))).taylorComp
    (fun k =>
      ((ftaylorSeries ℝ seeleyCutoff
          (seeleyCutoffCLM (n := n) j ε z) k).compContinuousLinearMap
          fun _ => seeleyCutoffCLM (n := n) j ε).prod
        ((p (seeleyReflectionMap j z) k).compContinuousLinearMap
          fun _ => seeleyReflectionMap (n := n) j))

private lemma seeleyUnweightedLeibnizTaylor_hasFTaylorSeriesUpToOn_support
    (a : ℕ → ℝ) (j : ℕ) {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin n)} (hx0 : x 0 = 0)
    (hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p
      (closedBall x d ∩ closedUpperHalfSpace (n := n))) :
    HasFTaylorSeriesUpToOn ∞
      (fun z => seeleyCutoffOnSpace (n := n) j ε z • f (seeleyReflectionMap j z))
      (seeleyUnweightedLeibnizTaylor (n := n) j ε f p)
      (seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε) :=
  seeleyTermWith_hasFTaylorSeriesUpToOn_support a j hd hε hx0 hεd hp

/-- At the cutoff seam the Leibniz field vanishes: every cutoff derivative is zero. -/
private lemma seeleyUnweightedLeibnizTaylor_eq_zero_at_seam
    (j : ℕ) {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin n)} (hx0 : x 0 = 0)
    (hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p
      (closedBall x d ∩ closedUpperHalfSpace (n := n)))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε)
    (hL : 2 ≤ seeleyCutoffCLM (n := n) j ε z) (m : ℕ) :
    seeleyUnweightedLeibnizTaylor (n := n) j ε f p z m = 0 := by
  let S := seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε
  have hunique : UniqueDiffOn ℝ S := uniqueDiffOn_lower_inter_support hd hε hx0 j
  have hT : HasFTaylorSeriesUpToOn ∞
      (fun w => seeleyCutoffOnSpace (n := n) j ε w • f (seeleyReflectionMap j w))
      (seeleyUnweightedLeibnizTaylor (n := n) j ε f p) S :=
    seeleyUnweightedLeibnizTaylor_hasFTaylorSeriesUpToOn_support
      (fun _ => (1 : ℝ)) j hd hε hx0 hεd hp
  have heq :=
    hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (nat_le_infty m) hunique hz
  rw [heq]
  have hχ : ContDiffOn ℝ ∞ (seeleyCutoffOnSpace (n := n) j ε) S :=
    (seeleyCutoff_contDiff_infty.comp (seeleyCutoffCLM (n := n) j ε).contDiff).contDiffOn
  have hsupp :
      S ⊆ seeleyReflectionMap j ⁻¹'
        (closedBall x d ∩ closedUpperHalfSpace (n := n)) := by
    intro w hw
    exact seeleyReflectionMap_mem_closedBall hd hε hx0 hεd hw.1 hw.2
  have hfR : ContDiffOn ℝ ∞ (fun w => f (seeleyReflectionMap j w)) S :=
    ((hp.compContinuousLinearMap (seeleyReflectionMap (n := n) j)).mono hsupp).contDiffOn
  have hle :=
    norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (𝕜' := ℝ) (F := F)
      hχ hfR hunique hz (n := m) (nat_le_infty m)
  have hsum0 :
      (∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i (seeleyCutoffOnSpace (n := n) j ε) S z‖ *
          ‖iteratedFDerivWithin ℝ (m - i) (fun w => f (seeleyReflectionMap j w)) S z‖) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hχi :
        iteratedFDerivWithin ℝ i (seeleyCutoffOnSpace (n := n) j ε) S z = 0 :=
      seeleyCutoffOnSpace_iteratedFDerivWithin_eq_zero hd hε hx0 j i hz hL
    simp [hχi]
  exact norm_le_zero_iff.mp (hle.trans (le_of_eq hsum0))

/-- Glued Taylor field of one cutoff-weighted term on the whole lower half-ball. -/
private def seeleyTermTaylor (a : ℕ → ℝ) (j : ℕ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (d : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → F)
    (p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F) :
    EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F :=
  fun z m =>
    closedPiecewise
      (seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε)
      (fun w => a j • seeleyUnweightedLeibnizTaylor (n := n) j ε f p w m)
      (fun _ => 0) z

private lemma seeleyTermTaylor_hasFTaylorSeriesUpToOn
    (a : ℕ → ℝ) (j : ℕ) {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin n)} (hx0 : x 0 = 0)
    (hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p
      (closedBall x d ∩ closedUpperHalfSpace (n := n))) :
    HasFTaylorSeriesUpToOn ∞ (seeleyTermWith a j ε f)
      (seeleyTermTaylor (n := n) a j ε x d f p)
      (seeleyLowerHalfBall (n := n) x d) := by
  let T := seeleyLowerHalfBall (n := n) x d
  let Supp := T ∩ seeleyTermSupport (n := n) j ε
  let Zero := T ∩ seeleyTermZero (n := n) j ε
  have hTeq : T = Supp ∪ Zero :=
    seeleyLowerHalfBall_eq_support_union_zero x d j ε
  have hSuppC : IsClosed Supp :=
    (isClosed_seeleyLowerHalfBall x d).inter (isClosed_seeleyTermSupport j ε)
  have hZeroC : IsClosed Zero :=
    (isClosed_seeleyLowerHalfBall x d).inter (isClosed_seeleyTermZero j ε)
  have hprod :
      HasFTaylorSeriesUpToOn ∞
        (fun z => seeleyCutoffOnSpace (n := n) j ε z • f (seeleyReflectionMap j z))
        (seeleyUnweightedLeibnizTaylor (n := n) j ε f p) Supp :=
    seeleyUnweightedLeibnizTaylor_hasFTaylorSeriesUpToOn_support a j hd hε hx0 hεd hp
  have hsmul :
      HasFTaylorSeriesUpToOn ∞
        (fun z => a j • seeleyCutoffOnSpace (n := n) j ε z • f (seeleyReflectionMap j z))
        (fun z m => a j • seeleyUnweightedLeibnizTaylor (n := n) j ε f p z m) Supp :=
    HasFTaylorSeriesUpToOn.const_smul_real hprod (a j)
  have hzero : HasFTaylorSeriesUpToOn ∞ (fun _ => (0 : F))
      (fun _ (_ : ℕ) =>
        (0 : ContinuousMultilinearMap ℝ
          (fun _ : Fin _ => EuclideanSpace ℝ (Fin n)) F)) Zero :=
    hasFTaylorSeriesUpToOn_zero Zero
  have hfun :
      EqOn (seeleyTermWith a j ε f)
        (closedPiecewise Supp
          (fun z => a j • seeleyCutoffOnSpace (n := n) j ε z • f (seeleyReflectionMap j z))
          (fun _ => 0)) T := by
    intro z hz
    by_cases hzs : z ∈ Supp
    · simp [closedPiecewise_of_mem hzs, seeleyTermWith]
    · have hzZ : z ∈ Zero := by
        have : z ∈ Supp ∪ Zero := by
          rw [← hTeq]
          exact hz
        exact this.resolve_left hzs
      simp [closedPiecewise_of_notMem hzs, seeleyTermWith_eq_zero_of_mem_zero a f hzZ.2]
  have hpiece :
      HasFTaylorSeriesUpToOn ∞
        (closedPiecewise Supp
          (fun z => a j • seeleyCutoffOnSpace (n := n) j ε z • f (seeleyReflectionMap j z))
          (fun _ => 0))
        (fun z m => closedPiecewise Supp
          (fun w => a j • seeleyUnweightedLeibnizTaylor (n := n) j ε f p w m)
          (fun _ => 0) z)
        (Supp ∪ Zero) := by
    apply HasFTaylorSeriesUpToOn.piecewise_of_isClosed hSuppC hZeroC hsmul hzero
    intro m hm z hz
    have hL : 2 ≤ seeleyCutoffCLM (n := n) j ε z := hz.2.2
    have hjet :=
      seeleyUnweightedLeibnizTaylor_eq_zero_at_seam j hd hε hx0 hεd hp hz.1 hL m
    simp [hjet]
  rw [seeleyLowerHalfBall_eq_support_union_zero x d j ε]
  exact hpiece.congr fun z hz => hfun (hTeq ▸ hz)

/-! ## Uniform jet bounds on the compact lower half-ball -/

private lemma exists_bound_taylor
    {d : ℝ} {x : EuclideanSpace ℝ (Fin n)}
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p
      (closedBall x d ∩ closedUpperHalfSpace (n := n))) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ w ∈ closedBall x d ∩ closedUpperHalfSpace (n := n), ‖p w k‖ ≤ M := by
  have hK := isCompact_upperSlice x d
  have hc : ContinuousOn (fun w => p w k) (closedBall x d ∩ closedUpperHalfSpace (n := n)) :=
    hp.cont k (nat_le_infty k)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨max M 0, le_max_right _ _, fun w hw => (hM w hw).trans (le_max_left _ _)⟩

private lemma seeleyCutoffOnSpace_iteratedFDeriv_norm_le
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) (i : ℕ) (z : EuclideanSpace ℝ (Fin n)) {C : ℝ}
    (hC : ∀ t : ℝ, |iteratedDeriv i seeleyCutoff t| ≤ C) :
    ‖iteratedFDeriv ℝ i (seeleyCutoffOnSpace (n := n) j ε) z‖ ≤
      C * ((2 : ℝ) ^ j / ε) ^ i := by
  have hcomp :
      iteratedFDeriv ℝ i (seeleyCutoffOnSpace (n := n) j ε) z =
        (iteratedFDeriv ℝ i seeleyCutoff
          (seeleyCutoffCLM (n := n) j ε z)).compContinuousLinearMap
          fun _ => seeleyCutoffCLM (n := n) j ε := by
    convert
      (seeleyCutoffCLM (n := n) j ε).iteratedFDeriv_comp_right
        seeleyCutoff_contDiff_infty z (nat_le_infty i) using 1 <;> rfl
  rw [hcomp]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hχ :
      ‖iteratedFDeriv ℝ i seeleyCutoff (seeleyCutoffCLM (n := n) j ε z)‖ ≤ C := by
    simpa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] using
      hC (seeleyCutoffCLM (n := n) j ε z)
  have hL : ‖seeleyCutoffCLM (n := n) j ε‖ ≤ (2 : ℝ) ^ j / ε :=
    opNorm_seeleyCutoffCLM_le (n := n) j hε
  have hprod :
      (∏ _k : Fin i, ‖seeleyCutoffCLM (n := n) j ε‖) ≤ ((2 : ℝ) ^ j / ε) ^ i := by
    simpa [prod_const, Fintype.card_fin] using
      pow_le_pow_left₀ (norm_nonneg _) hL i
  calc
    ‖(iteratedFDeriv ℝ i seeleyCutoff (seeleyCutoffCLM (n := n) j ε z)).compContinuousLinearMap
        fun _ => seeleyCutoffCLM (n := n) j ε‖
        ≤ ‖iteratedFDeriv ℝ i seeleyCutoff (seeleyCutoffCLM (n := n) j ε z)‖ *
            ∏ _k : Fin i, ‖seeleyCutoffCLM (n := n) j ε‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ C * ((2 : ℝ) ^ j / ε) ^ i := by
          gcongr

private lemma seeley_pow_factor (j m i : ℕ) {ε : ℝ} (hε : 0 < ε) (hi : i ≤ m) :
    ((2 : ℝ) ^ j / ε) ^ i * ((2 : ℝ) ^ (j + 2)) ^ (m - i) =
      ε⁻¹ ^ i * (4 : ℝ) ^ (m - i) * (2 : ℝ) ^ (j * m) := by
  have hiε : ((2 : ℝ) ^ j / ε) ^ i = (2 : ℝ) ^ (j * i) * ε⁻¹ ^ i := by
    simp only [div_eq_mul_inv, mul_pow, pow_mul, inv_pow]
  have hR : ((2 : ℝ) ^ (j + 2)) ^ (m - i) = (2 : ℝ) ^ ((j + 2) * (m - i)) := by
    rw [← pow_mul]
  have hsplit : (j + 2) * (m - i) = j * (m - i) + 2 * (m - i) := by ring
  have hjm : j * i + j * (m - i) = j * m := by
    rw [← mul_add, Nat.add_sub_of_le hi]
  calc
    ((2 : ℝ) ^ j / ε) ^ i * ((2 : ℝ) ^ (j + 2)) ^ (m - i)
        = (2 : ℝ) ^ (j * i) * ε⁻¹ ^ i * (2 : ℝ) ^ ((j + 2) * (m - i)) := by
          rw [hiε, hR]
    _ = (2 : ℝ) ^ (j * i) * ε⁻¹ ^ i * (2 : ℝ) ^ (j * (m - i) + 2 * (m - i)) := by
          rw [hsplit]
    _ = (2 : ℝ) ^ (j * i + j * (m - i)) * ε⁻¹ ^ i * (2 : ℝ) ^ (2 * (m - i)) := by
          rw [pow_add]; ring
    _ = (2 : ℝ) ^ (j * m) * ε⁻¹ ^ i * (4 : ℝ) ^ (m - i) := by
          rw [hjm, pow_mul (2 : ℝ) 2 (m - i)]
          norm_num
    _ = ε⁻¹ ^ i * (4 : ℝ) ^ (m - i) * (2 : ℝ) ^ (j * m) := by ring

private lemma seeleyTermTaylor_norm_le
    (a : ℕ → ℝ) (j : ℕ) {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin n)} (hx0 : x 0 = 0)
    (hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p
      (closedBall x d ∩ closedUpperHalfSpace (n := n)))
    (m : ℕ) {C : ℕ → ℝ} (hC : ∀ i t, |iteratedDeriv i seeleyCutoff t| ≤ C i)
    (hC0 : ∀ i, 0 ≤ C i)
    {M : ℕ → ℝ}
    (hM : ∀ k, 0 ≤ M k ∧
      ∀ w ∈ closedBall x d ∩ closedUpperHalfSpace (n := n), ‖p w k‖ ≤ M k)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ seeleyLowerHalfBall (n := n) x d) :
    ‖seeleyTermTaylor (n := n) a j ε x d f p z m‖ ≤
      |a j| * (∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * C i * M (m - i) * ε⁻¹ ^ i * (4 : ℝ) ^ (m - i)) *
        (2 : ℝ) ^ (j * m) := by
  let T := seeleyLowerHalfBall (n := n) x d
  let Supp := T ∩ seeleyTermSupport (n := n) j ε
  by_cases hzs : z ∈ Supp
  · have hmem : z ∈ Supp := hzs
    have hunique : UniqueDiffOn ℝ Supp := uniqueDiffOn_lower_inter_support hd hε hx0 j
    have hprod :
        HasFTaylorSeriesUpToOn ∞
          (fun w => seeleyCutoffOnSpace (n := n) j ε w • f (seeleyReflectionMap j w))
          (seeleyUnweightedLeibnizTaylor (n := n) j ε f p) Supp :=
      seeleyUnweightedLeibnizTaylor_hasFTaylorSeriesUpToOn_support a j hd hε hx0 hεd hp
    have hjet :
        seeleyUnweightedLeibnizTaylor (n := n) j ε f p z m =
          iteratedFDerivWithin ℝ m
            (fun w => seeleyCutoffOnSpace (n := n) j ε w • f (seeleyReflectionMap j w))
            Supp z :=
      hprod.eq_iteratedFDerivWithin_of_uniqueDiffOn (nat_le_infty m) hunique hmem
    have hχ : ContDiffOn ℝ ∞ (seeleyCutoffOnSpace (n := n) j ε) Supp :=
      (seeleyCutoff_contDiff_infty.comp (seeleyCutoffCLM (n := n) j ε).contDiff).contDiffOn
    have hsuppMap :
        Supp ⊆ seeleyReflectionMap j ⁻¹'
          (closedBall x d ∩ closedUpperHalfSpace (n := n)) := by
      intro w hw
      exact seeleyReflectionMap_mem_closedBall hd hε hx0 hεd hw.1 hw.2
    have hfR : ContDiffOn ℝ ∞ (fun w => f (seeleyReflectionMap j w)) Supp :=
      ((hp.compContinuousLinearMap (seeleyReflectionMap (n := n) j)).mono hsuppMap).contDiffOn
    have hle :=
      norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (𝕜' := ℝ) (F := F)
        hχ hfR hunique hmem (n := m) (nat_le_infty m)
    have hχF : ContDiff ℝ ∞ (seeleyCutoffOnSpace (n := n) j ε) :=
      seeleyCutoff_contDiff_infty.comp (seeleyCutoffCLM (n := n) j ε).contDiff
    have hterm :
        seeleyTermTaylor (n := n) a j ε x d f p z m =
          a j • seeleyUnweightedLeibnizTaylor (n := n) j ε f p z m :=
      closedPiecewise_of_mem hmem
    rw [hterm, hjet, norm_smul, Real.norm_eq_abs]
    have hsumle :
        (∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i (seeleyCutoffOnSpace (n := n) j ε) Supp z‖ *
            ‖iteratedFDerivWithin ℝ (m - i) (fun w => f (seeleyReflectionMap j w)) Supp z‖) ≤
          (∑ i ∈ Finset.range (m + 1),
              (m.choose i : ℝ) * C i * M (m - i) * ε⁻¹ ^ i * (4 : ℝ) ^ (m - i)) *
            (2 : ℝ) ^ (j * m) := by
      refine (Finset.sum_le_sum ?_).trans_eq (Finset.sum_mul _ _ _).symm
      intro i hi
      have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hχb :
          ‖iteratedFDerivWithin ℝ i (seeleyCutoffOnSpace (n := n) j ε) Supp z‖ ≤
            C i * ((2 : ℝ) ^ j / ε) ^ i := by
        rw [iteratedFDerivWithin_eq_iteratedFDeriv hunique
          ((hχF.of_le (nat_le_infty i)).contDiffAt) hmem]
        exact seeleyCutoffOnSpace_iteratedFDeriv_norm_le j hε i z (hC i)
      have hfRjet :
          iteratedFDerivWithin ℝ (m - i) (fun w => f (seeleyReflectionMap j w)) Supp z =
            (p (seeleyReflectionMap j z) (m - i)).compContinuousLinearMap
              fun _ => seeleyReflectionMap (n := n) j := by
        have hT :=
          (hp.compContinuousLinearMap (seeleyReflectionMap (n := n) j)).mono hsuppMap
        exact (hT.eq_iteratedFDerivWithin_of_uniqueDiffOn (nat_le_infty (m - i)) hunique hmem).symm
      have hRb : ‖seeleyReflectionMap (n := n) j‖ ≤ (2 : ℝ) ^ (j + 2) :=
        opNorm_seeleyReflectionMap_le_two_pow_succ (n := n) j
      have hzR :
          seeleyReflectionMap j z ∈ closedBall x d ∩ closedUpperHalfSpace (n := n) :=
        seeleyReflectionMap_mem_closedBall hd hε hx0 hεd hmem.1 hmem.2
      have hgbound :
          ‖iteratedFDerivWithin ℝ (m - i) (fun w => f (seeleyReflectionMap j w)) Supp z‖ ≤
            M (m - i) * ((2 : ℝ) ^ (j + 2)) ^ (m - i) := by
        rw [hfRjet]
        have hprod :
            (∏ _k : Fin (m - i), ‖seeleyReflectionMap (n := n) j‖) ≤
              ((2 : ℝ) ^ (j + 2)) ^ (m - i) := by
          simpa [prod_const, Fintype.card_fin] using
            pow_le_pow_left₀ (norm_nonneg _) hRb (m - i)
        calc
          ‖(p (seeleyReflectionMap j z) (m - i)).compContinuousLinearMap
              fun _ => seeleyReflectionMap (n := n) j‖
              ≤ ‖p (seeleyReflectionMap j z) (m - i)‖ *
                  ∏ _k : Fin (m - i), ‖seeleyReflectionMap (n := n) j‖ :=
                ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
          _ ≤ M (m - i) * ((2 : ℝ) ^ (j + 2)) ^ (m - i) := by
                gcongr
                · exact (hM (m - i)).1
                · exact (hM (m - i)).2 _ hzR
      have hpow := seeley_pow_factor j m i hε hi'
      calc
        (m.choose i : ℝ) *
            ‖iteratedFDerivWithin ℝ i (seeleyCutoffOnSpace (n := n) j ε) Supp z‖ *
            ‖iteratedFDerivWithin ℝ (m - i) (fun w => f (seeleyReflectionMap j w)) Supp z‖
            ≤ (m.choose i : ℝ) * (C i * ((2 : ℝ) ^ j / ε) ^ i) *
                (M (m - i) * ((2 : ℝ) ^ (j + 2)) ^ (m - i)) := by
              have hCi := hC0 i
              have hMi := (hM (m - i)).1
              have hco : 0 ≤ (m.choose i : ℝ) * (C i * ((2 : ℝ) ^ j / ε) ^ i) := by
                positivity
              exact mul_le_mul (mul_le_mul_of_nonneg_left hχb (by positivity))
                hgbound (norm_nonneg _) hco
        _ = (m.choose i : ℝ) * C i * M (m - i) *
              (((2 : ℝ) ^ j / ε) ^ i * ((2 : ℝ) ^ (j + 2)) ^ (m - i)) := by ring
        _ = ((m.choose i : ℝ) * C i * M (m - i) * ε⁻¹ ^ i * (4 : ℝ) ^ (m - i)) *
              (2 : ℝ) ^ (j * m) := by
              rw [hpow]; ring
    have hprodle := hle.trans hsumle
    have hmul := mul_le_mul_of_nonneg_left hprodle (abs_nonneg (a j))
    simpa [mul_assoc] using hmul
  · have : seeleyTermTaylor (n := n) a j ε x d f p z m = 0 :=
      closedPiecewise_of_notMem hzs
    rw [this, norm_zero]
    refine mul_nonneg (mul_nonneg (abs_nonneg _) ?_) (pow_nonneg (by norm_num) _)
    refine Finset.sum_nonneg fun i _ => ?_
    have hεi : 0 ≤ ε⁻¹ ^ i := pow_nonneg (inv_nonneg.2 hε.le) _
    have h4 : 0 ≤ (4 : ℝ) ^ (m - i) := pow_nonneg (by norm_num) _
    have hch : 0 ≤ (m.choose i : ℝ) := Nat.cast_nonneg _
    have hCi := hC0 i
    have hMi := (hM (m - i)).1
    positivity

private lemma seeleyTermTaylor_summable_bound
    (a : ℕ → ℝ) {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin n)} (hx0 : x 0 = 0)
    (hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p
      (closedBall x d ∩ closedUpperHalfSpace (n := n)))
    (ha : SeeleyCoeffSummable a) (m : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧
      ∀ j z, z ∈ seeleyLowerHalfBall (n := n) x d →
        ‖seeleyTermTaylor (n := n) a j ε x d f p z m‖ ≤ u j := by
  let C : ℕ → ℝ := fun i => Classical.choose (seeleyCutoff_iteratedDeriv_bounded i)
  have hC : ∀ i, 0 ≤ C i ∧ ∀ t, |iteratedDeriv i seeleyCutoff t| ≤ C i :=
    fun i => Classical.choose_spec (seeleyCutoff_iteratedDeriv_bounded i)
  let M : ℕ → ℝ := fun k => Classical.choose (exists_bound_taylor hp k)
  have hM : ∀ k, 0 ≤ M k ∧
      ∀ w ∈ closedBall x d ∩ closedUpperHalfSpace (n := n), ‖p w k‖ ≤ M k :=
    fun k => Classical.choose_spec (exists_bound_taylor hp k)
  let K : ℝ := ∑ i ∈ Finset.range (m + 1),
    (m.choose i : ℝ) * C i * M (m - i) * ε⁻¹ ^ i * (4 : ℝ) ^ (m - i)
  have hK : 0 ≤ K := by
    refine Finset.sum_nonneg fun i _ => ?_
    have : 0 ≤ ε⁻¹ ^ i := pow_nonneg (inv_nonneg.2 hε.le) _
    positivity [(hC i).1, (hM (m - i)).1]
  refine ⟨fun j => |a j| * K * (2 : ℝ) ^ (j * m), ?_, ?_⟩
  · have hsum : Summable fun j : ℕ => |a j| * (2 : ℝ) ^ (j * m) := ha m
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsum.mul_left K
  · intro j z hz
    have := seeleyTermTaylor_norm_le a j hd hε hx0 hεd hp m
      (fun i => (hC i).2) (fun i => (hC i).1) hM hz
    simpa [K] using this

/-! ## Boundary identification -/

private lemma seeleyCutoffOnSpace_eq_one_of_normal_eq_zero
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) {z : EuclideanSpace ℝ (Fin n)} (hz : z 0 = 0) :
    seeleyCutoffOnSpace (n := n) j ε z = 1 := by
  rw [seeleyCutoffOnSpace_eq, hz]
  simp [seeleyCutoff_eq_one]

private lemma eventually_seeleyCutoffOnSpace_eq_one
    (j : ℕ) {ε : ℝ} (hε : 0 < ε) {x : EuclideanSpace ℝ (Fin n)} {d : ℝ}
    {z : EuclideanSpace ℝ (Fin n)}
    (hzT : z ∈ seeleyLowerHalfBall (n := n) x d) (hz0 : z 0 = 0) :
    seeleyCutoffOnSpace (n := n) j ε =ᶠ[𝓝[seeleyLowerHalfBall (n := n) x d] z]
      fun _ => (1 : ℝ) := by
  let U : Set (EuclideanSpace ℝ (Fin n)) :=
    {w | seeleyCutoffCLM (n := n) j ε w < 1}
  have hUopen : IsOpen U :=
    isOpen_Iio.preimage (seeleyCutoffCLM (n := n) j ε).continuous
  have hzU : z ∈ U := by
    change seeleyCutoffCLM (n := n) j ε z < 1
    rw [seeleyCutoffCLM_apply, hz0]
    simp [hε]
  refine Filter.eventuallyEq_of_mem
    (inter_mem_nhdsWithin _ (hUopen.mem_nhds hzU)) ?_
  intro w hw
  exact seeleyCutoffOnSpace_eq_one_of_le (le_of_lt hw.2)

private lemma seeleyTermTaylor_boundary
    (a : ℕ → ℝ) (j : ℕ) {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin n)} (hx0 : x 0 = 0)
    (hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p
      (closedBall x d ∩ closedUpperHalfSpace (n := n)))
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ seeleyLowerHalfBall (n := n) x d) (hz0 : z 0 = 0) (m : ℕ) :
    seeleyTermTaylor (n := n) a j ε x d f p z m =
      a j • (p z m).compContinuousLinearMap fun _ => seeleyReflectionMap (n := n) j := by
  let T := seeleyLowerHalfBall (n := n) x d
  have huniqueT : UniqueDiffOn ℝ T := uniqueDiffOn_seeleyLowerHalfBall hd hx0
  have hTfield :=
    seeleyTermTaylor_hasFTaylorSeriesUpToOn a j hd hε hx0 hεd hp
  have hterm :
      seeleyTermTaylor (n := n) a j ε x d f p z m =
        iteratedFDerivWithin ℝ m (seeleyTermWith a j ε f) T z :=
    hTfield.eq_iteratedFDerivWithin_of_uniqueDiffOn (nat_le_infty m) huniqueT hz
  have hχ1 :
      seeleyCutoffOnSpace (n := n) j ε =ᶠ[𝓝[T] z] fun _ => (1 : ℝ) :=
    eventually_seeleyCutoffOnSpace_eq_one j hε hz hz0
  have hfun :
      seeleyTermWith a j ε f =ᶠ[𝓝[T] z]
        fun w => a j • f (seeleyReflectionMap j w) := by
    filter_upwards [hχ1] with w hw
    simp [seeleyTermWith, hw]
  have hfunz : seeleyTermWith a j ε f z = a j • f (seeleyReflectionMap j z) := by
    simp [seeleyTermWith, seeleyCutoffOnSpace_eq_one_of_normal_eq_zero j hε hz0]
  have hEQterm :
      iteratedFDerivWithin ℝ m (seeleyTermWith a j ε f) T z =
        iteratedFDerivWithin ℝ m (fun w => a j • f (seeleyReflectionMap j w)) T z :=
    hfun.iteratedFDerivWithin_eq hfunz m
  let U : Set (EuclideanSpace ℝ (Fin n)) :=
    {w | seeleyCutoffCLM (n := n) j ε w < 1}
  have hUopen : IsOpen U :=
    isOpen_Iio.preimage (seeleyCutoffCLM (n := n) j ε).continuous
  have hzU : z ∈ U := by
    change seeleyCutoffCLM (n := n) j ε z < 1
    rw [seeleyCutoffCLM_apply, hz0]
    simp [hε]
  have hUN : U ∈ 𝓝 z := hUopen.mem_nhds hzU
  have hinter :
      iteratedFDerivWithin ℝ m (fun w => a j • f (seeleyReflectionMap j w)) T z =
        iteratedFDerivWithin ℝ m (fun w => a j • f (seeleyReflectionMap j w)) (T ∩ U) z :=
    (iteratedFDerivWithin_inter (n := m)
      (f := fun w => a j • f (seeleyReflectionMap j w)) (s := T) hUN).symm
  have hmaps : T ∩ U ⊆
      seeleyReflectionMap j ⁻¹' (closedBall x d ∩ closedUpperHalfSpace (n := n)) := by
    intro w hw
    have hwsupp : w ∈ seeleyTermSupport (n := n) j ε :=
      (le_of_lt hw.2).trans (by norm_num : (1 : ℝ) ≤ 2)
    exact seeleyReflectionMap_mem_closedBall hd hε hx0 hεd hw.1 hwsupp
  have hfR :
      HasFTaylorSeriesUpToOn ∞ (fun w => f (seeleyReflectionMap j w))
        (fun w k => (p (seeleyReflectionMap j w) k).compContinuousLinearMap
          fun _ => seeleyReflectionMap (n := n) j)
        (T ∩ U) :=
    (hp.compContinuousLinearMap (seeleyReflectionMap (n := n) j)).mono hmaps
  have hsmul :
      HasFTaylorSeriesUpToOn ∞ (fun w => a j • f (seeleyReflectionMap j w))
        (fun w k => a j • (p (seeleyReflectionMap j w) k).compContinuousLinearMap
          fun _ => seeleyReflectionMap (n := n) j)
        (T ∩ U) :=
    HasFTaylorSeriesUpToOn.const_smul_real hfR (a j)
  have huniqueU : UniqueDiffOn ℝ (T ∩ U) := huniqueT.inter hUopen
  have hzTU : z ∈ T ∩ U := ⟨hz, hzU⟩
  have hjetU :=
    hsmul.eq_iteratedFDerivWithin_of_uniqueDiffOn (nat_le_infty m) huniqueU hzTU
  have hRz : seeleyReflectionMap j z = z :=
    seeleyReflectionMap_of_normal_eq_zero j hz0
  rw [hterm, hEQterm, hinter, ← hjetU, hRz]

private lemma seeleyCoeff_summable : SeeleyCoeffSummable seeleyCoeff :=
  summable_abs_seeleyCoeff_mul_pow

private lemma seeley_boundary_jet_sum (m : ℕ)
    (M : EuclideanSpace ℝ (Fin n) [×m]→L[ℝ] F) :
    (∑' j : ℕ, seeleyCoeff j •
      (M.compContinuousLinearMap fun _ => seeleyReflectionMap (n := n) j)) = M := by
  refine ContinuousMultilinearMap.ext fun w => ?_
  have hsum : Summable fun j : ℕ =>
      seeleyCoeff j •
        (M.compContinuousLinearMap fun _ => seeleyReflectionMap (n := n) j) := by
    have hmaj : Summable fun j : ℕ => |seeleyCoeff j| * (2 : ℝ) ^ (j * m) :=
      summable_abs_seeleyCoeff_mul_pow m
    refine Summable.of_norm_bounded
      (hmaj.mul_left (‖M‖ * (4 : ℝ) ^ m)) fun j => ?_
    have hR : ‖seeleyReflectionMap (n := n) j‖ ≤ (2 : ℝ) ^ (j + 2) :=
      opNorm_seeleyReflectionMap_le_two_pow_succ (n := n) j
    have hprod :
        (∏ _k : Fin m, ‖seeleyReflectionMap (n := n) j‖) ≤ ((2 : ℝ) ^ (j + 2)) ^ m := by
      simpa [prod_const, Fintype.card_fin] using
        pow_le_pow_left₀ (norm_nonneg _) hR m
    have hmap :
        ‖M.compContinuousLinearMap fun _ => seeleyReflectionMap (n := n) j‖ ≤
          ‖M‖ * ((2 : ℝ) ^ (j + 2)) ^ m :=
      (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
        (by gcongr)
    have hpow : ((2 : ℝ) ^ (j + 2)) ^ m = (4 : ℝ) ^ m * (2 : ℝ) ^ (j * m) := by
      rw [← pow_mul, add_mul]
      rw [pow_add, pow_mul (2 : ℝ) 2 m]
      norm_num
      ring
    calc
      ‖seeleyCoeff j •
            (M.compContinuousLinearMap fun _ => seeleyReflectionMap (n := n) j)‖
          = |seeleyCoeff j| *
              ‖M.compContinuousLinearMap fun _ => seeleyReflectionMap (n := n) j‖ := by
            simp [norm_smul, Real.norm_eq_abs]
      _ ≤ |seeleyCoeff j| * (‖M‖ * ((2 : ℝ) ^ (j + 2)) ^ m) := by gcongr
      _ = ‖M‖ * (4 : ℝ) ^ m * (|seeleyCoeff j| * (2 : ℝ) ^ (j * m)) := by
            rw [hpow]
            ring
  let heval :=
    ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin m => EuclideanSpace ℝ (Fin n)) F w
  have happly :
      (∑' j, seeleyCoeff j •
          (M.compContinuousLinearMap fun _ => seeleyReflectionMap (n := n) j)) w =
        ∑' j, (seeleyCoeff j •
          (M.compContinuousLinearMap fun _ => seeleyReflectionMap (n := n) j)) w := by
    simpa only [heval, ContinuousMultilinearMap.apply_apply] using heval.map_tsum hsum
  rw [happly]
  simp only [ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have harg : ∀ j i,
      seeleyReflectionMap (n := n) j (w i) =
        seeleyNode j • normalProjection (w i) + tangentialProjection (w i) :=
    fun j i => seeleyReflectionMap_apply j (w i)
  simp_rw [harg]
  have htsum :=
    seeley_weighted_multilinear_tsum m M
      (fun i => normalProjection (w i)) (fun i => tangentialProjection (w i))
  convert htsum using 1
  refine congrArg M (funext fun i => (normal_add_tangential (w i)).symm)

/-- The Taylor field of `seeleyLower` is the series of Leibniz jets of the
cutoff-weighted reflected terms, not the uncut combination
`∑ a_j (p ∘ R_j) ∘ R_j`. That uncut formula is false already at order `0`:
with `f = 1`, `ε = d/8` and lower pole `y = x - (d/4) e₀`, every cutoff vanishes
so the series is `0`, while `∑ a_j = 1`. -/
lemma seeleyLower_hasFTaylorSeriesUpToOn
    {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin n)} (hx0 : x 0 = 0)
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2)
    (hp : HasFTaylorSeriesUpToOn ∞ f p
      (Metric.closedBall x d ∩ closedUpperHalfSpace (n := n))) :
    ∃ q : EuclideanSpace ℝ (Fin n) →
        FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F,
      HasFTaylorSeriesUpToOn ∞ (seeleyLower ε f) q
        (Metric.closedBall x (d / 4) ∩ closedLowerHalfSpace (n := n)) ∧
      ∀ z ∈ (Metric.closedBall x (d / 4) ∩ closedLowerHalfSpace (n := n)),
        z 0 = 0 → ∀ m, q z m = p z m := by
  let T : Set (EuclideanSpace ℝ (Fin n)) := seeleyLowerHalfBall (n := n) x d
  have hTeq : T = closedBall x (d / 4) ∩ closedLowerHalfSpace (n := n) := rfl
  let q : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F :=
    fun z m => ∑' j, seeleyTermTaylor (n := n) seeleyCoeff j ε x d f p z m
  have hpj : ∀ j, HasFTaylorSeriesUpToOn ∞ (seeleyTermWith seeleyCoeff j ε f)
      (seeleyTermTaylor (n := n) seeleyCoeff j ε x d f p) T :=
    fun j => seeleyTermTaylor_hasFTaylorSeriesUpToOn seeleyCoeff j hd hε hx0 hεd hp
  have hbound :
      ∀ m, ∃ u : ℕ → ℝ, Summable u ∧
        ∀ j z, z ∈ T → ‖seeleyTermTaylor (n := n) seeleyCoeff j ε x d f p z m‖ ≤ u j :=
    fun m => seeleyTermTaylor_summable_bound seeleyCoeff hd hε hx0 hεd hp
      seeleyCoeff_summable m
  have hsum :
      HasFTaylorSeriesUpToOn ∞
        (fun z => ∑' j, seeleyTermWith seeleyCoeff j ε f z) q T :=
    hasFTaylorSeriesUpToOn_tsum
      (isClosed_seeleyLowerHalfBall x d)
      (convex_seeleyLowerHalfBall x d)
      (interior_seeleyLowerHalfBall_nonempty hd hx0)
      hpj hbound
  have hfun : (fun z => ∑' j, seeleyTermWith seeleyCoeff j ε f z) = seeleyLower ε f := by
    funext z
    simp [seeleyLower, seeleyTermWith_eq_seeleyTerm]
  refine ⟨q, hsum.congr fun z _ => (congrFun hfun z).symm, ?_⟩
  intro z hz hz0 m
  have hzT : z ∈ T := hz
  have hterm : ∀ j,
      seeleyTermTaylor (n := n) seeleyCoeff j ε x d f p z m =
        seeleyCoeff j • (p z m).compContinuousLinearMap
          fun _ => seeleyReflectionMap (n := n) j :=
    fun j => seeleyTermTaylor_boundary seeleyCoeff j hd hε hx0 hεd hp hzT hz0 m
  calc
    q z m = ∑' j, seeleyTermTaylor (n := n) seeleyCoeff j ε x d f p z m := rfl
    _ = ∑' j, seeleyCoeff j •
          (p z m).compContinuousLinearMap fun _ => seeleyReflectionMap (n := n) j :=
        tsum_congr hterm
    _ = p z m := seeley_boundary_jet_sum m (p z m)

end LeeSmooth.SeeleyExtension
