import MorganTianLib.Ch01.BishopGromovManifold
import MorganTianLib.Ch01.BishopGromovManifoldProducers
import MorganTianLib.Ch01.ModelVolumeDensityPos

open MeasureTheory Measure Set Filter Metric Riemannian Module
open scoped ENNReal Topology ContDiff Manifold Bundle

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Math.** Volume half of `thm:local-volume-injectivity-radius-control`.
No injectivity radius, Klingenberg, or metric rescaling. -/
theorem riemannianMeasure_ball_ge_mul_pow_of_ricci
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [ConnectedSpace M]
    (p : M) {k r0 v0 : ℝ} (hk : 0 ≤ k) (hr0 : 0 < r0) (hv0 : 0 < v0)
    (hcompact : IsCompact (closure (Metric.ball p r0)))
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p r0, ∀ v : TangentSpace I x,
      -(((Module.finrank ℝ E : ℝ) - 1) * k) * g.metricInner x v v
        ≤ ricciAt g g.leviCivitaConnection hLC x v v)
    (hvol : ENNReal.ofReal v0 ≤
      riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r0)) :
    ∃ vstar : ℝ, 0 < vstar ∧
      ∀ s ∈ Ioc (0 : ℝ) r0,
        ENNReal.ofReal vstar * ENNReal.ofReal (s ^ Module.finrank ℝ E) ≤
          riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p s) :=
/- SWARM_PROOF_BEGIN -/
by
  set nDim := Module.finrank ℝ E
  set Y : ℝ → ℝ≥0∞ := fun r => modelBallVolume (volume : Measure 𝔼) k r
  set vol : ℝ → ℝ≥0∞ := fun r =>
    riemannianMeasure (I := I) g (gpHaar (I := I) g p) (Metric.ball p r)
  have hdiv_mul (a d b : ℝ≥0∞) : a / b * d = a * d / b := by
    rw [mul_comm, ← mul_div_assoc, mul_comm d]
  have hjac : Measurable (transportedJacobian (I := I) g hg p) :=
    (bishop_gromov_manifold_producers_of_available (I := I) g hg p r0).transportedJacobian_measurable
  have hBG :=
    bishop_gromov_manifold_ratio (I := I) g hg p hk hr0 hcompact hdim hLC hric hjac
  haveI : Nontrivial 𝔼 :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (by
        rw [finrank_coeffSpace (E := E)]
        exact Nat.pos_of_ne_zero (NeZero.ne _))
  obtain ⟨c, hcpos, hc⟩ :=
    modelBallVolume_lower_power (E := 𝔼) (μ := (volume : Measure 𝔼)) k hk
  have hYpos {r : ℝ} (hr : 0 < r) : 0 < Y r :=
    modelBallVolume_pos (volume : Measure 𝔼) hk hr
  have hY0 {r : ℝ} (hr : 0 < r) : Y r ≠ 0 := (hYpos hr).ne'
  have hYtop (r : ℝ) : Y r ≠ ⊤ := modelBallVolume_ne_top (volume : Measure 𝔼) hk r
  have hYmono : StrictMonoOn Y (Ioi (0 : ℝ)) :=
    modelBallVolume_strictMonoOn (volume : Measure 𝔼) hk
  have hratio_ge {r1 r2 : ℝ} (hr1 : r1 ∈ Ioo (0 : ℝ) r0) (hr2 : r2 ∈ Ioo (0 : ℝ) r0)
      (hle : r1 ≤ r2) : vol r2 * Y r1 / Y r2 ≤ vol r1 := by
    have hanti := hBG hr1 hr2 hle
    have hle' : vol r2 ≤ vol r1 / Y r1 * Y r2 :=
      (ENNReal.div_le_iff (hY0 hr2.1) (hYtop r2)).mp hanti
    have hle'' : vol r2 ≤ vol r1 * Y r2 / Y r1 := by
      convert hle' using 1
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
    have hmul : vol r2 * Y r1 ≤ vol r1 * Y r2 :=
      (ENNReal.le_div_iff_mul_le (Or.inl (hY0 hr1.1)) (Or.inl (hYtop r1))).mp hle''
    exact ENNReal.div_le_of_le_mul hmul
  set t0 : ℝ := min (1 : ℝ) (r0 / 2)
  have ht0pos : 0 < t0 := lt_min zero_lt_one (half_pos hr0)
  have ht0le1 : t0 ≤ 1 := min_le_left _ _
  have ht0lt : t0 < r0 := (min_le_right (1 : ℝ) (r0 / 2)).trans_lt (half_lt_self hr0)
  have ht0mem : t0 ∈ Ioo (0 : ℝ) r0 := ⟨ht0pos, ht0lt⟩
  set rSeq : ℕ → ℝ := fun m => r0 * ((m : ℝ) + 1) / ((m : ℝ) + 2)
  have hrSeq_pos (m : ℕ) : 0 < rSeq m := by
    dsimp [rSeq]
    positivity
  have hrSeq_lt (m : ℕ) : rSeq m < r0 := by
    dsimp [rSeq]
    have hfrac : ((m : ℝ) + 1) / ((m : ℝ) + 2) < 1 := by
      rw [div_lt_one (by positivity)]
      linarith
    calc
      r0 * ((m : ℝ) + 1) / ((m : ℝ) + 2)
          = r0 * (((m : ℝ) + 1) / ((m : ℝ) + 2)) := by rw [mul_div_assoc]
      _ < r0 * 1 := mul_lt_mul_of_pos_left hfrac hr0
      _ = r0 := mul_one r0
  have hrSeq_mem (m : ℕ) : rSeq m ∈ Ioo (0 : ℝ) r0 := ⟨hrSeq_pos m, hrSeq_lt m⟩
  have hrSeq_mono : Monotone rSeq := by
    intro i j hij
    dsimp [rSeq]
    have hijR : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    have hfrac :
        ((i : ℝ) + 1) / ((i : ℝ) + 2) ≤ ((j : ℝ) + 1) / ((j : ℝ) + 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hijR]
    calc
      r0 * ((i : ℝ) + 1) / ((i : ℝ) + 2)
          = r0 * (((i : ℝ) + 1) / ((i : ℝ) + 2)) := by rw [mul_div_assoc]
      _ ≤ r0 * (((j : ℝ) + 1) / ((j : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left hfrac hr0.le
      _ = r0 * ((j : ℝ) + 1) / ((j : ℝ) + 2) := by rw [mul_div_assoc]
  have hrSeq0 : rSeq 0 = r0 / 2 := by
    dsimp [rSeq]
    ring
  have ht0_le_rSeq (m : ℕ) : t0 ≤ rSeq m :=
    (min_le_right (1 : ℝ) (r0 / 2)).trans (hrSeq0 ▸ hrSeq_mono (Nat.zero_le m))
  have hball_mono : Monotone (fun m : ℕ => Metric.ball p (rSeq m)) :=
    fun i j hij => Metric.ball_subset_ball (hrSeq_mono hij)
  have hfrac_lim :
      Tendsto (fun m : ℕ => ((m : ℝ) + 1) / ((m : ℝ) + 2)) atTop (𝓝 1) := by
    have h :=
      (tendsto_natCast_div_add_atTop (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
    have hfun :
        (fun m : ℕ => ((m : ℝ) + 1) / ((m : ℝ) + 2)) =
          (fun n : ℕ => (n : ℝ) / (n + 1)) ∘ fun a => a + 1 := by
      funext m
      simp [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    rwa [hfun]
  have hrSeq_tendsto : Tendsto rSeq atTop (𝓝 r0) := by
    have hmul := hfrac_lim.const_mul r0
    simpa [rSeq, mul_div_assoc, mul_one] using hmul
  have hunion : (⋃ m : ℕ, Metric.ball p (rSeq m)) = Metric.ball p r0 := by
    ext x
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := mem_iUnion.mp hx
      exact (Metric.ball_subset_ball (hrSeq_lt m).le) hm
    · intro hx
      have hxlt : dist p x < r0 := by
        simpa [dist_comm] using (Metric.mem_ball.mp hx)
      have hev : ∀ᶠ m in atTop, dist p x < rSeq m :=
        hrSeq_tendsto.eventually (Ioi_mem_nhds hxlt)
      obtain ⟨m, hm⟩ := hev.exists
      exact mem_iUnion.mpr ⟨m, Metric.mem_ball.mpr (by simpa [dist_comm] using hm)⟩
  have hvol_iSup : vol r0 = ⨆ m : ℕ, vol (rSeq m) := by
    dsimp [vol]
    rw [← hunion]
    exact hball_mono.directed_le.measure_iUnion
  have hvol_t0 : ENNReal.ofReal v0 * Y t0 / Y r0 ≤ vol t0 := by
    have hpt (m : ℕ) : vol (rSeq m) * Y t0 / Y r0 ≤ vol t0 := by
      have hge := hratio_ge ht0mem (hrSeq_mem m) (ht0_le_rSeq m)
      have hYle : Y (rSeq m) ≤ Y r0 :=
        (hYmono (mem_Ioi.mpr (hrSeq_pos m)) (mem_Ioi.mpr hr0) (hrSeq_lt m)).le
      have hdiv :
          vol (rSeq m) * Y t0 / Y r0 ≤ vol (rSeq m) * Y t0 / Y (rSeq m) :=
        ENNReal.div_le_div_left hYle _
      exact hdiv.trans hge
    have hsup : (⨆ m : ℕ, vol (rSeq m)) * Y t0 / Y r0 ≤ vol t0 := by
      rw [ENNReal.iSup_mul, ENNReal.iSup_div]
      exact iSup_le hpt
    calc
      ENNReal.ofReal v0 * Y t0 / Y r0 ≤ vol r0 * Y t0 / Y r0 := by gcongr
      _ = (⨆ m : ℕ, vol (rSeq m)) * Y t0 / Y r0 := by rw [hvol_iSup]
      _ ≤ vol t0 := hsup
  have hpow_r0 : 0 < ENNReal.ofReal (r0 ^ nDim) :=
    ENNReal.ofReal_pos.mpr (pow_pos hr0 _)
  have hden0 : Y r0 * ENNReal.ofReal (r0 ^ nDim) ≠ 0 :=
    mul_ne_zero (hY0 hr0) hpow_r0.ne'
  set α : ℝ≥0∞ := ENNReal.ofReal v0 * ENNReal.ofReal c / Y r0
  set β : ℝ≥0∞ := ENNReal.ofReal v0 * Y t0 / (Y r0 * ENNReal.ofReal (r0 ^ nDim))
  have hαpos : 0 < α :=
    ENNReal.div_pos
      (ne_of_gt (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hv0).ne'
        (ENNReal.ofReal_pos.mpr hcpos).ne'))
      (hYtop r0)
  have hβpos : 0 < β :=
    ENNReal.div_pos
      (ne_of_gt (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hv0).ne' (hY0 ht0pos)))
      (ENNReal.mul_ne_top (hYtop r0) ENNReal.ofReal_ne_top)
  have hαtop : α ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      (hY0 hr0)
  have hβtop : β ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hYtop t0)) hden0
  have hminpos : 0 < min α β := lt_min hαpos hβpos
  have hmintop : min α β ≠ ⊤ := by
    intro h
    exact hαtop (min_eq_top.mp h).1
  refine ⟨(min α β).toReal, ENNReal.toReal_pos hminpos.ne' hmintop, ?_⟩
  intro s hs
  have hspos : 0 < s := hs.1
  have hsle : s ≤ r0 := hs.2
  have hvstar : ENNReal.ofReal (min α β).toReal = min α β :=
    ENNReal.ofReal_toReal hmintop
  rw [hvstar]
  by_cases hsmall : s ≤ t0
  · have hs01 : s ∈ Ioc (0 : ℝ) 1 := ⟨hspos, hsmall.trans ht0le1⟩
    have hpow : ENNReal.ofReal c * ENNReal.ofReal (s ^ nDim) ≤ Y s := by
      simpa [Y, nDim, finrank_coeffSpace (E := E)] using hc s hs01
    have hsmem : s ∈ Ioo (0 : ℝ) r0 := ⟨hspos, hsmall.trans_lt ht0lt⟩
    have hge := hratio_ge hsmem ht0mem hsmall
    have hcancel :
        ENNReal.ofReal v0 * Y t0 / Y r0 * (Y s / Y t0) =
          ENNReal.ofReal v0 * Y s / Y r0 := by
      calc
        ENNReal.ofReal v0 * Y t0 / Y r0 * (Y s / Y t0)
            = (ENNReal.ofReal v0 * Y t0 * (Y s / Y t0)) / Y r0 :=
              hdiv_mul _ _ _
        _ = (ENNReal.ofReal v0 * (Y t0 * (Y s / Y t0))) / Y r0 := by
              rw [mul_assoc]
        _ = ENNReal.ofReal v0 * Y s / Y r0 := by
              rw [ENNReal.mul_div_cancel (hY0 ht0pos) (hYtop t0)]
    have hchain : α * ENNReal.ofReal (s ^ nDim) ≤ vol s := by
      dsimp [α]
      calc
        ENNReal.ofReal v0 * ENNReal.ofReal c / Y r0 * ENNReal.ofReal (s ^ nDim)
            = ENNReal.ofReal v0 * ENNReal.ofReal c * ENNReal.ofReal (s ^ nDim) / Y r0 :=
              hdiv_mul _ _ _
        _ = ENNReal.ofReal v0 * (ENNReal.ofReal c * ENNReal.ofReal (s ^ nDim)) / Y r0 := by
              rw [mul_assoc]
        _ ≤ ENNReal.ofReal v0 * Y s / Y r0 := by gcongr
        _ = ENNReal.ofReal v0 * Y t0 / Y r0 * (Y s / Y t0) := hcancel.symm
        _ ≤ vol t0 * (Y s / Y t0) := by gcongr
        _ = vol t0 * Y s / Y t0 := by rw [← mul_div_assoc]
        _ ≤ vol s := hge
    have hminα : min α β * ENNReal.ofReal (s ^ nDim) ≤ α * ENNReal.ofReal (s ^ nDim) := by
      gcongr
      exact min_le_left _ _
    exact hminα.trans hchain
  · have ht0le : t0 ≤ s := le_of_not_ge hsmall
    have hvol_le : vol t0 ≤ vol s :=
      measure_mono (Metric.ball_subset_ball ht0le)
    have hsn : ENNReal.ofReal (s ^ nDim) ≤ ENNReal.ofReal (r0 ^ nDim) :=
      ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hspos.le hsle nDim)
    have hβmul :
        β * ENNReal.ofReal (r0 ^ nDim) = ENNReal.ofReal v0 * Y t0 / Y r0 := by
      dsimp [β]
      calc
        ENNReal.ofReal v0 * Y t0 / (Y r0 * ENNReal.ofReal (r0 ^ nDim)) *
              ENNReal.ofReal (r0 ^ nDim)
            = ENNReal.ofReal v0 * Y t0 * ENNReal.ofReal (r0 ^ nDim) /
                (Y r0 * ENNReal.ofReal (r0 ^ nDim)) :=
              hdiv_mul _ _ _
        _ = ENNReal.ofReal v0 * Y t0 / Y r0 :=
              ENNReal.mul_div_mul_right _ _ hpow_r0.ne' ENNReal.ofReal_ne_top
    have hchain : β * ENNReal.ofReal (s ^ nDim) ≤ vol s := by
      calc
        β * ENNReal.ofReal (s ^ nDim) ≤ β * ENNReal.ofReal (r0 ^ nDim) := by gcongr
        _ = ENNReal.ofReal v0 * Y t0 / Y r0 := hβmul
        _ ≤ vol t0 := hvol_t0
        _ ≤ vol s := hvol_le
    have hminβ : min α β * ENNReal.ofReal (s ^ nDim) ≤ β * ENNReal.ofReal (s ^ nDim) := by
      gcongr
      exact min_le_right _ _
    exact hminβ.trans hchain
/- SWARM_PROOF_END -/

end MorganTianLib

end

#print axioms MorganTianLib.riemannianMeasure_ball_ge_mul_pow_of_ricci
