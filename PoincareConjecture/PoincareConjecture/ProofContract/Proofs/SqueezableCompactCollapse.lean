import PoincareConjecture.ProofContract.Proofs.SupportedDisplacement
import PoincareConjecture.ProofContract.Proofs.UniformSurjectiveLimit
import PoincareConjecture.ProofContract.Proofs.ControlledUniformLimit
import PoincareConjecture.ProofContract.Proofs.ControlledCollapseFibers
import PoincareConjecture.ProofContract.V1.Obligations
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Proofs
open Set Function Filter Topology
open scoped Topology
theorem squeezable_compact_single_fiber_map {X : Type u} [MetricSpace X] [CompactSpace X]
    (K : Set X) (hK : IsCompact K) (hKn : K.Nonempty)
    (shrink : ∀ U : Set X, IsOpen U → K ⊆ U → ∀ eps : ℝ, 0 < eps →
      ∃ h : X ≃ₜ X, (∀ x, x∉U → h x=x) ∧ ∀ x∈K, ∀ y∈K, dist (h x) (h y) < eps) :
    ∃ q : X → X, Continuous q ∧ Surjective q ∧
      ∀ x y, q x=q y ↔ x=y ∨ (x∈K ∧ y∈K) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  let k₀ : X := Classical.choose hKn
  have hk₀ : k₀ ∈ K := Classical.choose_spec hKn
  let A : ℕ → Set X := fun n => Metric.thickening ((1 / 2 : ℝ) ^ n) K
  have hAopen : ∀ n, IsOpen (A n) := by
    intro n
    exact Metric.isOpen_thickening
  have hAK : ∀ n, K ⊆ A n := by
    intro n
    exact Metric.self_subset_thickening (by positivity) K
  have hAmono : Antitone A := by
    intro m n hmn
    apply Metric.thickening_mono _ K
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
  have hAcompact : ∀ n, IsCompact (closure (A n)) := by
    intro n
    exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
  let P : ℕ → (X ≃ₜ X) → Set X → Prop := fun n F U =>
    IsOpen U ∧ K ⊆ U ∧ IsCompact (closure U) ∧ U ⊆ A n ∧
      ∀ x ∈ K, ∀ y ∈ K, dist (F x) (F y) ≤ (1 / 2 : ℝ) ^ (n + 1)
  have hstage : ∀ (n : ℕ) (F : X ≃ₜ X) (U : Set X), P n F U →
      ∃ z : Set X × (X ≃ₜ X),
        P (n + 1) (z.2.trans F) z.1 ∧
          (∀ x, x ∉ z.1 → z.2 x = x) ∧ z.1 ⊆ A (n + 1) ∧
          (∀ x ∈ z.1, ∀ y ∈ z.1,
            dist (F x) (F y) ≤ 4 * (1 / 2 : ℝ) ^ (n + 1)) := by
    intro n F U hP
    have hFU : UniformContinuous (F : X → X) :=
      CompactSpace.uniformContinuous_of_continuous F.continuous
    obtain ⟨δ, hδ, hFδ⟩ := Metric.uniformContinuous_iff.mp hFU
      ((1 / 2 : ℝ) ^ (n + 2)) (by positivity)
    let W : Set X := A (n + 1) ∩
      F ⁻¹' Metric.ball (F k₀) (2 * (1 / 2 : ℝ) ^ (n + 1))
    have hWopen : IsOpen W := by
      exact (hAopen (n + 1)).inter (F.continuous.isOpen_preimage _ Metric.isOpen_ball)
    have hKW : K ⊆ W := by
      intro x hx
      refine ⟨hAK (n + 1) hx, ?_⟩
      apply Metric.mem_ball.mpr
      have hdist := hP.2.2.2.2 x hx k₀ hk₀
      have hp : 0 < (1 / 2 : ℝ) ^ (n + 1) := by positivity
      exact hdist.trans_lt (by nlinarith)
    obtain ⟨V, hVo, hKV, hVcl⟩ :=
      hK.exists_isOpen_closure_subset (hWopen.mem_nhdsSet.mpr hKW)
    have hVcompact : IsCompact (closure V) := by
      exact isCompact_univ.of_isClosed_subset isClosed_closure (subset_univ _)
    have hVsubA : V ⊆ A (n + 1) := by
      intro x hx
      exact (hVcl (subset_closure hx)).1
    have hVimage : ∀ x ∈ V, ∀ y ∈ V,
        dist (F x) (F y) ≤ 4 * (1 / 2 : ℝ) ^ (n + 1) := by
      intro x hx y hy
      have hxball : F x ∈ Metric.ball (F k₀) (2 * (1 / 2 : ℝ) ^ (n + 1)) :=
        (hVcl (subset_closure hx)).2
      have hyball : F y ∈ Metric.ball (F k₀) (2 * (1 / 2 : ℝ) ^ (n + 1)) :=
        (hVcl (subset_closure hy)).2
      have hxlt := Metric.mem_ball.mp hxball
      have hylt := Metric.mem_ball.mp hyball
      have hlt : dist (F x) (F y) < 4 * (1 / 2 : ℝ) ^ (n + 1) := by
        calc
          dist (F x) (F y) ≤ dist (F x) (F k₀) + dist (F k₀) (F y) :=
            dist_triangle _ _ _
          _ < 2 * (1 / 2 : ℝ) ^ (n + 1) +
              2 * (1 / 2 : ℝ) ^ (n + 1) :=
            add_lt_add hxlt (by simpa [dist_comm] using hylt)
          _ = 4 * (1 / 2 : ℝ) ^ (n + 1) := by ring
      exact hlt.le
    obtain ⟨h, hfix, hsmall⟩ := shrink V hVo hKV δ hδ
    refine ⟨(V, h), ?_, hfix, hVsubA, hVimage⟩
    refine ⟨hVo, hKV, hVcompact, hVsubA, ?_⟩
    intro x hx y hy
    simpa only [Homeomorph.trans_apply] using (hFδ (hsmall x hx y hy)).le
  have hinit : ∃ h : X ≃ₜ X,
      (∀ x, x ∉ A 0 → h x = x) ∧
        (∀ x ∈ K, ∀ y ∈ K, dist (h x) (h y) ≤ (1 / 2 : ℝ) ^ (0 + 1)) := by
    obtain ⟨h, hfix, hsmall⟩ := shrink (A 0) (hAopen 0) (hAK 0) (1 / 2) (by norm_num)
    refine ⟨h, hfix, ?_⟩
    intro x hx y hy
    simpa [pow_one] using (hsmall x hx y hy).le
  obtain ⟨h₀, h₀fix, h₀small⟩ := hinit
  let s₀ : (X ≃ₜ X) × Set X := (h₀, A 0)
  have hs₀ : P 0 s₀.1 s₀.2 := by
    refine ⟨hAopen 0, hAK 0, hAcompact 0, subset_rfl, ?_⟩
    exact h₀small
  let State : ℕ → Type u := fun n =>
    {s : (X ≃ₜ X) × Set X // P n s.1 s.2}
  let state₀ : State 0 := ⟨s₀, hs₀⟩
  let choice : ∀ (n : ℕ) (F : X ≃ₜ X) (U : Set X), P n F U →
      Set X × (X ≃ₜ X) := fun n F U hP =>
    Classical.choose (hstage n F U hP)
  have choice_spec : ∀ (n : ℕ) (F : X ≃ₜ X) (U : Set X) (hP : P n F U),
      P (n + 1) ((choice n F U hP).2.trans F) (choice n F U hP).1 ∧
        (∀ x, x ∉ (choice n F U hP).1 → (choice n F U hP).2 x = x) ∧
        (choice n F U hP).1 ⊆ A (n + 1) ∧
        (∀ x ∈ (choice n F U hP).1, ∀ y ∈ (choice n F U hP).1,
          dist (F x) (F y) ≤ 4 * (1 / 2 : ℝ) ^ (n + 1)) := by
    intro n F U hP
    exact Classical.choose_spec (hstage n F U hP)
  let step : ∀ (n : ℕ), State n → State (n + 1) × (X ≃ₜ X) := fun n s =>
    let z := choice n s.1.1 s.1.2 s.2
    ⟨⟨(z.2.trans s.1.1, z.1),
        (choice_spec n s.1.1 s.1.2 s.2).1⟩, z.2⟩
  let states : (n : ℕ) → State n := fun n =>
    Nat.rec state₀ (fun n s => (step n s).1) n
  let hseq : ℕ → X ≃ₜ X := fun n =>
    (choice n (states n).1.1 (states n).1.2 (states n).2).2
  let f : ℕ → X → X := fun n => (states n).1.1
  have hstate_succ (n : ℕ) : states (n + 1) = (step n (states n)).1 := by
    simp [states]
  have hstate_F (n : ℕ) :
      (states (n + 1)).1.1 = (hseq n).trans (states n).1.1 := by
    rw [hstate_succ]
  have hstate_U (n : ℕ) :
      (states (n + 1)).1.2 =
        (choice n (states n).1.1 (states n).1.2 (states n).2).1 := by
    rw [hstate_succ]
  have hlocal : ∀ n x, x ∉ (states (n + 1)).1.2 → hseq n x = x := by
    intro n x hx
    have hz := choice_spec n (states n).1.1 (states n).1.2 (states n).2
    rw [hstate_U] at hx
    exact hz.2.1 x hx
  have hUsmall : ∀ n, (states (n + 1)).1.2 ⊆ A (n + 1) := by
    intro n
    rw [hstate_U]
    exact (choice_spec n (states n).1.1 (states n).1.2 (states n).2).2.2.1
  have hmapU : ∀ n x, x ∈ (states (n + 1)).1.2 →
      hseq n x ∈ (states (n + 1)).1.2 := by
    intro n x hx
    by_contra hnot
    have hfixed : hseq n (hseq n x) = hseq n x := hlocal n (hseq n x) hnot
    have hxeq : x = hseq n x := hseq n |>.injective hfixed.symm
    exact hnot (hxeq ▸ hx)
  have hsupport : ∀ n : ℕ, ∀ x : X, x ∈ (states (n + 1)).1.2 →
      ∀ y : X, y ∈ (states (n + 1)).1.2 →
        dist ((states n).1.1 x) ((states n).1.1 y) ≤
          4 * (1 / 2 : ℝ) ^ (n + 1) := by
    intro n x hx y hy
    rw [hstate_U] at hx hy
    exact (choice_spec n (states n).1.1 (states n).1.2 (states n).2).2.2.2 x hx y hy
  have ha : ∀ n, 0 ≤ 2 * (1 / 2 : ℝ) ^ n := by
    intro n
    positivity
  have hsum : Summable (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) := by
    exact Summable.mul_left 2 summable_geometric_two
  have hfstep : ∀ n x, dist (f (n + 1) x) (f n x) ≤
      2 * (1 / 2 : ℝ) ^ n := by
    intro n x
    by_cases hx : x ∈ (states (n + 1)).1.2
    · have hx' := hmapU n x hx
      have hdist := hsupport n x hx (hseq n x) hx'
      calc
        dist (f (n + 1) x) (f n x) =
            dist ((hseq n).trans (states n).1.1 x) ((states n).1.1 x) := by
              simp [f, hstate_F, Homeomorph.trans_apply]
        _ ≤ 4 * (1 / 2 : ℝ) ^ (n + 1) := by
          change dist ((states n).1.1 (hseq n x)) ((states n).1.1 x) ≤ _
          rw [dist_comm]
          exact hdist
        _ = 2 * (1 / 2 : ℝ) ^ n := by
          rw [pow_succ]
          ring
    · have hfix := hlocal n x hx
      simp [f, hstate_F, Homeomorph.trans_apply, hfix]
  obtain ⟨q, hq, hf⟩ := continuous_limit_of_summable_steps f
    (fun n => (states n).1.1.continuous) (fun n => 2 * (1 / 2 : ℝ) ^ n)
    ha hsum hfstep
  have hsurj : ∀ n, Surjective (f n) := by
    intro n y
    exact ⟨(states n).1.1.symm y, by simp [f]⟩
  have hqsurj : Surjective q :=
    uniform_limit_surjective_compact f q hq hsurj hf
  have hsmall : ∀ n x y, x ∈ K → y ∈ K →
      dist (f n x) (f n y) ≤ (1 / 2 : ℝ) ^ n := by
    intro n x y hx hy
    have hxy := (states n).2.2.2.2.2 x hx y hy
    have hp : (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ n := by
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
    exact hxy.trans hp
  have hexternal : ∀ z, z ∉ K → ∃ N, z ∉ closure (A N) := by
    intro z hz
    have hzcl : z ∉ closure K := by
      simpa [hK.isClosed.closure_eq] using hz
    obtain ⟨ε, hε, hεinf⟩ :=
      Metric.exists_real_pos_lt_infEDist_of_notMem_closure hzcl
    have hpows : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨N, hN⟩ :=
      eventually_atTop.1 ((tendsto_order.1 hpows).2 ε hε)
    refine ⟨N, ?_⟩
    intro hzclA
    have hzct : z ∈ Metric.cthickening ((1 / 2 : ℝ) ^ N) K := by
      exact Metric.closure_thickening_subset_cthickening _ _ hzclA
    rw [Metric.mem_cthickening_iff] at hzct
    have hpowε : ENNReal.ofReal ((1 / 2 : ℝ) ^ N) < ENNReal.ofReal ε :=
      (ENNReal.ofReal_lt_ofReal_iff hε).mpr (hN N le_rfl)
    exact (not_lt_of_ge hzct) (hpowε.trans hεinf)
  have hstable : ∀ N z, z ∉ closure (A N) → ∀ n ≥ N, f n z = f N z := by
    intro N z hz n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
        have hzAN : z ∉ A N := fun hz' => hz (subset_closure hz')
        have hAN : A (n + 1) ⊆ A N :=
          hAmono (by omega)
        have hzU : z ∉ (states (n + 1)).1.2 := by
          intro hzU
          exact hzAN (hAN (hUsmall n hzU))
        have hfix := hlocal n z hzU
        calc
          f (n + 1) z = (hseq n).trans (states n).1.1 z := by
            simp [f, hstate_F]
          _ = (states n).1.1 (hseq n z) := by rfl
          _ = f n z := by rw [hfix]
          _ = f N z := ih
  have hmap_closure : ∀ N n, N ≤ n →
      ∀ z ∈ closure (A N), hseq n z ∈ closure (A N) := by
    intro N n hn z hz
    by_cases hzU : z ∈ (states (n + 1)).1.2
    · have hmap := hmapU n z hzU
      have hAN : A (n + 1) ⊆ A N := hAmono (by omega)
      exact subset_closure (hAN (hUsmall n hmap))
    · simpa [hlocal n z hzU] using hz
  have himage : ∀ N n, N ≤ n → ∀ z ∈ closure (A N),
      ∃ w ∈ closure (A N), f n z = f N w := by
    intro N n hn z hz
    induction n, hn using Nat.le_induction generalizing z with
    | base => exact ⟨z, hz, rfl⟩
    | succ n hn ih =>
        obtain ⟨w, hw, hzw⟩ := ih (hseq n z) (hmap_closure N n hn z hz)
        refine ⟨w, hw, ?_⟩
        calc
          f (n + 1) z = (states n).1.1 (hseq n z) := by
            simp [f, hstate_F, Homeomorph.trans_apply]
          _ = f N w := by simpa only [f] using hzw
  have hinout : ∀ x y, x ∈ K → y ∉ K → x ≠ y →
      ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N,
        ε ≤ dist (f n x) (f n y) := by
    intro x y hx hy hxy
    obtain ⟨N, hN⟩ := hexternal y hy
    let C : Set X := f N '' closure (A N)
    have hCcompact : IsCompact C := by
      exact (hAcompact N).image (states N).1.1.continuous
    have hpC : f N y ∉ C := by
      intro hp
      obtain ⟨z, hz, hzy⟩ := hp
      have hzy' : (states N).1.1 z = (states N).1.1 y := by
        simpa [f] using hzy
      have hzy'' : z = y := (states N).1.1.injective hzy'
      exact hN (hzy'' ▸ hz)
    have hpcl : f N y ∉ closure C := by
      simpa [hCcompact.isClosed.closure_eq] using hpC
    have hpcl' := hpcl
    rw [Metric.mem_closure_iff] at hpcl'
    push Not at hpcl'
    obtain ⟨ε, hε, hεC⟩ := hpcl'
    refine ⟨ε, hε, N, ?_⟩
    intro n hn
    have hxcl : x ∈ closure (A N) := subset_closure (hAK N hx)
    obtain ⟨z, hz, hxz⟩ := himage N n hn x hxcl
    have hxf : f n x ∈ C := ⟨z, hz, hxz.symm⟩
    have hyf := hstable N y hN n hn
    rw [hyf]
    calc
      ε ≤ dist (f N y) (f n x) := hεC (f n x) hxf
      _ = dist (f n x) (f N y) := dist_comm _ _
  have houtin : ∀ x y, x ∉ K → y ∈ K → x ≠ y →
      ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N,
        ε ≤ dist (f n x) (f n y) := by
    intro x y hx hy hxy
    obtain ⟨ε, hε, N, hN⟩ := hinout y x hy hx hxy.symm
    refine ⟨ε, hε, N, ?_⟩
    intro n hn
    calc
      ε ≤ dist (f n y) (f n x) := hN n hn
      _ = dist (f n x) (f n y) := dist_comm _ _
  have houtout : ∀ x y, x ∉ K → y ∉ K → x ≠ y →
      ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N,
        ε ≤ dist (f n x) (f n y) := by
    intro x y hx hy hxy
    obtain ⟨Nx, hNx⟩ := hexternal x hx
    obtain ⟨Ny, hNy⟩ := hexternal y hy
    let N := max Nx Ny
    have hNxN : x ∉ closure (A N) := by
      intro hxN
      exact hNx (closure_mono (hAmono (le_max_left _ _)) hxN)
    have hNyN : y ∉ closure (A N) := by
      intro hyN
      exact hNy (closure_mono (hAmono (le_max_right _ _)) hyN)
    have hdistpos : 0 < dist (f N x) (f N y) := by
      apply dist_pos.mpr
      intro hxyf
      apply hxy
      apply (states N).1.1.injective
      simpa [f] using hxyf
    refine ⟨dist (f N x) (f N y) / 2, by linarith, N, ?_⟩
    intro n hn
    have hxn := hstable N x hNxN n hn
    have hyn := hstable N y hNyN n hn
    rw [hxn, hyn]
    nlinarith
  have hsep : ∀ x y, x ≠ y → ¬ (x ∈ K ∧ y ∈ K) →
      ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ, ∀ n ≥ N,
        ε ≤ dist (f n x) (f n y) := by
    intro x y hxy hnot
    by_cases hx : x ∈ K
    · have hy : y ∉ K := by
        intro hy
        exact hnot ⟨hx, hy⟩
      exact hinout x y hx hy hxy
    · by_cases hy : y ∈ K
      · exact houtin x y hx hy hxy
      · exact houtout x y hx hy hxy
  have hfib := uniform_limit_exact_fibers f q K hf hsmall hsep
  exact ⟨q, hq, hqsurj, hfib⟩
/- SWARM_PROOF_END -/
end PoincareConjecture.ProofContract.Proofs
