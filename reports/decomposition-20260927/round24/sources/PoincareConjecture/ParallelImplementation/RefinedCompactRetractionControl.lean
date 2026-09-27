import PoincareConjecture.ProofContract.Refinement20260927.AmbientApproximationLeaves
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ParallelImplementation.RefinedCompactRetractionControl
open PoincareConjecture.ProofContract.Refinement20260927
theorem compact_retraction_control : CompactRetractionControlStatement.{u} :=
/- SWARM_PROOF_BEGIN -/
by
  intro N n R
  let P : ApproxAmbient n → ApproxAmbient n := embeddedRetractMap R
  rcases R with ⟨A, hEmbed, L, hAgree, hLocal⟩
  cases A with
  | mk embed domain hOpen hContains retract hRetEmbed =>
    have hPmd : ContMDiffOn (modelWithCornersSelf ℝ (ApproxAmbient n))
        (modelWithCornersSelf ℝ (ApproxAmbient n)) (↑(⊤ : ℕ∞)) P domain := by
      simpa [P, embeddedRetractMap] using
        hEmbed.contMDiffOn.comp hLocal Set.subset_preimage_univ
    have hPcd : ContDiffOn ℝ (↑(⊤ : ℕ∞)) P domain :=
      (contMDiffOn_iff_contDiffOn).mp hPmd

    have hK : IsCompact (Set.range (⇑embed)) := isCompact_range embed.continuous
    have hKdomain : Set.range (⇑embed) ⊆ domain := by
      rintro x ⟨p, rfl⟩
      exact hContains p
    obtain ⟨d, hdpos, hdsub⟩ := hK.exists_cthickening_subset_open hOpen hKdomain
    let C : Set (ApproxAmbient n) := Metric.cthickening d (Set.range (⇑embed))
    have hCcompact : IsCompact C := by
      change IsCompact (Metric.cthickening d (Set.range (⇑embed)))
      exact hK.cthickening
    have hCdomain : C ⊆ domain := by
      change Metric.cthickening d (Set.range (⇑embed)) ⊆ domain
      exact hdsub

    have hPcont : ContinuousOn P domain := hPcd.continuousOn
    have hPcontC : ContinuousOn P C := hPcont.mono hCdomain
    have hDcont : ContinuousOn (fderiv ℝ P) domain :=
      hPcd.continuousOn_fderiv_of_isOpen hOpen (by simp)
    have hDcontC : ContinuousOn (fderiv ℝ P) C := hDcont.mono hCdomain
    have hPuniform : UniformContinuousOn P C :=
      hCcompact.uniformContinuousOn_of_continuous hPcontC
    have hDuniform : UniformContinuousOn (fderiv ℝ P) C :=
      hCcompact.uniformContinuousOn_of_continuous hDcontC

    have hBounded := (hCcompact.image_of_continuousOn hDcontC).isBounded
    obtain ⟨B, hB⟩ := hBounded.exists_norm_le
    let Q : ℝ := max B 0

    have hFix : ∀ x ∈ Set.range (⇑embed), P x = x := by
      rintro x ⟨p, rfl⟩
      calc
        P (⇑embed p) = ⇑embed (L (⇑embed p)) := by
          simp [P, embeddedRetractMap]
        _ = ⇑embed (retract ⟨⇑embed p, hContains p⟩) := by
          rw [hAgree (⇑embed p) (hContains p)]
        _ = ⇑embed p := by
          rw [hRetEmbed p]

    have hControlP :
        ∃ Q' : ℝ, 0 ≤ Q' ∧ ∀ eta : ℝ, 0 < eta → ∃ rho : ℝ, 0 < rho ∧
          ∀ (x : ApproxAmbient n), x ∈ Set.range (⇑embed) →
            ∀ y : ApproxAmbient n, dist y x < rho →
              y ∈ domain ∧ dist (P y) x < eta ∧
                ‖fderiv ℝ P y - fderiv ℝ P x‖ ≤ eta ∧ ‖fderiv ℝ P y‖ ≤ Q' := by
      refine ⟨Q, le_max_right B 0, ?_⟩
      intro eta heta
      obtain ⟨rP, hrPpos, hPmod⟩ := (Metric.uniformContinuousOn_iff.mp hPuniform) eta heta
      obtain ⟨rD, hrDpos, hDmod⟩ := (Metric.uniformContinuousOn_iff.mp hDuniform) eta heta
      let rho : ℝ := min d (min rP rD)
      have hrhopos : 0 < rho := by
        dsimp [rho]
        exact lt_min hdpos (lt_min hrPpos hrDpos)
      have hrhod : rho ≤ d := by
        dsimp [rho]
        exact min_le_left _ _
      have hrhoP : rho ≤ rP := by
        dsimp [rho]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      have hrhoD : rho ≤ rD := by
        dsimp [rho]
        exact le_trans (min_le_right _ _) (min_le_right _ _)
      refine ⟨rho, hrhopos, ?_⟩
      intro x hx y hxy
      have hxC : x ∈ C := by
        change x ∈ Metric.cthickening d (Set.range (⇑embed))
        exact Metric.self_subset_cthickening (δ := d) _ hx
      have hyC : y ∈ C := by
        change y ∈ Metric.cthickening d (Set.range (⇑embed))
        apply Metric.mem_cthickening_of_dist_le y x d (Set.range (⇑embed)) hx
        exact le_of_lt (hxy.trans_le hrhod)
      have hxy' : dist x y < rP := by
        calc
          dist x y = dist y x := dist_comm _ _
          _ < rho := hxy
          _ ≤ rP := hrhoP
      have hxy'' : dist x y < rD := by
        calc
          dist x y = dist y x := dist_comm _ _
          _ < rho := hxy
          _ ≤ rD := hrhoD
      have hPy : dist (P y) x < eta := by
        calc
          dist (P y) x = dist (P y) (P x) := by rw [hFix x hx]
          _ = dist (P x) (P y) := dist_comm _ _
          _ < eta := hPmod x hxC y hyC hxy'
      have hDy : ‖fderiv ℝ P y - fderiv ℝ P x‖ ≤ eta := by
        have hDxy : ‖fderiv ℝ P x - fderiv ℝ P y‖ < eta := by
          simpa only [dist_eq_norm] using hDmod x hxC y hyC hxy''
        rw [norm_sub_rev]
        exact le_of_lt hDxy
      have hQy : ‖fderiv ℝ P y‖ ≤ Q := by
        calc
          ‖fderiv ℝ P y‖ ≤ B := hB _ ⟨y, hyC, rfl⟩
          _ ≤ max B 0 := le_max_left _ _
      exact ⟨hCdomain hyC, hPy, hDy, hQy⟩

    constructor
    · simpa [P, embeddedRetractMap] using hPcd
    · simpa [P, Q] using hControlP
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.RefinedCompactRetractionControl
