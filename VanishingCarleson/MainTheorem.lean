/-
# The beta-number Carleson estimate, the `Θ_h` estimate, and the main theorem
(Sections 8 and 9)

* Theorem (Comparison)                      — `compare_beta_eps` (proved in `ProofSteps.lean`)
* Theorem (Beta-number Carleson estimate)   — `beta_carleson_master` (in `ProofSteps.lean`),
  `beta_carleson_uniform` (C), `beta_carleson_vanishing` (V)
* Theorem (`Θ_h` Carleson estimate)          — `theta_carleson`
* Bridge (`SS(ℝ)` forces quasisymmetry)      — `ss_imp_quasisymmetric`
* Theorem 1 (Main theorem)                  — `main_theorem`
-/
import Mathlib
import VanishingCarleson.ProofSteps

open MeasureTheory Real Set

noncomputable section

namespace VanishingCarleson


/- **Theorem (Comparison)**: if `h` is increasing and locally absolutely
continuous and `w = h' ∈ A_∞(ℝ)` with constants `C₁, σ` as in (A1), then for
every bounded interval `J`,
`∬_{Q_J} β_h² dxdy/y ≤ C₂ ∬_{Q_{3J}} ε_h² dxdy/y`.

Proved in `ProofSteps.lean` as `compare_beta_eps`, placed there (rather than here) because its
proof needs `beta_sq_pointwise_bound` and `carlesonBoxIntegral_dyadicShift`, both of which are
downstream of this file in the Lean import order (the same "relocate near the actual use-site"
pattern already used for `denominator_lower_bounds`'s helper lemmas). See `ProofSteps.lean` for
the statement (it carries one additional hypothesis, `hfin`, needed to rule out the Bochner-junk-
value degenerate case) and proof. -/

/-- **Theorem (Beta-number Carleson estimate), part (C)**: under the same
hypotheses, `sup_J ‖β_h‖_{T²(J)} < ∞` — i.e. `β_h² dxdy/y` is a Carleson
measure on `𝕌`, with constant depending only on the `A_∞` constant. -/
theorem beta_carleson_uniform (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (hsurj : Function.Surjective h)
    (hw : AInfinityWeight (deriv h)) :
    IsCarlesonFn (betaPt h) :=
  isCarlesonFn_betaPt h hh hac hsurj hw

/-- **Theorem (Beta-number Carleson estimate), part (V)**: if moreover
`α = log h' ∈ VMO(ℝ)`, then `β_h² dxdy/y` is a vanishing Carleson measure:
`‖β_h‖_{T²(J)} → 0` as `|J| → 0`, uniformly in the position of `J`. -/
theorem beta_carleson_vanishing (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (hsurj : Function.Surjective h)
    (hw : AInfinityWeight (deriv h))
    (hvmo : VMO (fun t => Real.log (deriv h t))) :
    IsVanishingCarleson (betaPt h) :=
  isVanishingCarleson_betaPt h hh hac hsurj hw hvmo

/-! ### Auxiliary lemmas for `theta_carleson` -/

/-- `β_h ≥ 0` everywhere: it is an infimum of non-negative reals (and `sInf ∅ = 0`). -/
private lemma thetaC_betaPt_nonneg (h : ℝ → ℝ) (x y : ℝ) : 0 ≤ betaPt h x y := by
  unfold betaPt beta
  exact Real.sInf_nonneg fun _ ⟨_, _, hr, _⟩ => hr

/-- `β_h(x, y) ≤ 1` for `y > 0` (Lemma (Crude Beta Bound)). -/
private lemma thetaC_betaPt_le_one (h : ℝ → ℝ) (hh : StrictMono h) (x y : ℝ) (hy : 0 < y) :
    betaPt h x y ≤ 1 :=
  crude_beta_bound h hh (x - y) (x + y) (by linarith)

/-- Joint measurability of `β_h`, via a piecewise combination of the continuity off the
`y = 0` line (`continuous_betaPt`) and the vanishing of `β_h` on `y ≤ 0`
(degenerate/reversed intervals). -/
private lemma thetaC_betaPt_measurable (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h) :
    Measurable fun p : ℝ × ℝ => betaPt h p.1 p.2 := by
  classical
  have hzeroEq : ∀ a : ℝ, beta h a a = 0 := by
    intro a
    have hset_eq : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
        r = ((a - a) * (h a - h a))⁻¹ * ∫ t in a..a, |h t - (κ * t + τ)| } = {0} := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, sub_self, inv_zero,
        intervalIntegral.integral_same, mul_zero]
      constructor
      · rintro ⟨κ, τ, _, hr⟩; exact hr
      · rintro rfl; exact ⟨0, 0, le_refl 0, rfl⟩
    unfold beta
    rw [hset_eq, csInf_singleton]
  have hzeroGt : ∀ a b : ℝ, b < a → beta h a b = 0 := by
    intro a b hba
    have hset_sub : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
        r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| } ⊆ {0} := by
      rintro r ⟨κ, τ, hr0, hreq⟩
      have hprod_pos : (0 : ℝ) < (b - a) * (h b - h a) :=
        mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr (hh hba))
      have hint_le : (∫ t in a..b, |h t - (κ * t + τ)|) ≤ 0 := by
        have hsym : ∫ t in a..b, |h t - (κ * t + τ)| = -∫ t in b..a, |h t - (κ * t + τ)| :=
          intervalIntegral.integral_symm _ _
        have hnn : (0 : ℝ) ≤ ∫ t in b..a, |h t - (κ * t + τ)| :=
          intervalIntegral.integral_nonneg hba.le (fun _ _ => abs_nonneg _)
        linarith [hsym, hnn]
      have hrle : r ≤ 0 := by
        rw [hreq]
        exact mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hprod_pos).le hint_le
      exact Set.mem_singleton_iff.mpr (le_antisymm hrle hr0)
    unfold beta
    by_cases hS : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
        r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| }.Nonempty
    · obtain ⟨r₀, hr₀⟩ := hS
      have hr₀0 : r₀ = 0 := Set.mem_singleton_iff.mp (hset_sub hr₀)
      have hSeq : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
          r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| } = {0} :=
        Set.Subset.antisymm hset_sub (Set.singleton_subset_iff.mpr (hr₀0 ▸ hr₀))
      rw [hSeq, csInf_singleton]
    · rw [Set.not_nonempty_iff_eq_empty] at hS
      rw [hS, Real.sInf_empty]
  have hzero : ∀ p : ℝ × ℝ, p.2 ≤ 0 → betaPt h p.1 p.2 = 0 := by
    intro p hp
    rcases hp.lt_or_eq with hlt | heq
    · exact hzeroGt (p.1 - p.2) (p.1 + p.2) (by linarith)
    · show beta h (p.1 - p.2) (p.1 + p.2) = 0
      rw [heq]
      simp only [sub_zero, add_zero]
      exact hzeroEq p.1
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.2} := measurableSet_lt measurable_const measurable_snd
  have hf : ContinuousOn (fun p : ℝ × ℝ => betaPt h p.1 p.2) {p : ℝ × ℝ | 0 < p.2} :=
    (continuous_betaPt h hh hc).mono (fun p hp => ne_of_gt hp)
  have hg : ContinuousOn (fun _ : ℝ × ℝ => (0:ℝ)) {p : ℝ × ℝ | 0 < p.2}ᶜ := continuousOn_const
  have hpm := hf.measurable_piecewise hg hs
  have heq : Set.piecewise {p : ℝ × ℝ | 0 < p.2} (fun p : ℝ × ℝ => betaPt h p.1 p.2)
      (fun _ : ℝ × ℝ => (0:ℝ)) = fun p : ℝ × ℝ => betaPt h p.1 p.2 := by
    funext p
    by_cases hp : 0 < p.2
    · simp [Set.piecewise, hp]
    · have hp' : p ∉ {p : ℝ × ℝ | 0 < p.2} := hp
      rw [Set.piecewise_eq_of_notMem _ _ _ hp']
      exact (hzero p (not_lt.mp hp)).symm
  rwa [heq] at hpm


/-- Measurability of the dilated beta-number `(x, y) ↦ β_h(x, c y)`. -/
private lemma thetaC_betaPt_dil_measurable (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (c : ℝ) : Measurable fun p : ℝ × ℝ => betaPt h p.1 (c * p.2) :=
  (thetaC_betaPt_measurable h hh hc).comp (f := fun p : ℝ × ℝ => (p.1, c * p.2))
    (measurable_fst.prodMk (measurable_snd.const_mul c))

/-- Measurability of the slice `Y ↦ β_h(x, Y)`. -/
private lemma thetaC_betaPt_slice_measurable (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (x : ℝ) : Measurable (betaPt h x) :=
  (thetaC_betaPt_measurable h hh hc).comp (f := fun Y : ℝ => (x, Y))
    (measurable_const.prodMk measurable_id)

/-- Tonelli decomposition of the box `lintegral` into an iterated `lintegral`. -/
private lemma thetaC_box_eq_iter (F : ℝ → ℝ → ℝ)
    (hFm : Measurable fun p : ℝ × ℝ => F p.1 p.2) (a b : ℝ) :
    carlesonBoxLIntegral F a b =
      ∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a), ENNReal.ofReal ((F x y) ^ 2 / y) := by
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((F p.1 p.2) ^ 2 / p.2) :=
    ((hFm.pow_const 2).div measurable_snd).ennreal_ofReal
  unfold carlesonBoxLIntegral carlesonBox
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict,
    MeasureTheory.lintegral_prod _ hg.aemeasurable]

/-- **The `dy/y = dY/Y` scale invariance**: for `k > 0`, substituting `Y = k y`
in `∫ G(ky)²/y dy` over `(0, L]` gives `∫ G(Y)²/Y dY` over `(0, kL]`. -/
private lemma thetaC_y_scale (k : ℝ) (hk : 0 < k) (L : ℝ) (G : ℝ → ℝ)
    (hG : Measurable G) :
    ∫⁻ y in Set.Ioc (0:ℝ) L, ENNReal.ofReal (G (k * y) ^ 2 / y) =
      ∫⁻ Y in Set.Ioc (0:ℝ) (k * L), ENNReal.ofReal (G Y ^ 2 / Y) := by
  have hk0 : k ≠ 0 := hk.ne'
  set f : ℝ → ENNReal := fun Y => ENNReal.ofReal (G Y ^ 2 / Y) with hfdef
  have hfmeas : Measurable f := (hG.pow_const 2).div measurable_id |>.ennreal_ofReal
  have hpt : ∀ y : ℝ, ENNReal.ofReal (G (k * y) ^ 2 / y) = ENNReal.ofReal k * f (k * y) := by
    intro y
    rcases eq_or_ne y 0 with hy0 | hy0
    · simp [hy0, hfdef]
    · show ENNReal.ofReal (G (k * y) ^ 2 / y) =
        ENNReal.ofReal k * ENNReal.ofReal (G (k * y) ^ 2 / (k * y))
      rw [← ENNReal.ofReal_mul hk.le]
      congr 1
      field_simp
  have step1 : (∫⁻ y in Set.Ioc (0:ℝ) L, ENNReal.ofReal (G (k * y) ^ 2 / y)) =
      ∫⁻ y in Set.Ioc (0:ℝ) L, ENNReal.ofReal k * f (k * y) := by
    congr 1
    exact funext hpt
  rw [step1, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hpre : (fun y : ℝ => k * y) ⁻¹' (Set.Ioc (0:ℝ) (k * L)) = Set.Ioc (0:ℝ) L := by
    ext y
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, by nlinarith⟩
      by_contra hy
      push Not at hy
      have hle : k * y ≤ k * 0 := mul_le_mul_of_nonneg_left hy hk.le
      simp at hle
      linarith
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hmap : Measure.map (fun y : ℝ => k * y) volume = ENNReal.ofReal k⁻¹ • volume := by
    rw [Real.map_volume_mul_left hk0, abs_of_pos (inv_pos.mpr hk)]
  have hkey := setLIntegral_map (μ := volume) (f := f) (g := fun y : ℝ => k * y)
      (measurableSet_Ioc (a := (0:ℝ)) (b := k * L)) hfmeas (measurable_const_mul k)
  rw [hmap, hpre] at hkey
  rw [← hkey]
  have hsmul : (∫⁻ Y in Set.Ioc (0:ℝ) (k * L), f Y ∂(ENNReal.ofReal k⁻¹ • volume)) =
      ENNReal.ofReal k⁻¹ * ∫⁻ Y in Set.Ioc (0:ℝ) (k * L), f Y := by
    rw [Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  rw [hsmul, ← mul_assoc, ← ENNReal.ofReal_mul hk.le, mul_inv_cancel₀ hk0, ENNReal.ofReal_one,
    one_mul]

/-- **Head bound (eq. `head-new`)**: after the change of variables `Y = 2^k y`, the region
`{x ∈ J, 0 < Y ≤ 2^k |J|}` lies in the Carleson box of the interval `J_k` concentric with
`J = [a, b]` of length `2^k |J|`. -/
private lemma thetaC_head (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h) (a b : ℝ)
    (hab : a < b) (k : ℕ) :
    carlesonBoxLIntegral (fun x y => betaPt h x (2 ^ k * y)) a b ≤
      carlesonBoxLIntegral (betaPt h) ((a + b) / 2 - 2 ^ k * (b - a) / 2)
        ((a + b) / 2 + 2 ^ k * (b - a) / 2) := by
  have hβm := thetaC_betaPt_measurable h hh hc
  have hk : (0:ℝ) < 2 ^ k := by positivity
  have hk1 : (1:ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hL : b - a ≤ 2 ^ k * (b - a) := by
    have := mul_le_mul_of_nonneg_right hk1 (sub_pos.mpr hab).le
    linarith
  have hm : Measurable fun p : ℝ × ℝ => betaPt h p.1 (2 ^ k * p.2) :=
    thetaC_betaPt_dil_measurable h hh hc (2 ^ k)
  have hinner : ∀ x : ℝ,
      ∫⁻ y in Set.Ioc (0:ℝ) (b - a), ENNReal.ofReal (betaPt h x (2 ^ k * y) ^ 2 / y) =
        ∫⁻ Y in Set.Ioc (0:ℝ) (2 ^ k * (b - a)), ENNReal.ofReal (betaPt h x Y ^ 2 / Y) :=
    fun x => thetaC_y_scale (2 ^ k) hk (b - a) (betaPt h x)
      (thetaC_betaPt_slice_measurable h hh hc x)
  have hlen : (a + b) / 2 + 2 ^ k * (b - a) / 2 - ((a + b) / 2 - 2 ^ k * (b - a) / 2) =
      2 ^ k * (b - a) := by ring
  have e1 := thetaC_box_eq_iter (fun x y => betaPt h x (2 ^ k * y)) hm a b
  have e2 := thetaC_box_eq_iter (betaPt h) hβm ((a + b) / 2 - 2 ^ k * (b - a) / 2)
    ((a + b) / 2 + 2 ^ k * (b - a) / 2)
  have hsub : Set.Ioc a b ⊆
      Set.Ioc ((a + b) / 2 - 2 ^ k * (b - a) / 2) ((a + b) / 2 + 2 ^ k * (b - a) / 2) :=
    Set.Ioc_subset_Ioc (by linarith) (by linarith)
  rw [e1, e2, hlen, lintegral_congr hinner]
  exact lintegral_mono_set hsub

/-- **Weighted Cauchy–Schwarz** for the scale average: if `0 ≤ c_k ≤ 1`, then
`(∑ 4^{-k} c_k)² ≤ (∑ 4^{-k}) (∑ 4^{-k} c_k²) = (4/3) ∑ 4^{-k} c_k²`. -/
private lemma thetaC_sq_tsum_le (c : ℕ → ℝ) (hc0 : ∀ k, 0 ≤ c k) (hc1 : ∀ k, c k ≤ 1) :
    (∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k) ^ 2 ≤ 4 / 3 * ∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2 := by
  have hw : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hwsum : ∑' k : ℕ, (1 / 4 : ℝ) ^ k = 4 / 3 := by
    rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num)]
    norm_num
  have hf : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k * c k :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (by positivity) (hc0 k))
      (fun k => mul_le_of_le_one_right (by positivity) (hc1 k)) hw
  have hg0 : ∀ k : ℕ, 0 ≤ (1 / 4 : ℝ) ^ k * c k ^ 2 :=
    fun k => mul_nonneg (by positivity) (sq_nonneg _)
  have hg : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k * c k ^ 2 :=
    Summable.of_nonneg_of_le hg0
      (fun k => mul_le_of_le_one_right (by positivity) (pow_le_one₀ (hc0 k) (hc1 k))) hw
  refine le_of_tendsto' (hf.hasSum.tendsto_sum_nat.pow 2) fun n => ?_
  have hcs : (∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k * c k) ^ 2 ≤
      (∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k) *
        ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k * c k ^ 2 :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun k _ => by positivity)
      (fun k _ => hg0 k) (fun k _ => le_of_eq (by ring))
  have h1 : ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k ≤ 4 / 3 :=
    calc ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k ≤ ∑' k : ℕ, (1 / 4 : ℝ) ^ k :=
          hw.sum_le_tsum _ fun k _ => by positivity
      _ = 4 / 3 := hwsum
  have h2 : ∑ k ∈ Finset.range n, (1 / 4 : ℝ) ^ k * c k ^ 2 ≤
      ∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2 :=
    hg.sum_le_tsum _ fun k _ => hg0 k
  exact hcs.trans (mul_le_mul h1 h2 (Finset.sum_nonneg fun k _ => hg0 k) (by norm_num))

/-- Pointwise form of the weighted Cauchy–Schwarz bound, for the integrand of the box
integral: `Θ_h² / y ≤ ∑ (4/3) 4^{-k} β_h(x, 2^k y)² / y` (trivially for `y ≤ 0`). -/
private lemma thetaC_pointwise (h : ℝ → ℝ) (hh : StrictMono h) (p : ℝ × ℝ) :
    ENNReal.ofReal (Theta h p.1 p.2 ^ 2 / p.2) ≤
      ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
        ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) := by
  rcases le_or_gt p.2 0 with hy | hy
  · rw [ENNReal.ofReal_of_nonpos (div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hy)]
    exact bot_le
  set c : ℕ → ℝ := fun k => betaPt h p.1 (2 ^ k * p.2) with hcdef
  have hc0 : ∀ k, 0 ≤ c k := fun k => thetaC_betaPt_nonneg h _ _
  have hc1 : ∀ k, c k ≤ 1 := fun k => thetaC_betaPt_le_one h hh _ _ (mul_pos (by positivity) hy)
  have hTheta : Theta h p.1 p.2 = ∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k := rfl
  have hterm0 : ∀ k : ℕ, 0 ≤ 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2) :=
    fun k => mul_nonneg (by positivity) (div_nonneg (sq_nonneg _) hy.le)
  have hsumm : Summable fun k : ℕ => 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2) := by
    refine Summable.of_nonneg_of_le hterm0 (fun k => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4) (by norm_num)).mul_left
        (4 / 3 / p.2))
    have hck : c k ^ 2 ≤ 1 := pow_le_one₀ (hc0 k) (hc1 k)
    have hq : 0 ≤ 4 / 3 / p.2 * (1 / 4 : ℝ) ^ k :=
      mul_nonneg (div_nonneg (by norm_num) hy.le) (by positivity)
    calc 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2) = 4 / 3 / p.2 * (1 / 4 : ℝ) ^ k * c k ^ 2 := by
          ring
      _ ≤ 4 / 3 / p.2 * (1 / 4 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left hck hq
      _ = 4 / 3 / p.2 * (1 / 4 : ℝ) ^ k := mul_one _
  have heq : 4 / 3 * (∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2) / p.2 =
      ∑' k : ℕ, 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2) := by
    rw [show 4 / 3 * (∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2) / p.2 =
        4 / 3 / p.2 * ∑' k : ℕ, (1 / 4 : ℝ) ^ k * c k ^ 2 by ring, ← tsum_mul_left]
    exact tsum_congr fun k => by ring
  calc ENNReal.ofReal (Theta h p.1 p.2 ^ 2 / p.2)
      ≤ ENNReal.ofReal (∑' k : ℕ, 4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [← heq, hTheta]
        exact div_le_div_of_nonneg_right (thetaC_sq_tsum_le c hc0 hc1) hy.le
    _ = ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k * (c k ^ 2 / p.2)) :=
        ENNReal.ofReal_tsum_of_nonneg hterm0 hsumm
    _ = ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
          ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) := by
        refine tsum_congr fun k => ?_
        rw [ENNReal.ofReal_mul (by positivity)]

/-- **Minkowski-type reduction** at the `ℝ≥0∞` level: if the box integrals of the dilated
beta-numbers `β_h(·, 2^k ·)` over `Q_J` are bounded by `u_k`, then
`∬_{Q_J} Θ_h² dxdy/y ≤ (4/3) ∑ 4^{-k} u_k`. -/
private lemma thetaC_box_le (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h) (a b : ℝ)
    (u : ℕ → ℝ) (hu0 : ∀ k, 0 ≤ u k) (hus : Summable fun k => (1 / 4 : ℝ) ^ k * u k)
    (hu : ∀ k : ℕ, carlesonBoxLIntegral (fun x y => betaPt h x (2 ^ k * y)) a b ≤
      ENNReal.ofReal (u k)) :
    carlesonBoxLIntegral (Theta h) a b ≤
      ENNReal.ofReal (4 / 3 * ∑' k : ℕ, (1 / 4 : ℝ) ^ k * u k) := by
  have hmk : ∀ k : ℕ, Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) := fun k =>
    (((thetaC_betaPt_dil_measurable h hh hc (2 ^ k)).pow_const 2).div
      measurable_snd).ennreal_ofReal
  have hcu0 : ∀ k : ℕ, 0 ≤ 4 / 3 * (1 / 4 : ℝ) ^ k * u k :=
    fun k => mul_nonneg (by positivity) (hu0 k)
  have hcus : Summable fun k : ℕ => 4 / 3 * (1 / 4 : ℝ) ^ k * u k :=
    (hus.mul_left (4 / 3)).congr fun k => by ring
  calc carlesonBoxLIntegral (Theta h) a b
      ≤ ∫⁻ p in carlesonBox a b, ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
          ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) :=
        lintegral_mono fun p => thetaC_pointwise h hh p
    _ = ∑' k : ℕ, ∫⁻ p in carlesonBox a b, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
          ENNReal.ofReal (betaPt h p.1 (2 ^ k * p.2) ^ 2 / p.2) :=
        lintegral_tsum fun k => ((hmk k).const_mul _).aemeasurable
    _ = ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) *
          carlesonBoxLIntegral (fun x y => betaPt h x (2 ^ k * y)) a b := by
        refine tsum_congr fun k => ?_
        rw [lintegral_const_mul _ (hmk k)]
        rfl
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k) * ENNReal.ofReal (u k) :=
        ENNReal.tsum_le_tsum fun k => mul_le_mul_right (hu k) _
    _ = ∑' k : ℕ, ENNReal.ofReal (4 / 3 * (1 / 4 : ℝ) ^ k * u k) :=
        tsum_congr fun k => (ENNReal.ofReal_mul (by positivity)).symm
    _ = ENNReal.ofReal (∑' k : ℕ, 4 / 3 * (1 / 4 : ℝ) ^ k * u k) :=
        (ENNReal.ofReal_tsum_of_nonneg hcu0 hcus).symm
    _ = ENNReal.ofReal (4 / 3 * ∑' k : ℕ, (1 / 4 : ℝ) ^ k * u k) := by
        rw [← tsum_mul_left]
        exact congrArg ENNReal.ofReal (tsum_congr fun k => by ring)

/-- **Theorem (`Θ_h` Carleson estimate)**: for an increasing, locally
absolutely continuous homeomorphism `h` of `ℝ` with `h' ∈ A_∞(ℝ)` and
`log h' ∈ VMO(ℝ)`, one has `sup_J ‖Θ_h‖_{T²(J)} < ∞` and
`‖Θ_h‖_{T²(J)} → 0` as `|J| → 0`, uniformly in the position of `J`;
that is, `Θ_h² dxdy/y ∈ CM₀(𝕌)`. -/
theorem theta_carleson (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (hsurj : Function.Surjective h)
    (hw : AInfinityWeight (deriv h))
    (hvmo : VMO (fun t => Real.log (deriv h t))) :
    IsVanishingCarleson (Theta h) := by
  have hc : Continuous h := hac.1
  obtain ⟨⟨Cβ, hCβ0, hCβ⟩, hvan⟩ := isVanishingCarleson_betaPt h hh hac hsurj hw hvmo
  have h12 : ∀ k : ℕ, (1 / 2 : ℝ) ^ k = (1 / 4) ^ k * 2 ^ k := fun k => by
    rw [← mul_pow]; norm_num
  have h34 : ∀ k : ℕ, (3 / 4 : ℝ) ^ k = (1 / 4) ^ k * 3 ^ k := fun k => by
    rw [← mul_pow]; norm_num
  have hlen : ∀ (a b : ℝ) (k : ℕ),
      (a + b) / 2 + 2 ^ k * (b - a) / 2 - ((a + b) / 2 - 2 ^ k * (b - a) / 2) =
        2 ^ k * (b - a) := fun a b k => by ring
  -- The head bound combined with part (C) for `β_h`: `∬_{Q_J} β_h(x, 2^k y)² ≤ C_β 2^k |J|`.
  have hhead : ∀ a b : ℝ, a < b → ∀ k : ℕ,
      carlesonBoxLIntegral (fun x y => betaPt h x (2 ^ k * y)) a b ≤
        ENNReal.ofReal (Cβ * (2 ^ k * (b - a))) := by
    intro a b hab k
    have hpos : (0 : ℝ) < 2 ^ k * (b - a) := mul_pos (by positivity) (sub_pos.mpr hab)
    have hJk := hCβ ((a + b) / 2 - 2 ^ k * (b - a) / 2) ((a + b) / 2 + 2 ^ k * (b - a) / 2)
      (by linarith)
    rw [hlen] at hJk
    exact (thetaC_head h hh hc a b hab k).trans hJk
  refine ⟨⟨8 / 3 * Cβ, mul_nonneg (by norm_num) hCβ0, fun a b hab => ?_⟩, fun ε hε => ?_⟩
  · -- Carleson boundedness: `∑ 4^{-k} C_β 2^k |J| = 2 C_β |J|`.
    have hL : 0 < b - a := sub_pos.mpr hab
    have hgeom : ∀ k : ℕ, (1 / 4 : ℝ) ^ k * (Cβ * (2 ^ k * (b - a))) =
        Cβ * (b - a) * (1 / 2) ^ k := fun k => by rw [h12]; ring
    have hsum : Summable fun k : ℕ => (1 / 4 : ℝ) ^ k * (Cβ * (2 ^ k * (b - a))) :=
      (summable_geometric_two.mul_left (Cβ * (b - a))).congr fun k => (hgeom k).symm
    refine (thetaC_box_le h hh hc a b _
      (fun k => mul_nonneg hCβ0 (mul_nonneg (by positivity) hL.le)) hsum
      (hhead a b hab)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [tsum_congr hgeom, tsum_mul_left, tsum_geometric_two]
    ring
  · -- Vanishing: the scales `k < K` use part (V) at `J_k`, the scales `k ≥ K` part (C).
    have h16 : (0 : ℝ) < 16 * (Cβ + 1) := by linarith
    obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hε h16)
      (show (2 / 3 : ℝ) < 1 by norm_num)
    obtain ⟨δ', hδ'pos, hδ'⟩ := hvan (ε / 4) (by linarith)
    have h2K : (0 : ℝ) < 2 ^ K := by positivity
    refine ⟨δ' / 2 ^ K, div_pos hδ'pos h2K, fun a b hab hlenδ => ?_⟩
    have hL : 0 < b - a := sub_pos.mpr hab
    have hLK : (b - a) * 2 ^ K ≤ δ' := (le_div_iff₀ h2K).mp hlenδ
    set u : ℕ → ℝ := fun k => ε / 4 * (2 ^ k * (b - a)) + Cβ * (2 / 3) ^ K * 3 ^ k * (b - a)
      with hudef
    have hA0 : ∀ k : ℕ, 0 ≤ ε / 4 * (2 ^ k * (b - a)) :=
      fun k => mul_nonneg (by linarith) (mul_nonneg (by positivity) hL.le)
    have hB0 : ∀ k : ℕ, 0 ≤ Cβ * (2 / 3) ^ K * 3 ^ k * (b - a) :=
      fun k => mul_nonneg (mul_nonneg (mul_nonneg hCβ0 (by positivity)) (by positivity)) hL.le
    have hu0 : ∀ k, 0 ≤ u k := fun k => add_nonneg (hA0 k) (hB0 k)
    have hwu : ∀ k : ℕ, (1 / 4 : ℝ) ^ k * u k =
        ε / 4 * (b - a) * (1 / 2) ^ k + Cβ * (2 / 3) ^ K * (b - a) * (3 / 4) ^ k := fun k => by
      rw [h12, h34]
      simp only [hudef]
      ring
    have hs1 := summable_geometric_two.mul_left (ε / 4 * (b - a))
    have hs2 := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3 / 4)
      (by norm_num)).mul_left (Cβ * (2 / 3) ^ K * (b - a))
    have hsum : Summable fun k => (1 / 4 : ℝ) ^ k * u k :=
      (hs1.add hs2).congr fun k => (hwu k).symm
    have htsum : ∑' k : ℕ, (1 / 4 : ℝ) ^ k * u k =
        ε / 4 * (b - a) * 2 + Cβ * (2 / 3) ^ K * (b - a) * 4 := by
      rw [tsum_congr hwu, hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left, tsum_geometric_two,
        tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 3 / 4) (by norm_num)]
      norm_num
    have hbound : ∀ k : ℕ, carlesonBoxLIntegral (fun x y => betaPt h x (2 ^ k * y)) a b ≤
        ENNReal.ofReal (u k) := by
      intro k
      rcases lt_or_ge k K with hkK | hkK
      · have hpos : (0 : ℝ) < 2 ^ k * (b - a) := mul_pos (by positivity) hL
        have hkle : (2 : ℝ) ^ k * (b - a) ≤ δ' := by
          have h2k : (2 : ℝ) ^ k ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hkK.le
          have := mul_le_mul_of_nonneg_right h2k hL.le
          linarith
        have hJk := hδ' ((a + b) / 2 - 2 ^ k * (b - a) / 2) ((a + b) / 2 + 2 ^ k * (b - a) / 2)
          (by linarith) (by rw [hlen]; exact hkle)
        rw [hlen] at hJk
        refine (thetaC_head h hh hc a b hab k).trans (hJk.trans (ENNReal.ofReal_le_ofReal ?_))
        simp only [hudef]
        linarith [hB0 k]
      · refine (hhead a b hab k).trans (ENNReal.ofReal_le_ofReal ?_)
        have h23 : (2 : ℝ) ^ k ≤ (2 / 3) ^ K * 3 ^ k := by
          have hle : (2 / 3 : ℝ) ^ k ≤ (2 / 3) ^ K :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) hkK
          calc (2 : ℝ) ^ k = (2 / 3) ^ k * 3 ^ k := by rw [← mul_pow]; norm_num
            _ ≤ (2 / 3) ^ K * 3 ^ k := mul_le_mul_of_nonneg_right hle (by positivity)
        have hCk := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h23 hL.le) hCβ0
        simp only [hudef]
        linarith [hA0 k]
    refine (thetaC_box_le h hh hc a b u hu0 hsum hbound).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [htsum]
    have hK' : 16 * Cβ * (2 / 3) ^ K ≤ ε := by
      have h1 := (lt_div_iff₀ h16).mp hK
      have hp : (0 : ℝ) ≤ (2 / 3) ^ K := by positivity
      linarith
    have := mul_le_mul_of_nonneg_right hK' hL.le
    linarith

/-- **Bridge theorem (§2.2)**: strong symmetry forces quasisymmetry — if
`f ∈ SS(ℝ)` then `f' ∈ A_∞` makes `f` strongly quasisymmetric, in particular
`ρ`-quasisymmetric for some `ρ ≥ 1`. (This is the missing link between the
hypothesis of the main theorem and the `Quasisymmetric` hypothesis of
`forward_to_theta` / the forward inequality.) -/
theorem ss_imp_quasisymmetric (f : ℝ → ℝ) (hf : StronglySymmetric f) :
    ∃ ρ : ℝ, 1 ≤ ρ ∧ Quasisymmetric f ρ :=
  ainfty_imp_quasisymmetric f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1

/-- **Theorem 1 (Main theorem)**: for every `f ∈ SS(ℝ)`, the complex
dilatation `μ_{e(f)}` of the barycentric extension `e(f) : 𝕌 → 𝕌` satisfies
`μ_{e(f)} ∈ ℳ₀(𝕌) = M(𝕌) ∩ 𝓛₀(𝕌)`:

* `|μ_{e(f)}(z)|² dxdy/y` is a vanishing Carleson measure on `𝕌`;
* `‖μ_{e(f)}‖_∞ < 1`, in the form of a *uniform* bound `‖μ_{e(f)}(z)‖ ≤ k < 1`;
* `μ_{e(f)}` is continuous on `𝕌`, in particular measurable.

`complexDilatation (douadyEarle f)` is the genuine dilatation on `𝕌`: `e(f)`
is differentiable there with `∂e(f) ≠ 0` (`differentiableAt_douadyEarle`,
`wirtZ_douadyEarle_ne_zero`). -/
theorem main_theorem (f : ℝ → ℝ) (hf : StronglySymmetric f) :
    IsVanishingCarleson
        (fun x y => ‖complexDilatation (douadyEarle f) (x + y * Complex.I)‖) ∧
      (∃ k : ℝ, k < 1 ∧ ∀ z : ℂ, 0 < z.im →
        ‖complexDilatation (douadyEarle f) z‖ ≤ k) ∧
      ContinuousOn (complexDilatation (douadyEarle f)) {z : ℂ | 0 < z.im} := by
  obtain ⟨ρ, hρ, hqs⟩ := ss_imp_quasisymmetric f hf
  obtain ⟨C, hC, hfwd⟩ := forward_to_theta ρ hρ
  refine ⟨isVanishingCarleson_of_le _ (Theta f) C hC.le (fun x y hy => ?_)
      (theta_carleson f hf.1 hf.2.2.1 hf.2.1 hf.2.2.2.1 hf.2.2.2.2),
    ss_dilatation_sup_lt_one f hf,
    continuousOn_complexDilatation_douadyEarle f hf.1 hf.2.2.1.1 hf.2.1⟩
  exact (abs_of_nonneg (norm_nonneg _)).trans_le (hfwd f hqs x y hy)

end VanishingCarleson

end
