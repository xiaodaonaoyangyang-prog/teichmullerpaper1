/-
# Beta-numbers and the affine deviation (Section 5)

Definitions of the beta-numbers `β_h`, the scale average `Θ_h`, the `L²`
orthogonal projection onto affine functions, and the statements of:

* Remark 5.2 (attainment, continuity of `β_h`)  — `beta_attained`, `continuous_betaPt`
* Lemma (Denominator Lower Bounds for `L²` Projection) — `denominator_lower_bounds`
* Lemma (Affine Growth on Concentric Intervals)        — `affine_growth`
* Lemma (Crude Beta Bound)                             — `crude_beta_bound`
* Lemma (`L²`–`L¹` Comparison)                          — `l2_l1_comparison`
* Lemma (Telescoping Decomposition)                    — `telescoping_decomposition`
* Proposition (Forward Inequality to Beta Deviation)   — `forward_to_theta`
-/
import Mathlib
import VanishingCarleson.ForwardInequality

open MeasureTheory Real Set

noncomputable section

namespace VanishingCarleson

/-! ## Definitions (Section 5.1) -/

/-- **Definition (Beta-number)**: for an interval `I = [a, b]`,
`β_h(I) = inf_A (|I| |h(I)|)⁻¹ ∫_I |h - A| dt` over all real affine maps. -/
def beta (h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sInf { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
    r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| }

/-- Point form: `β_h(x, y) = β_h([x - y, x + y])`. -/
def betaPt (h : ℝ → ℝ) (x y : ℝ) : ℝ := beta h (x - y) (x + y)

/-- **Definition (Affine deviation)**: `Θ_h(x, y) = ∑_{k≥0} 4^{-k} β_h(x, 2^k y)`. -/
def Theta (h : ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∑' k : ℕ, (1 / 4 : ℝ) ^ k * betaPt h x (2 ^ k * y)

/-- **Remark 5.2 (attainment)**: the infimum defining `β_h(I)` is attained by
some affine map `A(t) = κt + τ`. (Together with `l2_l1_comparison`, which
takes the optimizer as a hypothesis, this licenses reasoning about *the*
optimal affine approximation.) -/
theorem beta_attained (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (a b : ℝ) (hab : a < b) :
    ∃ κ τ : ℝ, ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| =
      beta h a b := by
  have hb0 : (b - a : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hdh : (0 : ℝ) < h b - h a := sub_pos.mpr (hh hab)
  have hM : (0 : ℝ) < (b - a) * (h b - h a) := mul_pos (sub_pos.mpr hab) hdh
  set F : ℝ × ℝ → ℝ := fun p =>
    ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (p.1 * t + p.2)| with hFdef
  -- Continuity
  have hFcont : Continuous F := by
    apply Continuous.mul continuous_const
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    fun_prop
  -- The coercivity estimate: `∫ |κt+τ| dt ≥ (|κ|+|τ|)/K` for a constant `K > 0`.
  have hba : (0:ℝ) < b - a := sub_pos.mpr hab
  set X : ℝ := (a + b) / 2 with hXdef
  set K : ℝ := (6 * (1 + |X|) + (b - a)) / (b - a) ^ 2 with hKdef
  have hKpos : (0 : ℝ) < K := by positivity
  have hcoer : ∀ κ τ : ℝ, (|κ| + |τ|) / K ≤ ∫ t in a..b, |κ * t + τ| := by
    intro κ τ
    have hid : IntervalIntegrable (fun t : ℝ => t) volume a b :=
      continuous_id'.intervalIntegrable _ _
    have hA_int : IntervalIntegrable (fun t : ℝ => κ * t + τ) volume a b :=
      ((continuous_const.mul continuous_id').add continuous_const).intervalIntegrable _ _
    set J' : ℝ := ∫ t in a..b, |κ * t + τ| with hJ'def
    have hJ'nn : (0:ℝ) ≤ J' := intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _)
    have HA : ∫ s in a..b, (κ * s + τ) = (b - a) * (κ * X + τ) := by
      have hk : IntervalIntegrable (fun s : ℝ => κ * s) volume a b :=
        (continuous_const.mul continuous_id').intervalIntegrable _ _
      rw [intervalIntegral.integral_add hk intervalIntegrable_const,
        intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
        smul_eq_mul, hXdef]
      ring
    have hsc_cont : ContinuousOn (fun s : ℝ => s - X) (Set.uIcc a b) :=
      (continuous_id'.sub continuous_const).continuousOn
    have hAw_int : IntervalIntegrable (fun s : ℝ => (κ * s + τ) * (s - X)) volume a b :=
      hA_int.mul_continuousOn hsc_cont
    have Hxc : ∫ t in a..b, (t - X) = 0 := by
      rw [intervalIntegral.integral_sub hid intervalIntegrable_const, integral_id,
        intervalIntegral.integral_const, smul_eq_mul, hXdef]
      ring
    have Hsq : ∫ t in a..b, (t - X) ^ 2 = (b - a) ^ 3 / 12 := by
      have hExp : (fun t : ℝ => (t - X) ^ 2) =
          fun t => t ^ 2 - 2 * X * t + X ^ 2 := by funext t; ring
      have hsq_int : IntervalIntegrable (fun t : ℝ => t ^ 2) volume a b :=
        (continuous_id'.pow 2).intervalIntegrable _ _
      have hlin_int : IntervalIntegrable (fun t : ℝ => 2 * X * t) volume a b :=
        (continuous_const.mul continuous_id').intervalIntegrable _ _
      rw [hExp, intervalIntegral.integral_add (hsq_int.sub hlin_int) intervalIntegrable_const,
        intervalIntegral.integral_sub hsq_int hlin_int, integral_pow,
        intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
        smul_eq_mul, hXdef]
      ring
    have HB : ∫ s in a..b, (κ * s + τ) * (s - X) = κ * ((b - a) ^ 3 / 12) := by
      have hExp : (fun s : ℝ => (κ * s + τ) * (s - X)) =
          fun s => κ * (s - X) ^ 2 + (κ * X + τ) * (s - X) := by funext s; ring
      have hp1 : IntervalIntegrable (fun s : ℝ => κ * (s - X) ^ 2) volume a b :=
        (((continuous_id'.sub continuous_const).pow 2).const_mul κ).intervalIntegrable _ _
      have hp2 : IntervalIntegrable (fun s : ℝ => (κ * X + τ) * (s - X)) volume a b :=
        ((continuous_id'.sub continuous_const).const_mul _).intervalIntegrable _ _
      rw [hExp, intervalIntegral.integral_add hp1 hp2, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, Hsq, Hxc]
      ring
    -- Ineq 1: `(b-a) |κX+τ| ≤ J'`
    have hIneq1 : (b - a) * |κ * X + τ| ≤ J' := by
      have := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := fun s => κ * s + τ) hab.le
      rw [HA, abs_mul, abs_of_pos (sub_pos.mpr hab)] at this
      exact this
    -- Ineq 2: `|κ| (b-a)^3 / 12 ≤ ((b-a)/2) * J'`
    have hIneq2 : |κ| * (b - a) ^ 3 / 12 ≤ (b - a) / 2 * J' := by
      have h1 := intervalIntegral.abs_integral_le_integral_abs
        (μ := volume) (f := fun s => (κ * s + τ) * (s - X)) hab.le
      rw [HB, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (b - a) ^ 3 / 12)] at h1
      have h2 : ∫ s in a..b, |(κ * s + τ) * (s - X)| ≤ (b - a) / 2 * J' := by
        calc ∫ s in a..b, |(κ * s + τ) * (s - X)|
            ≤ ∫ s in a..b, |κ * s + τ| * ((b - a) / 2) := by
              apply intervalIntegral.integral_mono_on hab.le
                (hAw_int.abs) (hA_int.abs.mul_const _)
              intro s hs
              rw [abs_mul]
              have hsc : |s - X| ≤ (b - a) / 2 := by
                rw [abs_le, hXdef]; constructor <;> linarith [hs.1, hs.2]
              exact mul_le_mul_of_nonneg_left hsc (abs_nonneg _)
          _ = (b - a) / 2 * J' := by rw [intervalIntegral.integral_mul_const]; ring
      calc |κ| * (b - a) ^ 3 / 12 = |κ| * ((b - a) ^ 3 / 12) := by ring
        _ ≤ ∫ s in a..b, |(κ * s + τ) * (s - X)| := h1
        _ ≤ (b - a) / 2 * J' := h2
    -- Clear denominators: `(b-a)^2 |κ| ≤ 6 J'` and `(b-a)^2 |κX+τ| ≤ (b-a) J'`.
    have hκ' : (b - a) ^ 2 * |κ| ≤ 6 * J' := by
      have h12 : |κ| * (b - a) ^ 3 ≤ 6 * ((b - a) * J') := by nlinarith [hIneq2]
      have h12' : (b - a) * ((b - a) ^ 2 * |κ|) ≤ (b - a) * (6 * J') := by nlinarith [h12]
      exact le_of_mul_le_mul_left (by nlinarith [h12']) hba
    have hc' : (b - a) ^ 2 * |κ * X + τ| ≤ (b - a) * J' := by
      have h1 : (b - a) * ((b - a) * |κ * X + τ|) ≤ (b - a) * J' := by nlinarith [hIneq1]
      nlinarith [h1]
    have hτ' : |τ| ≤ |κ * X + τ| + |κ| * |X| := by
      have e : τ = (κ * X + τ) + (-(κ * X)) := by ring
      calc |τ| = |(κ * X + τ) + (-(κ * X))| := by rw [← e]
        _ ≤ |κ * X + τ| + |-(κ * X)| := abs_add_le _ _
        _ = |κ * X + τ| + |κ| * |X| := by rw [abs_neg, abs_mul]
    have hτ'' : (b - a) ^ 2 * |τ| ≤ (b - a) * J' + 6 * J' * |X| := by
      have hXnn : (0:ℝ) ≤ |X| := abs_nonneg _
      calc (b - a) ^ 2 * |τ| ≤ (b - a) ^ 2 * (|κ * X + τ| + |κ| * |X|) :=
            mul_le_mul_of_nonneg_left hτ' (by positivity)
        _ = (b - a) ^ 2 * |κ * X + τ| + ((b - a) ^ 2 * |κ|) * |X| := by ring
        _ ≤ (b - a) * J' + (6 * J') * |X| := by gcongr
        _ = (b - a) * J' + 6 * J' * |X| := by ring
    have hfinal : (b - a) ^ 2 * (|κ| + |τ|) ≤ J' * (6 * (1 + |X|) + (b - a)) := by
      nlinarith [hκ', hτ'']
    have hKeq : K * (b - a) ^ 2 = 6 * (1 + |X|) + (b - a) := by
      rw [hKdef]; field_simp
    have hgoal2 : (b - a) ^ 2 * (|κ| + |τ|) ≤ (b - a) ^ 2 * (J' * K) := by
      rw [show (b - a) ^ 2 * (J' * K) = J' * (K * (b - a) ^ 2) by ring, hKeq]
      exact hfinal
    have hgoal3 : |κ| + |τ| ≤ J' * K :=
      le_of_mul_le_mul_left hgoal2 (by positivity : (0:ℝ) < (b - a) ^ 2)
    rw [div_le_iff₀ hKpos]
    exact hgoal3
  -- The reverse triangle inequality, integrated: `∫|A| - ∫|h| ≤ ∫|h - A|`.
  have hMint : IntervalIntegrable (fun t => |h t|) volume a b :=
    hc.abs.intervalIntegrable _ _
  set M : ℝ := ∫ t in a..b, |h t| with hMdef
  have hMnn : (0:ℝ) ≤ M := intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _)
  have hRev : ∀ κ τ : ℝ,
      (∫ t in a..b, |κ * t + τ|) - M ≤ ∫ t in a..b, |h t - (κ * t + τ)| := by
    intro κ τ
    have hAint : IntervalIntegrable (fun t : ℝ => κ * t + τ) volume a b :=
      ((continuous_const.mul continuous_id').add continuous_const).intervalIntegrable _ _
    have hfint : IntervalIntegrable (fun t : ℝ => h t - (κ * t + τ)) volume a b :=
      (hh.monotone.intervalIntegrable).sub hAint
    have hptw : ∀ t ∈ Set.Icc a b, |κ * t + τ| - |h t| ≤ |h t - (κ * t + τ)| := by
      intro t _
      have h1 := abs_sub_abs_le_abs_sub (κ * t + τ) (h t)
      rwa [abs_sub_comm (κ * t + τ) (h t)] at h1
    calc (∫ t in a..b, |κ * t + τ|) - M
        = (∫ t in a..b, |κ * t + τ|) - ∫ t in a..b, |h t| := by rw [hMdef]
      _ = ∫ t in a..b, (|κ * t + τ| - |h t|) := (intervalIntegral.integral_sub hAint.abs hMint).symm
      _ ≤ ∫ t in a..b, |h t - (κ * t + τ)| := by
          apply intervalIntegral.integral_mono_on hab.le (hAint.abs.sub hMint) hfint.abs
          exact hptw
  -- Combine: `F p ≥ D * ‖p‖ - E` for fixed constants `D > 0`, `E ≥ 0`.
  set D : ℝ := ((b - a) * (h b - h a))⁻¹ / K with hDdef
  set E : ℝ := ((b - a) * (h b - h a))⁻¹ * M with hEdef
  have hDpos : (0:ℝ) < D := by rw [hDdef]; positivity
  have hnormle : ∀ p : ℝ × ℝ, ‖p‖ ≤ |p.1| + |p.2| := by
    intro p
    simp only [Prod.norm_def, Real.norm_eq_abs]
    exact max_le (by linarith [abs_nonneg p.2]) (by linarith [abs_nonneg p.1])
  have hcoercive : ∀ p : ℝ × ℝ, D * ‖p‖ - E ≤ F p := by
    intro p
    have hinv : (0:ℝ) < ((b - a) * (h b - h a))⁻¹ := inv_pos.mpr hM
    have step1 : (|p.1| + |p.2|) / K - M ≤ ∫ t in a..b, |h t - (p.1 * t + p.2)| :=
      le_trans (by linarith [hcoer p.1 p.2]) (hRev p.1 p.2)
    have step2 : D * ‖p‖ - E ≤ ((b - a) * (h b - h a))⁻¹ * ((|p.1| + |p.2|) / K - M) := by
      have h1 : D * ‖p‖ ≤ ((b - a) * (h b - h a))⁻¹ * ((|p.1| + |p.2|) / K) := by
        have e1 : D * ‖p‖ = ((b - a) * (h b - h a))⁻¹ * (‖p‖ / K) := by rw [hDdef]; ring
        rw [e1]
        gcongr
        exact hnormle p
      have h2 : ((b - a) * (h b - h a))⁻¹ * ((|p.1| + |p.2|) / K - M) =
          ((b - a) * (h b - h a))⁻¹ * ((|p.1| + |p.2|) / K) - E := by
        rw [hEdef]; ring
      linarith [h1, h2]
    calc D * ‖p‖ - E ≤ ((b - a) * (h b - h a))⁻¹ * ((|p.1| + |p.2|) / K - M) := step2
      _ ≤ ((b - a) * (h b - h a))⁻¹ * (∫ t in a..b, |h t - (p.1 * t + p.2)|) :=
          mul_le_mul_of_nonneg_left step1 hinv.le
      _ = F p := by rw [hFdef]
  -- Coercivity of `F` at infinity, and existence of a global minimizer.
  have htendsto : Filter.Tendsto (fun p : ℝ × ℝ => D * ‖p‖ + (-E)) (Bornology.cobounded (ℝ × ℝ))
      Filter.atTop :=
    (tendsto_norm_cobounded_atTop (E := ℝ × ℝ)).const_mul_atTop hDpos
      |>.atTop_add tendsto_const_nhds
  have htendsto' : Filter.Tendsto F (Bornology.cobounded (ℝ × ℝ)) Filter.atTop :=
    Filter.tendsto_atTop_mono (fun p => by simpa [sub_eq_add_neg] using hcoercive p) htendsto
  have htendsto'' : Filter.Tendsto F (Filter.cocompact (ℝ × ℝ)) Filter.atTop := by
    rwa [Metric.cobounded_eq_cocompact] at htendsto'
  obtain ⟨p₀, hp₀⟩ := hFcont.exists_forall_le htendsto''
  -- `F p₀` realises the infimum defining `β_h(I)`.
  have hSdef : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
      r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| } = Set.range F := by
    ext r
    constructor
    · rintro ⟨κ, τ, -, rfl⟩
      exact ⟨(κ, τ), rfl⟩
    · rintro ⟨⟨κ, τ⟩, rfl⟩
      refine ⟨κ, τ, ?_, rfl⟩
      rw [hFdef]
      exact mul_nonneg (inv_pos.mpr hM).le
        (intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _))
  have hIsLeast : IsLeast (Set.range F) (F p₀) := ⟨⟨p₀, rfl⟩, fun r ⟨q, hq⟩ => hq ▸ hp₀ q⟩
  refine ⟨p₀.1, p₀.2, ?_⟩
  rw [beta, hSdef, hIsLeast.csInf_eq]

/-! ## Auxiliary material for `continuous_betaPt` -/

/-- The coercivity estimate on affine functions used in `beta_attained`, extracted as a
standalone fact about `[a, b]` alone (no dependence on `h`). -/
private lemma affine_coercive (a b : ℝ) (hab : a < b) (κ τ : ℝ) :
    (|κ| + |τ|) / ((6 * (1 + |(a + b) / 2|) + (b - a)) / (b - a) ^ 2) ≤
      ∫ t in a..b, |κ * t + τ| := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  set X : ℝ := (a + b) / 2 with hXdef
  set K : ℝ := (6 * (1 + |X|) + (b - a)) / (b - a) ^ 2 with hKdef
  have hKpos : (0 : ℝ) < K := by positivity
  have hid : IntervalIntegrable (fun t : ℝ => t) volume a b :=
    continuous_id'.intervalIntegrable _ _
  have hA_int : IntervalIntegrable (fun t : ℝ => κ * t + τ) volume a b :=
    ((continuous_const.mul continuous_id').add continuous_const).intervalIntegrable _ _
  set J' : ℝ := ∫ t in a..b, |κ * t + τ| with hJ'def
  have hJ'nn : (0 : ℝ) ≤ J' := intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _)
  have HA : ∫ s in a..b, (κ * s + τ) = (b - a) * (κ * X + τ) := by
    have hk : IntervalIntegrable (fun s : ℝ => κ * s) volume a b :=
      (continuous_const.mul continuous_id').intervalIntegrable _ _
    rw [intervalIntegral.integral_add hk intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
      smul_eq_mul, hXdef]
    ring
  have hsc_cont : ContinuousOn (fun s : ℝ => s - X) (Set.uIcc a b) :=
    (continuous_id'.sub continuous_const).continuousOn
  have hAw_int : IntervalIntegrable (fun s : ℝ => (κ * s + τ) * (s - X)) volume a b :=
    hA_int.mul_continuousOn hsc_cont
  have Hxc : ∫ t in a..b, (t - X) = 0 := by
    rw [intervalIntegral.integral_sub hid intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const, smul_eq_mul, hXdef]
    ring
  have Hsq : ∫ t in a..b, (t - X) ^ 2 = (b - a) ^ 3 / 12 := by
    have hExp : (fun t : ℝ => (t - X) ^ 2) =
        fun t => t ^ 2 - 2 * X * t + X ^ 2 := by funext t; ring
    have hsq_int : IntervalIntegrable (fun t : ℝ => t ^ 2) volume a b :=
      (continuous_id'.pow 2).intervalIntegrable _ _
    have hlin_int : IntervalIntegrable (fun t : ℝ => 2 * X * t) volume a b :=
      (continuous_const.mul continuous_id').intervalIntegrable _ _
    rw [hExp, intervalIntegral.integral_add (hsq_int.sub hlin_int) intervalIntegrable_const,
      intervalIntegral.integral_sub hsq_int hlin_int, integral_pow,
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
      smul_eq_mul, hXdef]
    ring
  have HB : ∫ s in a..b, (κ * s + τ) * (s - X) = κ * ((b - a) ^ 3 / 12) := by
    have hExp : (fun s : ℝ => (κ * s + τ) * (s - X)) =
        fun s => κ * (s - X) ^ 2 + (κ * X + τ) * (s - X) := by funext s; ring
    have hp1 : IntervalIntegrable (fun s : ℝ => κ * (s - X) ^ 2) volume a b :=
      (((continuous_id'.sub continuous_const).pow 2).const_mul κ).intervalIntegrable _ _
    have hp2 : IntervalIntegrable (fun s : ℝ => (κ * X + τ) * (s - X)) volume a b :=
      ((continuous_id'.sub continuous_const).const_mul _).intervalIntegrable _ _
    rw [hExp, intervalIntegral.integral_add hp1 hp2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, Hsq, Hxc]
    ring
  have hIneq1 : (b - a) * |κ * X + τ| ≤ J' := by
    have := intervalIntegral.abs_integral_le_integral_abs (μ := volume) (f := fun s => κ * s + τ) hab.le
    rw [HA, abs_mul, abs_of_pos (sub_pos.mpr hab)] at this
    exact this
  have hIneq2 : |κ| * (b - a) ^ 3 / 12 ≤ (b - a) / 2 * J' := by
    have h1 := intervalIntegral.abs_integral_le_integral_abs
      (μ := volume) (f := fun s => (κ * s + τ) * (s - X)) hab.le
    rw [HB, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (b - a) ^ 3 / 12)] at h1
    have h2 : ∫ s in a..b, |(κ * s + τ) * (s - X)| ≤ (b - a) / 2 * J' := by
      calc ∫ s in a..b, |(κ * s + τ) * (s - X)|
          ≤ ∫ s in a..b, |κ * s + τ| * ((b - a) / 2) := by
            apply intervalIntegral.integral_mono_on hab.le
              (hAw_int.abs) (hA_int.abs.mul_const _)
            intro s hs
            rw [abs_mul]
            have hsc : |s - X| ≤ (b - a) / 2 := by
              rw [abs_le, hXdef]; constructor <;> linarith [hs.1, hs.2]
            exact mul_le_mul_of_nonneg_left hsc (abs_nonneg _)
        _ = (b - a) / 2 * J' := by rw [intervalIntegral.integral_mul_const]; ring
    calc |κ| * (b - a) ^ 3 / 12 = |κ| * ((b - a) ^ 3 / 12) := by ring
      _ ≤ ∫ s in a..b, |(κ * s + τ) * (s - X)| := h1
      _ ≤ (b - a) / 2 * J' := h2
  have hκ' : (b - a) ^ 2 * |κ| ≤ 6 * J' := by
    have h12 : |κ| * (b - a) ^ 3 ≤ 6 * ((b - a) * J') := by nlinarith [hIneq2]
    have h12' : (b - a) * ((b - a) ^ 2 * |κ|) ≤ (b - a) * (6 * J') := by nlinarith [h12]
    exact le_of_mul_le_mul_left (by nlinarith [h12']) hba
  have hc' : (b - a) ^ 2 * |κ * X + τ| ≤ (b - a) * J' := by
    have h1 : (b - a) * ((b - a) * |κ * X + τ|) ≤ (b - a) * J' := by nlinarith [hIneq1]
    nlinarith [h1]
  have hτ' : |τ| ≤ |κ * X + τ| + |κ| * |X| := by
    have e : τ = (κ * X + τ) + (-(κ * X)) := by ring
    calc |τ| = |(κ * X + τ) + (-(κ * X))| := by rw [← e]
      _ ≤ |κ * X + τ| + |-(κ * X)| := abs_add_le _ _
      _ = |κ * X + τ| + |κ| * |X| := by rw [abs_neg, abs_mul]
  have hτ'' : (b - a) ^ 2 * |τ| ≤ (b - a) * J' + 6 * J' * |X| := by
    have hXnn : (0:ℝ) ≤ |X| := abs_nonneg _
    calc (b - a) ^ 2 * |τ| ≤ (b - a) ^ 2 * (|κ * X + τ| + |κ| * |X|) :=
          mul_le_mul_of_nonneg_left hτ' (by positivity)
      _ = (b - a) ^ 2 * |κ * X + τ| + ((b - a) ^ 2 * |κ|) * |X| := by ring
      _ ≤ (b - a) * J' + (6 * J') * |X| := by gcongr
      _ = (b - a) * J' + 6 * J' * |X| := by ring
  have hfinal : (b - a) ^ 2 * (|κ| + |τ|) ≤ J' * (6 * (1 + |X|) + (b - a)) := by
    nlinarith [hκ', hτ'']
  have hKeq : K * (b - a) ^ 2 = 6 * (1 + |X|) + (b - a) := by
    rw [hKdef]; field_simp
  have hgoal2 : (b - a) ^ 2 * (|κ| + |τ|) ≤ (b - a) ^ 2 * (J' * K) := by
    rw [show (b - a) ^ 2 * (J' * K) = J' * (K * (b - a) ^ 2) by ring, hKeq]
    exact hfinal
  have hgoal3 : |κ| + |τ| ≤ J' * K :=
    le_of_mul_le_mul_left hgoal2 (by positivity : (0:ℝ) < (b - a) ^ 2)
  rw [div_le_iff₀ hKpos]
  exact hgoal3

/-- The reverse-triangle-inequality estimate from `beta_attained`, extracted as a standalone
fact: replacing `h` by an affine map can only decrease the `L¹` deviation by at most `∫|h|`. -/
private lemma affine_reverse_triangle (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (a b : ℝ) (hab : a < b) (κ τ : ℝ) :
    (∫ t in a..b, |κ * t + τ|) - (∫ t in a..b, |h t|) ≤ ∫ t in a..b, |h t - (κ * t + τ)| := by
  have hAint : IntervalIntegrable (fun t : ℝ => κ * t + τ) volume a b :=
    ((continuous_const.mul continuous_id').add continuous_const).intervalIntegrable _ _
  have hMint : IntervalIntegrable (fun t => |h t|) volume a b := hc.abs.intervalIntegrable _ _
  have hfint : IntervalIntegrable (fun t : ℝ => h t - (κ * t + τ)) volume a b :=
    (hh.monotone.intervalIntegrable).sub hAint
  have hptw : ∀ t ∈ Set.Icc a b, |κ * t + τ| - |h t| ≤ |h t - (κ * t + τ)| := by
    intro t _
    have h1 := abs_sub_abs_le_abs_sub (κ * t + τ) (h t)
    rwa [abs_sub_comm (κ * t + τ) (h t)] at h1
  calc (∫ t in a..b, |κ * t + τ|) - ∫ t in a..b, |h t|
      = ∫ t in a..b, (|κ * t + τ| - |h t|) := (intervalIntegral.integral_sub hAint.abs hMint).symm
    _ ≤ ∫ t in a..b, |h t - (κ * t + τ)| := by
        apply intervalIntegral.integral_mono_on hab.le (hAint.abs.sub hMint) hfint.abs
        exact hptw

/-- The quantity minimised in the definition of `beta`, as a function of the affine
coefficients `p = (κ, τ)` alone (`a`, `b`, `h` fixed). -/
private def betaG (h : ℝ → ℝ) (a b : ℝ) (p : ℝ × ℝ) : ℝ :=
  ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (p.1 * t + p.2)|

private lemma betaG_nonneg (h : ℝ → ℝ) (hh : StrictMono h) (a b : ℝ) (hab : a < b)
    (p : ℝ × ℝ) : 0 ≤ betaG h a b p :=
  mul_nonneg (inv_pos.mpr (mul_pos (sub_pos.mpr hab) (sub_pos.mpr (hh hab)))).le
    (intervalIntegral.integral_nonneg hab.le (fun _ _ => abs_nonneg _))

private lemma beta_eq_sInf_range (h : ℝ → ℝ) (hh : StrictMono h) (a b : ℝ) (hab : a < b) :
    beta h a b = sInf (Set.range (betaG h a b)) := by
  have hSdef : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
      r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| } =
      Set.range (betaG h a b) := by
    ext r
    constructor
    · rintro ⟨κ, τ, -, rfl⟩
      exact ⟨(κ, τ), rfl⟩
    · rintro ⟨⟨κ, τ⟩, rfl⟩
      exact ⟨κ, τ, betaG_nonneg h hh a b hab (κ, τ), rfl⟩
  rw [beta, hSdef]

/-- The coercivity bound `D * ‖p‖ - E ≤ betaG h a b p` from `beta_attained`, with explicit
(non-optimal but uniform-enough) constants `D`, `E` given in closed form in `a`, `b`. -/
private lemma betaG_coercive (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (a b : ℝ) (hab : a < b) (p : ℝ × ℝ) :
    ((((b - a) * (h b - h a))⁻¹) / ((6 * (1 + |(a + b) / 2|) + (b - a)) / (b - a) ^ 2)) * ‖p‖ -
        ((b - a) * (h b - h a))⁻¹ * (∫ t in a..b, |h t|) ≤ betaG h a b p := by
  set K : ℝ := (6 * (1 + |(a + b) / 2|) + (b - a)) / (b - a) ^ 2 with hKdef
  have hM : (0 : ℝ) < (b - a) * (h b - h a) := mul_pos (sub_pos.mpr hab) (sub_pos.mpr (hh hab))
  have hinv : (0 : ℝ) < ((b - a) * (h b - h a))⁻¹ := inv_pos.mpr hM
  have hnormle : ‖p‖ ≤ |p.1| + |p.2| := by
    simp only [Prod.norm_def, Real.norm_eq_abs]
    exact max_le (by linarith [abs_nonneg p.2]) (by linarith [abs_nonneg p.1])
  have step1 : (|p.1| + |p.2|) / K - (∫ t in a..b, |h t|) ≤ ∫ t in a..b, |h t - (p.1 * t + p.2)| := by
    have hc1 := affine_coercive a b hab p.1 p.2
    have hc2 := affine_reverse_triangle h hh hc a b hab p.1 p.2
    rw [hKdef]
    linarith [hc1, hc2]
  have step2 : ((((b - a) * (h b - h a))⁻¹) / K) * ‖p‖ -
        ((b - a) * (h b - h a))⁻¹ * (∫ t in a..b, |h t|) ≤
      ((b - a) * (h b - h a))⁻¹ * ((|p.1| + |p.2|) / K - (∫ t in a..b, |h t|)) := by
    have h1 : ((((b - a) * (h b - h a))⁻¹) / K) * ‖p‖ ≤
        ((b - a) * (h b - h a))⁻¹ * ((|p.1| + |p.2|) / K) := by
      have e1 : ((((b - a) * (h b - h a))⁻¹) / K) * ‖p‖ =
          ((b - a) * (h b - h a))⁻¹ * (‖p‖ / K) := by ring
      rw [e1]
      gcongr
    linarith [h1]
  calc ((((b - a) * (h b - h a))⁻¹) / K) * ‖p‖ -
        ((b - a) * (h b - h a))⁻¹ * (∫ t in a..b, |h t|)
      ≤ ((b - a) * (h b - h a))⁻¹ * ((|p.1| + |p.2|) / K - (∫ t in a..b, |h t|)) := step2
    _ ≤ ((b - a) * (h b - h a))⁻¹ * (∫ t in a..b, |h t - (p.1 * t + p.2)|) :=
        mul_le_mul_of_nonneg_left step1 hinv.le
    _ = betaG h a b p := rfl

/-- The interval integral of a fixed continuous function, jointly continuous in both
endpoints (via the splitting identity `∫_a^b = ∫_0^b - ∫_0^a`). -/
private lemma continuous_integral_bounds (g : ℝ → ℝ) (hg : Continuous g) :
    Continuous (fun q : ℝ × ℝ => ∫ t in q.1..q.2, g t) := by
  have hP1 : Continuous (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.2, g t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_ : ℝ × ℝ) (t : ℝ) => g t) (hg.comp continuous_snd) continuous_snd
  have hP2 : Continuous (fun q : ℝ × ℝ => ∫ t in (0:ℝ)..q.1, g t) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (_ : ℝ × ℝ) (t : ℝ) => g t) (hg.comp continuous_snd) continuous_fst
  have heq : (fun q : ℝ × ℝ => ∫ t in q.1..q.2, g t) =
      fun q => (∫ t in (0:ℝ)..q.2, g t) - ∫ t in (0:ℝ)..q.1, g t := by
    funext q
    have e1 : ∫ t in q.1..(0:ℝ), g t = -(∫ t in (0:ℝ)..q.1, g t) :=
      intervalIntegral.integral_symm _ _
    have e2 : (∫ t in q.1..(0:ℝ), g t) + ∫ t in (0:ℝ)..q.2, g t = ∫ t in q.1..q.2, g t :=
      intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable q.1 0) (hg.intervalIntegrable 0 q.2)
    linarith [e1, e2]
  rw [heq]
  exact hP1.sub hP2

/-- The integral of `|h - (κ t + τ)|` over `[a, b]`, jointly continuous in `a, b, κ, τ`. -/
private lemma continuous_integral_bounds_affine (h : ℝ → ℝ) (hc : Continuous h) :
    Continuous (fun z : (ℝ × ℝ) × ℝ × ℝ => ∫ t in z.1.1..z.1.2, |h t - (z.2.1 * t + z.2.2)|) := by
  have hf : Continuous (fun z : (ℝ × ℝ × ℝ) × ℝ => |h z.2 - (z.1.2.1 * z.2 + z.1.2.2)|) := by
    fun_prop
  have hP1 : Continuous (fun z : (ℝ × ℝ) × ℝ × ℝ =>
      ∫ t in (0:ℝ)..z.1.2, |h t - (z.2.1 * t + z.2.2)|) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (w : (ℝ × ℝ) × ℝ × ℝ) (t : ℝ) => |h t - (w.2.1 * t + w.2.2)|)
      (by
        have : Continuous (fun z : ((ℝ × ℝ) × ℝ × ℝ) × ℝ =>
            |h z.2 - (z.1.2.1 * z.2 + z.1.2.2)|) := by fun_prop
        exact this)
      (continuous_fst.snd : Continuous fun z : (ℝ × ℝ) × ℝ × ℝ => z.1.2)
  have hP2 : Continuous (fun z : (ℝ × ℝ) × ℝ × ℝ =>
      ∫ t in (0:ℝ)..z.1.1, |h t - (z.2.1 * t + z.2.2)|) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (w : (ℝ × ℝ) × ℝ × ℝ) (t : ℝ) => |h t - (w.2.1 * t + w.2.2)|)
      (by
        have : Continuous (fun z : ((ℝ × ℝ) × ℝ × ℝ) × ℝ =>
            |h z.2 - (z.1.2.1 * z.2 + z.1.2.2)|) := by fun_prop
        exact this)
      (continuous_fst.fst : Continuous fun z : (ℝ × ℝ) × ℝ × ℝ => z.1.1)
  have heq : (fun z : (ℝ × ℝ) × ℝ × ℝ => ∫ t in z.1.1..z.1.2, |h t - (z.2.1 * t + z.2.2)|) =
      fun z => (∫ t in (0:ℝ)..z.1.2, |h t - (z.2.1 * t + z.2.2)|) -
        ∫ t in (0:ℝ)..z.1.1, |h t - (z.2.1 * t + z.2.2)| := by
    funext z
    set κ := z.2.1
    set τ := z.2.2
    have hgcont : Continuous (fun t : ℝ => |h t - (κ * t + τ)|) := by fun_prop
    have e1 : ∫ t in z.1.1..(0:ℝ), |h t - (κ * t + τ)| = -(∫ t in (0:ℝ)..z.1.1, |h t - (κ * t + τ)|) :=
      intervalIntegral.integral_symm _ _
    have e2 : (∫ t in z.1.1..(0:ℝ), |h t - (κ * t + τ)|) +
        ∫ t in (0:ℝ)..z.1.2, |h t - (κ * t + τ)| = ∫ t in z.1.1..z.1.2, |h t - (κ * t + τ)| :=
      intervalIntegral.integral_add_adjacent_intervals
        (hgcont.intervalIntegrable z.1.1 0) (hgcont.intervalIntegrable 0 z.1.2)
    linarith [e1, e2]
  rw [heq]
  exact hP1.sub hP2

/-- For `b < a`, `beta h a b = 0`: reversing the orientation of the interval makes
`(b - a) * (h b - h a)` positive while `∫ t in a..b, |h - A|` becomes non-positive (it is minus
a non-negative quantity), so every candidate `r` in the defining set of `beta h a b` is `≤ 0`;
combined with the defining constraint `0 ≤ r` this forces the set to be a subset of `{0}`, whose
infimum (whether the set is `∅` or `{0}`) is `0`. -/
private lemma beta_eq_zero_of_gt (h : ℝ → ℝ) (hh : StrictMono h) (a b : ℝ) (hba : b < a) :
    beta h a b = 0 := by
  have hset_sub : { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
      r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| } ⊆ {0} := by
    rintro r ⟨κ, τ, hr0, hreq⟩
    have hprod_pos : (0:ℝ) < (b - a) * (h b - h a) :=
      mul_pos_of_neg_of_neg (by linarith) (sub_neg.mpr (hh hba))
    have hint_le : (∫ t in a..b, |h t - (κ * t + τ)|) ≤ 0 := by
      have hsym : ∫ t in a..b, |h t - (κ * t + τ)| = -∫ t in b..a, |h t - (κ * t + τ)| :=
        intervalIntegral.integral_symm _ _
      have hnn : (0:ℝ) ≤ ∫ t in b..a, |h t - (κ * t + τ)| :=
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

/-- **Continuity of `beta` at an off-diagonal point.** For `a₀ < b₀`, `beta h` is continuous
at `(a₀, b₀)`. The proof restricts the minimisation defining `beta` to a fixed compact ball `K`
of affine coefficients, large enough (by the coercivity bound `betaG_coercive`, uniformised over
a compact box `Ubar` around `(a₀, b₀)`) that the true minimiser (from `beta_attained`) always
lies in `K` for `(a, b)` ranging over `Ubar`; the resulting restricted infimum is a continuous
function of `(a, b)` by `IsCompact.continuous_sInf`, and it agrees with `beta h` throughout the
(open) interior of `Ubar`. -/
private lemma continuousAt_beta (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (a₀ b₀ : ℝ) (hab₀ : a₀ < b₀) :
    ContinuousAt (fun q : ℝ × ℝ => beta h q.1 q.2) (a₀, b₀) := by
  set δ : ℝ := (b₀ - a₀) / 4 with hδdef
  have hδpos : (0:ℝ) < δ := by rw [hδdef]; linarith
  set aC : ℝ → ℝ := fun x => min (max x (a₀ - δ)) (a₀ + δ) with haCdef
  set bC : ℝ → ℝ := fun y => min (max y (b₀ - δ)) (b₀ + δ) with hbCdef
  have haCcont : Continuous aC := (continuous_id.max continuous_const).min continuous_const
  have hbCcont : Continuous bC := (continuous_id.max continuous_const).min continuous_const
  have haCmem : ∀ x, aC x ∈ Set.Icc (a₀ - δ) (a₀ + δ) :=
    fun x => ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩
  have hbCmem : ∀ y, bC y ∈ Set.Icc (b₀ - δ) (b₀ + δ) :=
    fun y => ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩
  have haCid : ∀ x ∈ Set.Icc (a₀ - δ) (a₀ + δ), aC x = x := by
    intro x hx
    show min (max x (a₀ - δ)) (a₀ + δ) = x
    rw [max_eq_left hx.1, min_eq_left hx.2]
  have hbCid : ∀ y ∈ Set.Icc (b₀ - δ) (b₀ + δ), bC y = y := by
    intro y hy
    show min (max y (b₀ - δ)) (b₀ + δ) = y
    rw [max_eq_left hy.1, min_eq_left hy.2]
  set Ubar : Set (ℝ × ℝ) := Set.Icc (a₀ - δ) (a₀ + δ) ×ˢ Set.Icc (b₀ - δ) (b₀ + δ) with hUbardef
  have hUbarCompact : IsCompact Ubar := isCompact_Icc.prod isCompact_Icc
  have hUbarLt : ∀ q ∈ Ubar, q.1 < q.2 := by
    intro q hq
    have h1 : q.1 ≤ a₀ + δ := hq.1.2
    have h2 : b₀ - δ ≤ q.2 := hq.2.1
    have : a₀ + δ < b₀ - δ := by rw [hδdef]; linarith
    linarith
  have hmem₀ : (a₀, b₀) ∈ Ubar :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  -- Uniform bound on the denominator product `(b - a) * (h b - h a)` over `Ubar`.
  set denomFun : ℝ × ℝ → ℝ := fun q => (q.2 - q.1) * (h q.2 - h q.1) with hdenomdef
  have hdenomCont : Continuous denomFun :=
    (continuous_snd.sub continuous_fst).mul ((hc.comp continuous_snd).sub (hc.comp continuous_fst))
  have hdenomPos : ∀ q ∈ Ubar, (0:ℝ) < denomFun q :=
    fun q hq => mul_pos (sub_pos.mpr (hUbarLt q hq)) (sub_pos.mpr (hh (hUbarLt q hq)))
  have hPbdd : BddAbove (denomFun '' Ubar) := (hUbarCompact.image hdenomCont).bddAbove
  set Pmax : ℝ := sSup (denomFun '' Ubar) with hPmaxdef
  have hPle : ∀ q ∈ Ubar, denomFun q ≤ Pmax :=
    fun q hq => le_csSup hPbdd (Set.mem_image_of_mem _ hq)
  have hPpos : (0:ℝ) < Pmax := lt_of_lt_of_le (hdenomPos (a₀, b₀) hmem₀) (hPle (a₀, b₀) hmem₀)
  -- Uniform bound on `Kfun (a, b) = (6 (1 + |X|) + (b - a)) / (b - a)²` over `Ubar`.
  set Kfun : ℝ × ℝ → ℝ := fun q => (6 * (1 + |(q.1 + q.2) / 2|) + (q.2 - q.1)) / (q.2 - q.1) ^ 2
    with hKfundef
  have hKfunPos : ∀ q ∈ Ubar, (0:ℝ) < Kfun q := fun q hq => by
    have : (0:ℝ) < q.2 - q.1 := sub_pos.mpr (hUbarLt q hq)
    rw [hKfundef]; positivity
  have hKfunContOn : ContinuousOn Kfun Ubar := by
    have hnum : Continuous (fun q : ℝ × ℝ => 6 * (1 + |(q.1 + q.2) / 2|) + (q.2 - q.1)) := by
      fun_prop
    have hden : Continuous (fun q : ℝ × ℝ => (q.2 - q.1) ^ 2) := by fun_prop
    exact ContinuousOn.div hnum.continuousOn hden.continuousOn
      (fun q hq => pow_ne_zero 2 (sub_pos.mpr (hUbarLt q hq)).ne')
  have hKbdd : BddAbove (Kfun '' Ubar) := (hUbarCompact.image_of_continuousOn hKfunContOn).bddAbove
  set Kmax : ℝ := sSup (Kfun '' Ubar) with hKmaxdef
  have hKle : ∀ q ∈ Ubar, Kfun q ≤ Kmax := fun q hq => le_csSup hKbdd (Set.mem_image_of_mem _ hq)
  have hKpos : (0:ℝ) < Kmax := lt_of_lt_of_le (hKfunPos (a₀, b₀) hmem₀) (hKle (a₀, b₀) hmem₀)
  -- Uniform lower bound `Dmin` on `Dfun (a, b) := (denomFun (a,b))⁻¹ / Kfun (a, b)`.
  set Dmin : ℝ := (Pmax * Kmax)⁻¹ with hDmindef
  have hDminPos : (0:ℝ) < Dmin := by rw [hDmindef]; positivity
  have hDge : ∀ q ∈ Ubar, Dmin ≤ (denomFun q)⁻¹ / Kfun q := by
    intro q hq
    have h1 : (Pmax)⁻¹ ≤ (denomFun q)⁻¹ := inv_anti₀ (hdenomPos q hq) (hPle q hq)
    have h2 : (Pmax)⁻¹ / Kmax ≤ (denomFun q)⁻¹ / Kmax :=
      div_le_div_of_nonneg_right h1 hKpos.le
    have h3 : (denomFun q)⁻¹ / Kmax ≤ (denomFun q)⁻¹ / Kfun q :=
      div_le_div_of_nonneg_left (inv_pos.mpr (hdenomPos q hq)).le (hKfunPos q hq) (hKle q hq)
    calc Dmin = (Pmax)⁻¹ / Kmax := by rw [hDmindef, mul_inv, div_eq_mul_inv]
      _ ≤ (denomFun q)⁻¹ / Kmax := h2
      _ ≤ (denomFun q)⁻¹ / Kfun q := h3
  -- Uniform bound on `Efun (a, b) := betaG h a b (0, 0) = (denomFun (a,b))⁻¹ * ∫_a^b |h|`.
  set Efun : ℝ × ℝ → ℝ := fun q => (denomFun q)⁻¹ * ∫ t in q.1..q.2, |h t| with hEfundef
  have hIntCont : Continuous (fun q : ℝ × ℝ => ∫ t in q.1..q.2, |h t|) :=
    continuous_integral_bounds (fun t => |h t|) hc.abs
  have hdenomContOn : ContinuousOn (fun q : ℝ × ℝ => (denomFun q)⁻¹) Ubar :=
    hdenomCont.continuousOn.inv₀ (fun q hq => (hdenomPos q hq).ne')
  have hEfunContOn : ContinuousOn Efun Ubar :=
    hdenomContOn.mul hIntCont.continuousOn
  have hEbdd : BddAbove (Efun '' Ubar) := (hUbarCompact.image_of_continuousOn hEfunContOn).bddAbove
  set Emax : ℝ := sSup (Efun '' Ubar) with hEmaxdef
  have hEle : ∀ q ∈ Ubar, Efun q ≤ Emax := fun q hq => le_csSup hEbdd (Set.mem_image_of_mem _ hq)
  have hEnonneg : ∀ q ∈ Ubar, (0:ℝ) ≤ Efun q := fun q hq =>
    mul_nonneg (inv_pos.mpr (hdenomPos q hq)).le
      (intervalIntegral.integral_nonneg (hUbarLt q hq).le (fun _ _ => abs_nonneg _))
  have hEmaxNonneg : (0:ℝ) ≤ Emax := le_trans (hEnonneg (a₀, b₀) hmem₀) (hEle (a₀, b₀) hmem₀)
  -- Uniform coercivity `Dmin * ‖p‖ - Emax ≤ betaG h q.1 q.2 p` on `Ubar`.
  have hbetaGE : ∀ q ∈ Ubar, betaG h q.1 q.2 (0, 0) = Efun q := by
    intro q hq
    have hint_eq : (fun t : ℝ => |h t - ((0:ℝ) * t + 0)|) = fun t => |h t| := by
      funext t; simp
    show ((q.2 - q.1) * (h q.2 - h q.1))⁻¹ * (∫ t in q.1..q.2, |h t - ((0:ℝ) * t + 0)|) = Efun q
    rw [hint_eq]
  have huniformCoercive : ∀ q ∈ Ubar, ∀ p : ℝ × ℝ, Dmin * ‖p‖ - Emax ≤ betaG h q.1 q.2 p := by
    intro q hq p
    have hbase := betaG_coercive h hh hc q.1 q.2 (hUbarLt q hq) p
    have heqK : (6 * (1 + |(q.1 + q.2) / 2|) + (q.2 - q.1)) / (q.2 - q.1) ^ 2 = Kfun q := rfl
    have heqD : (q.2 - q.1) * (h q.2 - h q.1) = denomFun q := rfl
    rw [heqK, heqD] at hbase
    have heqE : (denomFun q)⁻¹ * (∫ t in q.1..q.2, |h t|) = Efun q := rfl
    rw [heqE] at hbase
    have h1 : Dmin * ‖p‖ ≤ (denomFun q)⁻¹ / Kfun q * ‖p‖ :=
      mul_le_mul_of_nonneg_right (hDge q hq) (norm_nonneg _)
    linarith [hbase, h1, hEle q hq]
  -- The search radius `R`, and the fixed compact set `K := closedBall 0 R`.
  set R : ℝ := 2 * Emax / Dmin with hRdef
  have hRnonneg : (0:ℝ) ≤ R := by rw [hRdef]; positivity
  set Kball : Set (ℝ × ℝ) := Metric.closedBall (0 : ℝ × ℝ) R with hKballdef
  have hKballCompact : IsCompact Kball := isCompact_closedBall _ _
  -- The clamped, globally-defined restriction of `betaG`.
  have haCltbC : ∀ q : ℝ × ℝ, aC q.1 < bC q.2 := by
    intro q
    have h1 : aC q.1 ≤ a₀ + δ := (haCmem q.1).2
    have h2 : b₀ - δ ≤ bC q.2 := (hbCmem q.2).1
    have h3 : a₀ + δ < b₀ - δ := by rw [hδdef]; linarith
    linarith
  set clampDenom : ℝ × ℝ → ℝ := fun q => (bC q.2 - aC q.1) * (h (bC q.2) - h (aC q.1))
    with hclampDenomdef
  have hclampDenomCont : Continuous clampDenom :=
    ((hbCcont.comp continuous_snd).sub (haCcont.comp continuous_fst)).mul
      ((hc.comp (hbCcont.comp continuous_snd)).sub (hc.comp (haCcont.comp continuous_fst)))
  have hclampDenomPos : ∀ q : ℝ × ℝ, (0:ℝ) < clampDenom q :=
    fun q => mul_pos (sub_pos.mpr (haCltbC q)) (sub_pos.mpr (hh (haCltbC q)))
  have hclampInvCont : Continuous (fun q : ℝ × ℝ => (clampDenom q)⁻¹) :=
    hclampDenomCont.inv₀ (fun q => (hclampDenomPos q).ne')
  set bigG : ℝ × ℝ → ℝ × ℝ → ℝ := fun q p => betaG h (aC q.1) (bC q.2) p with hbigGdef
  have hbigGuncurryCont : Continuous (Function.uncurry bigG) := by
    have hΨ : Continuous (fun z : (ℝ × ℝ) × ℝ × ℝ =>
        ((aC z.1.1, bC z.1.2) : ℝ × ℝ)) :=
      (haCcont.comp continuous_fst.fst).prodMk (hbCcont.comp continuous_fst.snd)
    have hΨ' : Continuous (fun z : (ℝ × ℝ) × ℝ × ℝ => ((aC z.1.1, bC z.1.2), z.2)) :=
      hΨ.prodMk continuous_snd
    have hintcomp : Continuous (fun z : (ℝ × ℝ) × ℝ × ℝ =>
        ∫ t in (aC z.1.1)..(bC z.1.2), |h t - (z.2.1 * t + z.2.2)|) :=
      (continuous_integral_bounds_affine h hc).comp hΨ'
    have hprefactorcomp : Continuous (fun z : (ℝ × ℝ) × ℝ × ℝ => (clampDenom z.1)⁻¹) :=
      hclampInvCont.comp continuous_fst
    have heq : (Function.uncurry bigG) = fun z : (ℝ × ℝ) × ℝ × ℝ =>
        (clampDenom z.1)⁻¹ * ∫ t in (aC z.1.1)..(bC z.1.2), |h t - (z.2.1 * t + z.2.2)| := rfl
    rw [heq]
    exact hprefactorcomp.mul hintcomp
  set Φext : ℝ × ℝ → ℝ := fun q => sInf (bigG q '' Kball) with hΦextdef
  have hΦextCont : Continuous Φext := hKballCompact.continuous_sInf hbigGuncurryCont
  -- `Φext` agrees with `beta h` throughout `Ubar`.
  have hΦeqBeta : ∀ q ∈ Ubar, Φext q = beta h q.1 q.2 := by
    intro q hq
    have haCeq : aC q.1 = q.1 := haCid q.1 hq.1
    have hbCeq : bC q.2 = q.2 := hbCid q.2 hq.2
    have hbigGeq : ∀ p, bigG q p = betaG h q.1 q.2 p := by
      intro p
      show betaG h (aC q.1) (bC q.2) p = betaG h q.1 q.2 p
      rw [haCeq, hbCeq]
    have hΦeq : Φext q = sInf (betaG h q.1 q.2 '' Kball) := by
      show sInf (bigG q '' Kball) = sInf (betaG h q.1 q.2 '' Kball)
      congr 1
      exact Set.image_congr (fun p _ => hbigGeq p)
    rw [hΦeq]
    have hab : q.1 < q.2 := hUbarLt q hq
    have hrange_eq : beta h q.1 q.2 = sInf (Set.range (betaG h q.1 q.2)) :=
      beta_eq_sInf_range h hh q.1 q.2 hab
    have hbdd_range : BddBelow (Set.range (betaG h q.1 q.2)) :=
      ⟨0, fun r ⟨p, hp⟩ => hp ▸ betaG_nonneg h hh q.1 q.2 hab p⟩
    have hsub : betaG h q.1 q.2 '' Kball ⊆ Set.range (betaG h q.1 q.2) :=
      fun r ⟨p, _, hp⟩ => ⟨p, hp⟩
    have hnonempty_ball : (betaG h q.1 q.2 '' Kball).Nonempty :=
      ⟨betaG h q.1 q.2 (0, 0), Set.mem_image_of_mem _ (by
        show (0, 0) ∈ Metric.closedBall (0 : ℝ × ℝ) R
        simp [hRnonneg])⟩
    have hle1 : beta h q.1 q.2 ≤ sInf (betaG h q.1 q.2 '' Kball) := by
      rw [hrange_eq]
      exact csInf_le_csInf hbdd_range hnonempty_ball hsub
    obtain ⟨κs, τs, hstar⟩ := beta_attained h hh hc q.1 q.2 hab
    have hstar' : betaG h q.1 q.2 (κs, τs) = beta h q.1 q.2 := hstar
    have hbetaEbound : beta h q.1 q.2 ≤ Emax := by
      have hle0 : beta h q.1 q.2 ≤ betaG h q.1 q.2 (0, 0) := by
        rw [hrange_eq]; exact csInf_le hbdd_range ⟨(0, 0), rfl⟩
      rw [hbetaGE q hq] at hle0
      linarith [hle0, hEle q hq]
    have hnormbound : ‖(κs, τs)‖ ≤ R := by
      have hcoercive := huniformCoercive q hq (κs, τs)
      rw [hstar'] at hcoercive
      have hfinal : Dmin * ‖(κs, τs)‖ ≤ beta h q.1 q.2 + Emax := by linarith [hcoercive]
      have hstep : ‖(κs, τs)‖ ≤ (beta h q.1 q.2 + Emax) / Dmin := by
        rw [le_div_iff₀ hDminPos]; linarith [hfinal]
      calc ‖(κs, τs)‖ ≤ (beta h q.1 q.2 + Emax) / Dmin := hstep
        _ ≤ (Emax + Emax) / Dmin := div_le_div_of_nonneg_right (by linarith [hbetaEbound]) hDminPos.le
        _ = R := by rw [hRdef]; ring
    have hmemK : (κs, τs) ∈ Kball := by
      rw [hKballdef, Metric.mem_closedBall, dist_zero_right]
      exact hnormbound
    have hle2 : sInf (betaG h q.1 q.2 '' Kball) ≤ beta h q.1 q.2 := by
      rw [← hstar']
      exact csInf_le (hbdd_range.mono hsub) (Set.mem_image_of_mem _ hmemK)
    linarith [hle1, hle2]
  -- `Ubar` is a neighbourhood of `(a₀, b₀)`, so `Φext` and `beta h` agree eventually there.
  have hUbarNhds : Ubar ∈ nhds (a₀, b₀) := by
    rw [hUbardef, nhds_prod_eq]
    exact Filter.prod_mem_prod (Icc_mem_nhds (by linarith) (by linarith))
      (Icc_mem_nhds (by linarith) (by linarith))
  have heventually : Φext =ᶠ[nhds (a₀, b₀)] (fun q => beta h q.1 q.2) :=
    Filter.eventually_of_mem hUbarNhds hΦeqBeta
  exact hΦextCont.continuousAt.congr heventually

/-- **Remark 5.2 (continuity)**: `β_h(x, y)` is continuous in `(x, y)` off the
diagonal `y = 0`, hence measurable — so the Carleson box integrals of
`β_h² / y` are meaningful. -/
theorem continuous_betaPt (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h) :
    ContinuousOn (fun p : ℝ × ℝ => betaPt h p.1 p.2) {p | p.2 ≠ 0} := by
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  rcases lt_or_gt_of_ne hp with hneg | hpos
  · -- `y < 0`: `betaPt` is identically `0` on the open half-plane `{y < 0}`.
    have hopenNeg : IsOpen {q : ℝ × ℝ | q.2 < 0} := isOpen_lt continuous_snd continuous_const
    have hconst : (fun q : ℝ × ℝ => betaPt h q.1 q.2) =ᶠ[nhds p] (fun _ => (0:ℝ)) := by
      filter_upwards [hopenNeg.mem_nhds hneg] with q hq
      exact beta_eq_zero_of_gt h hh (q.1 - q.2) (q.1 + q.2) (by linarith [hq])
    exact (continuousAt_const.congr hconst.symm).continuousWithinAt
  · -- `y > 0`: reduce to `continuousAt_beta` via the linear change of variables
    -- `(x, y) ↦ (x - y, x + y)`.
    have hlin : Continuous (fun q : ℝ × ℝ => (q.1 - q.2, q.1 + q.2)) := by fun_prop
    have hcb := continuousAt_beta h hh hc (p.1 - p.2) (p.1 + p.2) (by linarith [hpos])
    have hcontAt : ContinuousAt
        ((fun r : ℝ × ℝ => beta h r.1 r.2) ∘ (fun q : ℝ × ℝ => (q.1 - q.2, q.1 + q.2))) p :=
      ContinuousAt.comp hcb hlin.continuousAt
    exact hcontAt.continuousWithinAt

/-- **Definition (`L²` orthogonal projection)** of `h` onto affine functions
on `I₀ = [a, b]`: `L_{I₀}(t) = m₀ (t - x) + c₀` with `x` the centre,
`c₀` the average of `h` and `m₀ = 3/(2y³) ∫ h(s)(s - x) ds`. -/
def l2Proj (h : ℝ → ℝ) (a b : ℝ) (t : ℝ) : ℝ :=
  (3 / (2 * ((b - a) / 2) ^ 3) * ∫ s in a..b, h s * (s - (a + b) / 2)) *
    (t - (a + b) / 2) + intervalAvg h a b

/-! ## Section 5.2: lower bounds for the two denominators -/

/-- **Step (1) in the proof of Lemma (Denominator Lower Bounds)**: for every
real `q`,
`|q - w̄| ≥ c_ρ (L + dist(q, h(I₀)))`, obtained from `v ≥ c_DE L` and
`dist(u, h(I₀)) ≤ C₀ L`. -/
theorem dist_conj_lower_bound (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ h : ℝ → ℝ, Quasisymmetric h ρ → ∀ x y : ℝ, 0 < y → ∀ q : ℝ,
        c * ((h (x + y) - h (x - y)) +
              Metric.infDist q (Set.Icc (h (x - y)) (h (x + y)))) ≤
          ‖(q : ℂ) - star (douadyEarle h ((x : ℂ) + (y : ℂ) * Complex.I))‖ := by
  obtain ⟨cDE, CDE, hcDEpos, hcDEleCDE, hDE⟩ := de_localization ρ hρ
  obtain ⟨C0, hC0nonneg, hR⟩ := real_part_localization ρ hρ
  set C1 : ℝ := C0 + 1 with hC1def
  have hC1pos : (0:ℝ) < C1 := by rw [hC1def]; linarith
  refine ⟨min (cDE / (1 + 2 * C1)) (C1 / (2 * (2 * C1 + 1))),
    lt_min (by positivity) (by positivity), ?_⟩
  intro h hqsh x y hy q
  have hh : StrictMono h := hqsh.1
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hzdef
  have hzre : z.re = x := by simp [hzdef]
  have hzim : z.im = y := by simp [hzdef]
  have hzpos : (0:ℝ) < z.im := by rw [hzim]; exact hy
  set w := douadyEarle h z with hwdef
  set L : ℝ := h (x + y) - h (x - y) with hLdef
  have hLpos : (0:ℝ) < L := by
    have := hh (show x - y < x + y by linarith)
    rw [hLdef]; linarith
  have hvbound := hDE h hqsh z hzpos
  rw [hzre, hzim] at hvbound
  have hv1 : cDE * L ≤ w.im := hvbound.1
  have hd0 := hR h hqsh z hzpos
  rw [hzre, hzim] at hd0
  set d : ℝ := Metric.infDist q (Set.Icc (h (x - y)) (h (x + y))) with hddef
  have hdnonneg : (0:ℝ) ≤ d := Metric.infDist_nonneg
  have hnormim : w.im ≤ ‖(q : ℂ) - star w‖ := by
    have h1 : ((q : ℂ) - star w).im = w.im := by simp
    have h2 : |((q : ℂ) - star w).im| ≤ ‖(q : ℂ) - star w‖ := Complex.abs_im_le_norm _
    rw [h1] at h2
    exact (le_abs_self _).trans h2
  have hnormre : |q - w.re| ≤ ‖(q : ℂ) - star w‖ := by
    have h1 : ((q : ℂ) - star w).re = q - w.re := by simp
    have h2 : |((q : ℂ) - star w).re| ≤ ‖(q : ℂ) - star w‖ := Complex.abs_re_le_norm _
    rwa [h1] at h2
  have htri : d ≤ |q - w.re| + C0 * L := by
    have h1 : d ≤ Metric.infDist w.re (Set.Icc (h (x - y)) (h (x + y))) + dist q w.re :=
      Metric.infDist_le_infDist_add_dist
    rw [Real.dist_eq] at h1
    linarith [h1, hd0]
  by_cases hcase : d ≤ 2 * C1 * L
  · -- Case 1: `d ≤ 2 C1 L`.
    have hgoal : cDE / (1 + 2 * C1) * (L + d) ≤ ‖(q : ℂ) - star w‖ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 1 + 2 * C1)]
      nlinarith [hcase, hv1, hnormim]
    calc min (cDE / (1 + 2 * C1)) (C1 / (2 * (2 * C1 + 1))) * (L + d)
        ≤ cDE / (1 + 2 * C1) * (L + d) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (by linarith [hLpos, hdnonneg])
      _ ≤ ‖(q : ℂ) - star w‖ := hgoal
  · -- Case 2: `d > 2 C1 L`.
    rw [not_le] at hcase
    have hqu : d / 2 < |q - w.re| := by
      nlinarith [htri, hC0nonneg, hC1def, hcase, hLpos]
    have hgoal : C1 / (2 * (2 * C1 + 1)) * (L + d) ≤ ‖(q : ℂ) - star w‖ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < 2 * (2 * C1 + 1))]
      have h1 : C1 * (L + d) ≤ (2 * C1 + 1) * d := by
        nlinarith [hcase, hC1pos, hLpos]
      have h2 : (2 * C1 + 1) * d ≤ 2 * (2 * C1 + 1) * |q - w.re| := by
        nlinarith [hqu, hC1pos]
      have h3 : 2 * (2 * C1 + 1) * |q - w.re| ≤ 2 * (2 * C1 + 1) * ‖(q : ℂ) - star w‖ :=
        mul_le_mul_of_nonneg_left hnormre (by positivity)
      linarith [h1, h2, h3]
    calc min (cDE / (1 + 2 * C1)) (C1 / (2 * (2 * C1 + 1))) * (L + d)
        ≤ C1 / (2 * (2 * C1 + 1)) * (L + d) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by linarith [hLpos, hdnonneg])
      _ ≤ ‖(q : ℂ) - star w‖ := hgoal

/-- The slope `m₀ = 3/(2y³) ∫_{I₀} h(s)(s - x) ds` of the `L²` projection
`L_{I₀}`. -/
def l2ProjSlope (h : ℝ → ℝ) (a b : ℝ) : ℝ :=
  3 / (2 * ((b - a) / 2) ^ 3) * ∫ s in a..b, h s * (s - (a + b) / 2)

/-- `L_{I₀}(t) = m₀ (t - c_{I₀}) + c₀`. -/
theorem l2Proj_eq_slope (h : ℝ → ℝ) (a b t : ℝ) :
    l2Proj h a b t = l2ProjSlope h a b * (t - (a + b) / 2) + intervalAvg h a b := rfl

/-- **Symmetrised form of the slope**:
`m₀ = 3/(2y³) ∫₀^y (h(x+τ) - h(x-τ)) τ dτ`, manifestly positive for
increasing `h`. -/
theorem l2ProjSlope_symmetrised (h : ℝ → ℝ) (hc : Continuous h) (x y : ℝ) (_hy : 0 < y) :
    l2ProjSlope h (x - y) (x + y) =
      3 / (2 * y ^ 3) * ∫ τ in (0:ℝ)..y, (h (x + τ) - h (x - τ)) * τ := by
  unfold l2ProjSlope
  have h1 : (x + y - (x - y)) / 2 = y := by ring
  have h2 : (x - y + (x + y)) / 2 = x := by ring
  rw [h1, h2]
  congr 1
  set f : ℝ → ℝ := fun s => h s * (s - x) with hfdef
  have hfcont : Continuous f := by rw [hfdef]; fun_prop
  have hsplit : (∫ s in (x - y)..(x + y), f s) =
      (∫ s in (x - y)..x, f s) + ∫ s in x..(x + y), f s :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hfcont.intervalIntegrable (x - y) x) (hfcont.intervalIntegrable x (x + y))).symm
  have hpiece2 : (∫ s in x..(x + y), f s) = ∫ τ in (0:ℝ)..y, h (x + τ) * τ := by
    have heq := intervalIntegral.integral_comp_add_left (a := (0:ℝ)) (b := y) f x
    rw [show x + (0:ℝ) = x by ring] at heq
    rw [← heq]
    congr 1
    funext τ
    show h (x + τ) * (x + τ - x) = h (x + τ) * τ
    ring_nf
  have hpiece1 : (∫ s in (x - y)..x, f s) = -∫ τ in (0:ℝ)..y, h (x - τ) * τ := by
    have heq := intervalIntegral.integral_comp_sub_left (a := (0:ℝ)) (b := y) f x
    rw [show x - (0:ℝ) = x by ring] at heq
    rw [← heq]
    have hpt : (fun τ : ℝ => f (x - τ)) = fun τ => -(h (x - τ) * τ) := by
      funext τ
      show h (x - τ) * (x - τ - x) = -(h (x - τ) * τ)
      ring_nf
    rw [hpt, intervalIntegral.integral_neg]
  rw [hsplit, hpiece1, hpiece2]
  have hg1 : Continuous (fun τ : ℝ => h (x + τ) * τ) := by fun_prop
  have hg2 : Continuous (fun τ : ℝ => h (x - τ) * τ) := by fun_prop
  have hcomb : (∫ τ in (0:ℝ)..y, (h (x + τ) - h (x - τ)) * τ) =
      (∫ τ in (0:ℝ)..y, h (x + τ) * τ) - ∫ τ in (0:ℝ)..y, h (x - τ) * τ := by
    rw [← intervalIntegral.integral_sub (hg1.intervalIntegrable 0 y) (hg2.intervalIntegrable 0 y)]
    congr 1
    funext τ
    ring
  rw [hcomb]
  ring

/-- **Slope of `L_{I₀}`**: `m₀ ≍_ρ L/(2y) = a_{I₀}`; in particular `m₀ > 0`. -/
theorem l2ProjSlope_comparable (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ h : ℝ → ℝ, Quasisymmetric h ρ → ∀ x y : ℝ, 0 < y →
        c * ((h (x + y) - h (x - y)) / (2 * y)) ≤ l2ProjSlope h (x - y) (x + y) ∧
          l2ProjSlope h (x - y) (x + y) ≤ C * ((h (x + y) - h (x - y)) / (2 * y)) := by
  refine ⟨9 / (8 * (1 + ρ)), 3 / 2, by positivity, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity : (0:ℝ) < 8 * (1 + ρ))]
    nlinarith [hρ]
  intro h hqs x y hy
  obtain ⟨hh, hc, _, hqsrel⟩ := hqs
  have hmono : Monotone h := hh.monotone
  rw [l2ProjSlope_symmetrised h hc x y hy]
  set L : ℝ := h (x + y) - h (x - y) with hLdef
  have hcont1 : Continuous (fun τ : ℝ => (h (x + τ) - h (x - τ)) * τ) := by fun_prop
  -- Pointwise bounds `0 ≤ (h(x+τ) - h(x-τ)) τ ≤ L τ` for `τ ∈ [0, y]`.
  have hupper_pt : ∀ τ ∈ Set.Icc (0:ℝ) y, (h (x + τ) - h (x - τ)) * τ ≤ L * τ := by
    intro τ hτ
    have h1 : h (x + τ) ≤ h (x + y) := hmono (by linarith [hτ.2])
    have h2 : h (x - y) ≤ h (x - τ) := hmono (by linarith [hτ.2])
    exact mul_le_mul_of_nonneg_right (by rw [hLdef]; linarith) hτ.1
  have hlower_nonneg : ∀ τ ∈ Set.Icc (0:ℝ) y, (0:ℝ) ≤ (h (x + τ) - h (x - τ)) * τ := by
    intro τ hτ
    have : h (x - τ) ≤ h (x + τ) := hmono (by linarith [hτ.1])
    exact mul_nonneg (by linarith) hτ.1
  -- Upper bound: `∫₀^y (h(x+τ)-h(x-τ))τ dτ ≤ L y²/2`.
  have hUpperInt : (∫ τ in (0:ℝ)..y, (h (x + τ) - h (x - τ)) * τ) ≤ L * y ^ 2 / 2 := by
    have hstep : (∫ τ in (0:ℝ)..y, (h (x + τ) - h (x - τ)) * τ) ≤ ∫ τ in (0:ℝ)..y, L * τ :=
      intervalIntegral.integral_mono_on hy.le (hcont1.intervalIntegrable _ _)
        ((continuous_const.mul continuous_id).intervalIntegrable _ _) hupper_pt
    have hLy2 : (∫ τ in (0:ℝ)..y, L * τ) = L * y ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    linarith [hstep, hLy2.le, hLy2.ge]
  -- Growth estimate: `h(x+τ)-h(x-τ) ≥ L/(1+ρ)` for `τ ∈ [y/2, y]`.
  have hgrowth : ∀ τ ∈ Set.Icc (y / 2) y, L / (1 + ρ) ≤ h (x + τ) - h (x - τ) := by
    intro τ hτ
    have hτpos : (0:ℝ) < τ := by linarith [hτ.1]
    have hp1 := (hqsrel (x + τ) τ hτpos).1
    rw [show x + τ + τ = x + 2 * τ by ring, show x + τ - τ = x by ring] at hp1
    have hp2 := (hqsrel (x - τ) τ hτpos).2
    rw [show x - τ + τ = x by ring, show x - τ - τ = x - 2 * τ by ring] at hp2
    have hLmono : L ≤ h (x + 2 * τ) - h (x - 2 * τ) := by
      have e1 : h (x + y) ≤ h (x + 2 * τ) := hmono (by linarith [hτ.1])
      have e2 : h (x - 2 * τ) ≤ h (x - y) := hmono (by linarith [hτ.1])
      rw [hLdef]; linarith
    have hsum : h (x + 2 * τ) - h (x - 2 * τ) ≤ (1 + ρ) * (h (x + τ) - h (x - τ)) := by
      nlinarith [hp1, hp2]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 + ρ)]
    linarith [hLmono, hsum]
  -- Lower bound: `∫₀^y (h(x+τ)-h(x-τ))τ dτ ≥ (L/(1+ρ)) · 3y²/8`.
  have hLowerInt : (L / (1 + ρ)) * (3 * y ^ 2 / 8) ≤
      ∫ τ in (0:ℝ)..y, (h (x + τ) - h (x - τ)) * τ := by
    have hsplit : (∫ τ in (0:ℝ)..y, (h (x + τ) - h (x - τ)) * τ) =
        (∫ τ in (0:ℝ)..(y / 2), (h (x + τ) - h (x - τ)) * τ) +
          ∫ τ in (y / 2)..y, (h (x + τ) - h (x - τ)) * τ :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont1.intervalIntegrable 0 (y / 2)) (hcont1.intervalIntegrable (y / 2) y)).symm
    have hfirst_nonneg : (0:ℝ) ≤ ∫ τ in (0:ℝ)..(y / 2), (h (x + τ) - h (x - τ)) * τ :=
      intervalIntegral.integral_nonneg (by linarith) (fun τ hτ => hlower_nonneg τ ⟨hτ.1, by linarith [hτ.2]⟩)
    have hsecond : (L / (1 + ρ)) * (3 * y ^ 2 / 8) ≤
        ∫ τ in (y / 2)..y, (h (x + τ) - h (x - τ)) * τ := by
      have hconstint : (∫ τ in (y / 2)..y, (L / (1 + ρ)) * τ) = (L / (1 + ρ)) * (3 * y ^ 2 / 8) := by
        rw [intervalIntegral.integral_const_mul, integral_id]; ring
      have hmonoint : (∫ τ in (y / 2)..y, (L / (1 + ρ)) * τ) ≤
          ∫ τ in (y / 2)..y, (h (x + τ) - h (x - τ)) * τ :=
        intervalIntegral.integral_mono_on (by linarith)
          ((continuous_const.mul continuous_id).intervalIntegrable _ _)
          (hcont1.intervalIntegrable _ _)
          (fun τ hτ => mul_le_mul_of_nonneg_right (hgrowth τ hτ) (by linarith [hτ.1]))
      linarith [hconstint.le, hconstint.ge, hmonoint]
    linarith [hsplit, hfirst_nonneg, hsecond]
  constructor
  · have hstep : 3 / (2 * y ^ 3) * ((L / (1 + ρ)) * (3 * y ^ 2 / 8)) ≤
        3 / (2 * y ^ 3) * ∫ τ in (0:ℝ)..y, (h (x + τ) - h (x - τ)) * τ :=
      mul_le_mul_of_nonneg_left hLowerInt (by positivity)
    have heq : 3 / (2 * y ^ 3) * ((L / (1 + ρ)) * (3 * y ^ 2 / 8)) = 9 / (8 * (1 + ρ)) * (L / (2 * y)) := by
      field_simp; ring
    linarith [hstep, heq.le, heq.ge]
  · have hstep : 3 / (2 * y ^ 3) * (∫ τ in (0:ℝ)..y, (h (x + τ) - h (x - τ)) * τ) ≤
        3 / (2 * y ^ 3) * (L * y ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hUpperInt (by positivity)
    have heq : 3 / (2 * y ^ 3) * (L * y ^ 2 / 2) = 3 / 2 * (L / (2 * y)) := by
      field_simp
    linarith [hstep, heq.le, heq.ge]

/-- **Position of `c₀`**: the average of `h` over `I₀` lies in `h(I₀)`. -/
theorem intervalAvg_mem_image (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (a b : ℝ) (hab : a < b) : intervalAvg h a b ∈ Set.Icc (h a) (h b) := by
  have hint : IntervalIntegrable h volume a b := hc.intervalIntegrable a b
  have hmono : Monotone h := hh.monotone
  have hba : (0:ℝ) < b - a := by linarith
  have hlow : h a * (b - a) ≤ ∫ t in a..b, h t := by
    have hle := intervalIntegral.integral_mono_on hab.le intervalIntegrable_const hint
      (fun t ht => hmono ht.1)
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at hle
  have hhigh : (∫ t in a..b, h t) ≤ h b * (b - a) := by
    have hle := intervalIntegral.integral_mono_on hab.le hint intervalIntegrable_const
      (fun t ht => hmono ht.2)
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at hle
  rw [Set.mem_Icc]
  unfold intervalAvg
  refine ⟨?_, ?_⟩
  · rw [le_div_iff₀ hba]; exact hlow
  · rw [div_le_iff₀ hba]; exact hhigh

/-- **Quasisymmetry across dyadic blocks**: with `R_m = h(x + 2^m y) - h(x)`
and `S_m = h(x) - h(x - 2^m y)`, one has `ρ⁻¹ ≤ R_m/S_m ≤ ρ` and
`R_{m+1} ≤ (1 + ρ) R_m`, `S_{m+1} ≤ (1 + ρ) S_m`. -/
theorem qs_dyadic_growth (ρ : ℝ) (_hρ : 1 ≤ ρ) (h : ℝ → ℝ) (hqs : Quasisymmetric h ρ)
    (x y : ℝ) (hy : 0 < y) (m : ℕ) :
    h (x + 2 ^ m * y) - h x ≤ ρ * (h x - h (x - 2 ^ m * y)) ∧
      h x - h (x - 2 ^ m * y) ≤ ρ * (h (x + 2 ^ m * y) - h x) ∧
      h (x + 2 ^ (m + 1) * y) - h x ≤ (1 + ρ) * (h (x + 2 ^ m * y) - h x) ∧
      h x - h (x - 2 ^ (m + 1) * y) ≤ (1 + ρ) * (h x - h (x - 2 ^ m * y)) := by
  have ht : (0:ℝ) < 2 ^ m * y := by positivity
  obtain ⟨hbase1, hbase2⟩ := hqs.2.2.2 x (2 ^ m * y) ht
  refine ⟨hbase1, hbase2, ?_, ?_⟩
  · -- `R_{m+1} ≤ (1 + ρ) R_m`: apply the base inequality at `x + 2^m y`.
    have hbase3 := (hqs.2.2.2 (x + 2 ^ m * y) (2 ^ m * y) ht).1
    have heq1 : x + 2 ^ m * y + 2 ^ m * y = x + 2 ^ (m + 1) * y := by ring
    have heq2 : x + 2 ^ m * y - 2 ^ m * y = x := by ring
    rw [heq1, heq2] at hbase3
    linarith [hbase3]
  · -- `S_{m+1} ≤ (1 + ρ) S_m`: apply the base inequality at `x - 2^m y`.
    have hbase4 := (hqs.2.2.2 (x - 2 ^ m * y) (2 ^ m * y) ht).2
    have heq3 : x - 2 ^ m * y - 2 ^ m * y = x - 2 ^ (m + 1) * y := by ring
    have heq4 : x - 2 ^ m * y + 2 ^ m * y = x := by ring
    rw [heq3, heq4] at hbase4
    linarith [hbase4]


/-- **Lemma (Denominator Lower Bounds for `L²` Projection)**: for
`z = x + iy`, `w = e(h)(z)`, `I₀ = [x-y, x+y]`, `L = |h(I₀)|`, dyadic shells
`T_k = I_k ∖ I_{k-1}` and `t ∈ T_k`:
`|L_{I₀}(t) - w̄| ≥ c_ρ 2^k L` and `|h(t) - w̄| ≥ c_ρ |h(I_k)|`. -/
theorem denominator_lower_bounds (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧
      ∀ h : ℝ → ℝ, Quasisymmetric h ρ → ∀ x y : ℝ, 0 < y →
        ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ,
          (2 : ℝ) ^ (k - 1) * y ≤ |t - x| → |t - x| ≤ (2 : ℝ) ^ k * y →
            ‖(l2Proj h (x - y) (x + y) t : ℂ) -
                star (douadyEarle h (x + y * Complex.I))‖ ≥
              c * 2 ^ k * (h (x + y) - h (x - y)) ∧
            ‖(h t : ℂ) - star (douadyEarle h (x + y * Complex.I))‖ ≥
              c * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)) := by
  obtain ⟨c1, hc1pos, hc1⟩ := dist_conj_lower_bound ρ hρ
  obtain ⟨cS, CS, hcSpos, _, hSlope⟩ := l2ProjSlope_comparable ρ hρ
  set c : ℝ := min (c1 * cS / 4) (c1 / (1 + ρ) ^ 2) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact lt_min (by positivity) (by positivity)
  refine ⟨c, hcpos, ?_⟩
  intro h hqsh x y hy k hk t ht1 ht2
  have hh : StrictMono h := hqsh.1
  have hcont : Continuous h := hqsh.2.1
  set L : ℝ := h (x + y) - h (x - y) with hLdef
  have hLpos : (0:ℝ) < L := by
    have := hh (show x - y < x + y by linarith)
    rw [hLdef]; linarith
  set w := douadyEarle h ((x:ℂ) + (y:ℂ) * Complex.I) with hwdef
  have hendpoints : h (x - y) ≤ h (x + y) := by linarith [hLdef, hLpos]
  have hxmy_le_x : h (x - y) ≤ h x := hh.monotone (by linarith)
  have hx_le_xpy : h x ≤ h (x + y) := hh.monotone (by linarith)
  constructor
  · -- Conjunct 1: `L_{I₀}(t)` denominator bound.
    set c0 : ℝ := intervalAvg h (x - y) (x + y) with hc0def
    have hc0mem : c0 ∈ Set.Icc (h (x - y)) (h (x + y)) :=
      intervalAvg_mem_image h hh hcont (x - y) (x + y) (by linarith)
    set m0 : ℝ := l2ProjSlope h (x - y) (x + y) with hm0def
    have hm0lb : cS * (L / (2 * y)) ≤ m0 := (hSlope h hqsh x y hy).1
    have hm0pos : 0 < m0 := lt_of_lt_of_le (by positivity) hm0lb
    have hl2eq : l2Proj h (x - y) (x + y) t = m0 * (t - x) + c0 := by
      rw [l2Proj_eq_slope, show (x - y + (x + y)) / 2 = x from by ring]
    have h2k' : (2:ℝ) ^ k = (2:ℝ) ^ (k - 1) * 2 := by
      conv_lhs => rw [show k = (k - 1) + 1 from by omega]
      rw [pow_succ]
    have h2k : (2:ℝ) ^ (k - 1) = (2:ℝ) ^ k / 2 := by rw [h2k']; ring
    have hstep : cS * (2:ℝ) ^ k * L / 4 ≤ |m0 * (t - x)| := by
      rw [abs_mul, abs_of_pos hm0pos]
      calc cS * (2:ℝ) ^ k * L / 4 = (cS * (L / (2 * y))) * ((2:ℝ) ^ (k - 1) * y) := by
            rw [h2k]; field_simp; ring
        _ ≤ m0 * |t - x| := mul_le_mul hm0lb ht1 (by positivity) hm0pos.le
    have hdiff : l2Proj h (x - y) (x + y) t - c0 = m0 * (t - x) := by rw [hl2eq]; ring
    have hdd : dist (l2Proj h (x - y) (x + y) t) c0 ≤
        Metric.infDist (l2Proj h (x - y) (x + y) t) (Set.Icc (h (x - y)) (h (x + y))) +
          Metric.diam (Set.Icc (h (x - y)) (h (x + y))) :=
      Metric.dist_le_infDist_add_diam (Metric.isBounded_Icc _ _) hc0mem
    rw [Real.dist_eq, hdiff, Real.diam_Icc (by linarith : h (x - y) ≤ h (x + y))] at hdd
    have hLdist : cS * (2:ℝ) ^ k * L / 4 ≤
        L + Metric.infDist (l2Proj h (x - y) (x + y) t) (Set.Icc (h (x - y)) (h (x + y))) := by
      linarith [hdd, hstep, hLdef]
    have hbase := hc1 h hqsh x y hy (l2Proj h (x - y) (x + y) t)
    have hcombined : c1 * (cS * (2:ℝ) ^ k * L / 4) ≤ ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖ :=
      le_trans (mul_le_mul_of_nonneg_left hLdist hc1pos.le) hbase
    have hfinal : c * 2 ^ k * L ≤ c1 * (cS * (2:ℝ) ^ k * L / 4) := by
      have hle : c ≤ c1 * cS / 4 := min_le_left _ _
      have hnn : (0:ℝ) ≤ (2:ℝ) ^ k * L := by positivity
      calc c * 2 ^ k * L = c * ((2:ℝ) ^ k * L) := by ring
        _ ≤ (c1 * cS / 4) * ((2:ℝ) ^ k * L) := mul_le_mul_of_nonneg_right hle hnn
        _ = c1 * (cS * (2:ℝ) ^ k * L / 4) := by ring
    exact le_trans hfinal hcombined
  · -- Conjunct 2: `h(t)` denominator bound.
    set Rm : ℕ → ℝ := fun m => h (x + 2 ^ m * y) - h x with hRmdef
    set Sm : ℕ → ℝ := fun m => h x - h (x - 2 ^ m * y) with hSmdef
    have hkeq : (k - 1) + 1 = k := by omega
    have hgrowth_km1 := qs_dyadic_growth ρ hρ h hqsh x y hy (k - 1)
    have hR_step : Rm k ≤ (1 + ρ) * Rm (k - 1) := by
      have h1 := hgrowth_km1.2.2.1; rw [hkeq] at h1; exact h1
    have hS_step : Sm k ≤ (1 + ρ) * Sm (k - 1) := by
      have h1 := hgrowth_km1.2.2.2; rw [hkeq] at h1; exact h1
    have hgrowth_k := qs_dyadic_growth ρ hρ h hqsh x y hy k
    have hIk_boundR : Rm k + Sm k ≤ (1 + ρ) ^ 2 * Rm (k - 1) := by
      nlinarith [hR_step, hS_step, hgrowth_k.2.1]
    have hIk_boundS : Rm k + Sm k ≤ (1 + ρ) ^ 2 * Sm (k - 1) := by
      nlinarith [hR_step, hS_step, hgrowth_k.1]
    have hIk_eq : h (x + 2 ^ k * y) - h (x - 2 ^ k * y) = Rm k + Sm k := by
      rw [hRmdef, hSmdef]; ring
    have h2km1_ge_one : (1:ℝ) ≤ (2:ℝ) ^ (k - 1) := one_le_pow₀ (by norm_num)
    have hcaseA : x + 2 ^ (k - 1) * y ≤ t →
        Rm (k - 1) ≤ L + Metric.infDist (h t) (Set.Icc (h (x - y)) (h (x + y))) := by
      intro hA
      have hht : h (x + 2 ^ (k - 1) * y) ≤ h t := hh.monotone hA
      have hxy_le : h (x + y) ≤ h t := by
        have hxy' : x + y ≤ x + 2 ^ (k - 1) * y := by nlinarith [h2km1_ge_one, hy]
        exact le_trans (hh.monotone hxy') hht
      have hinfDist_lb : h t - h (x + y) ≤ Metric.infDist (h t) (Set.Icc (h (x - y)) (h (x + y))) := by
        rw [Metric.le_infDist (Set.nonempty_Icc.mpr hendpoints)]
        intro s hs
        rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.2, hxy_le] : (0:ℝ) ≤ h t - s)]
        linarith [hs.2]
      rw [hRmdef, hLdef]; linarith [hht, hxmy_le_x, hinfDist_lb]
    have hcaseB : t ≤ x - 2 ^ (k - 1) * y →
        Sm (k - 1) ≤ L + Metric.infDist (h t) (Set.Icc (h (x - y)) (h (x + y))) := by
      intro hB
      have hht : h t ≤ h (x - 2 ^ (k - 1) * y) := hh.monotone hB
      have hxmy_ge : h t ≤ h (x - y) := by
        have hxy' : x - 2 ^ (k - 1) * y ≤ x - y := by nlinarith [h2km1_ge_one, hy]
        exact le_trans hht (hh.monotone hxy')
      have hinfDist_lb : h (x - y) - h t ≤ Metric.infDist (h t) (Set.Icc (h (x - y)) (h (x + y))) := by
        rw [Metric.le_infDist (Set.nonempty_Icc.mpr hendpoints)]
        intro s hs
        rw [Real.dist_eq, abs_of_nonpos (by linarith [hs.1, hxmy_ge] : h t - s ≤ 0)]
        linarith [hs.1]
      rw [hSmdef, hLdef]; linarith [hht, hx_le_xpy, hinfDist_lb]
    have hfinal_bound : (Rm k + Sm k) / (1 + ρ) ^ 2 ≤
        L + Metric.infDist (h t) (Set.Icc (h (x - y)) (h (x + y))) := by
      rcases le_abs.mp ht1 with hA | hA
      · have ht_ge : x + 2 ^ (k - 1) * y ≤ t := by linarith [hA]
        have h1 := hcaseA ht_ge
        calc (Rm k + Sm k) / (1 + ρ) ^ 2 ≤ Rm (k - 1) := by
              rw [div_le_iff₀ (by positivity)]; linarith [hIk_boundR]
          _ ≤ L + Metric.infDist (h t) (Set.Icc (h (x - y)) (h (x + y))) := h1
      · have ht_le : t ≤ x - 2 ^ (k - 1) * y := by linarith [hA]
        have h1 := hcaseB ht_le
        calc (Rm k + Sm k) / (1 + ρ) ^ 2 ≤ Sm (k - 1) := by
              rw [div_le_iff₀ (by positivity)]; linarith [hIk_boundS]
          _ ≤ L + Metric.infDist (h t) (Set.Icc (h (x - y)) (h (x + y))) := h1
    have hbase := hc1 h hqsh x y hy (h t)
    have hcombined : c1 * ((Rm k + Sm k) / (1 + ρ) ^ 2) ≤ ‖(h t : ℂ) - star w‖ :=
      le_trans (mul_le_mul_of_nonneg_left hfinal_bound hc1pos.le) hbase
    have hfinal : c * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)) ≤
        c1 * ((Rm k + Sm k) / (1 + ρ) ^ 2) := by
      rw [hIk_eq]
      have hcle : c ≤ c1 / (1 + ρ) ^ 2 := min_le_right _ _
      have hnn : (0:ℝ) ≤ Rm k + Sm k := by
        rw [← hIk_eq]
        have h2ky : (0:ℝ) < (2:ℝ) ^ k * y := by positivity
        have hle : x - (2:ℝ) ^ k * y ≤ x + (2:ℝ) ^ k * y := by linarith
        linarith [hh.monotone hle]
      calc c * (Rm k + Sm k) ≤ (c1 / (1 + ρ) ^ 2) * (Rm k + Sm k) :=
            mul_le_mul_of_nonneg_right hcle hnn
        _ = c1 * ((Rm k + Sm k) / (1 + ρ) ^ 2) := by ring
    exact le_trans hfinal hcombined

/-! ## Section 5.3: auxiliary lemmas -/

/-- **Lemma (Affine Growth on Concentric Intervals)**: for affine
`P(t) = pt + q` and concentric intervals of ratio `R ≥ 1`,
`⨍_{I'} |P| ≤ C R ⨍_I |P|` with `C` an absolute constant. -/
theorem affine_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ p q c r R : ℝ, 0 < r → 1 ≤ R →
        intervalAvg (fun t => |p * t + q|) (c - R * r) (c + R * r) ≤
          C * R * intervalAvg (fun t => |p * t + q|) (c - r) (c + r) := by
  refine ⟨8, by norm_num, ?_⟩
  intro p q c r R hr hR
  have hRr : 0 < R * r := mul_pos (by linarith) hr
  have hPcont : Continuous fun t => p * t + q :=
    (continuous_const.mul continuous_id).add continuous_const
  have hIntP : ∀ u v : ℝ, IntervalIntegrable (fun t => |p * t + q|) volume u v :=
    fun u v => hPcont.abs.intervalIntegrable _ _
  -- `M` is the maximum of `|P|` on the endpoints of the small interval.
  set M : ℝ := |p * c + q| + |p| * r with hM
  have hMnn : 0 ≤ M := add_nonneg (abs_nonneg _) (mul_nonneg (abs_nonneg _) hr.le)
  -- Choose the endpoint sign `ε` at which `|P| = M`.
  have hε : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      |p * c + q + ε * (p * r)| = |p * c + q| + |p * r| := by
    rcases le_total 0 (p * c + q) with ha | ha
    · rcases le_total 0 (p * r) with hb | hb
      · exact ⟨1, Or.inl rfl, by
          rw [one_mul, abs_of_nonneg (add_nonneg ha hb), abs_of_nonneg ha, abs_of_nonneg hb]⟩
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [neg_one_mul, abs_of_nonneg (by linarith : 0 ≤ p * c + q + -(p * r)),
          abs_of_nonneg ha, abs_of_nonpos hb]
    · rcases le_total 0 (p * r) with hb | hb
      · refine ⟨-1, Or.inr rfl, ?_⟩
        rw [neg_one_mul, abs_of_nonpos (by linarith : p * c + q + -(p * r) ≤ 0),
          abs_of_nonpos ha, abs_of_nonneg hb]
        ring
      · exact ⟨1, Or.inl rfl, by
          rw [one_mul, abs_of_nonpos (add_nonpos ha hb), abs_of_nonpos ha, abs_of_nonpos hb]
          ring⟩
  obtain ⟨ε, hε1, hεabs⟩ := hε
  set t₀ : ℝ := c + ε * r with ht₀def
  have hPt₀ : |p * t₀ + q| = M := by
    have e1 : p * t₀ + q = p * c + q + ε * (p * r) := by rw [ht₀def]; ring
    rw [e1, hεabs, hM, abs_mul, abs_of_pos hr]
  -- Key: on any interval of length `r/2` within distance `r/2` of `t₀`, `|P| ≥ M/2`.
  have hkey : ∀ u v : ℝ, u ≤ v → v - u = r / 2 →
      (∀ t ∈ Set.Icc u v, |t - t₀| ≤ r / 2) →
      r * M / 4 ≤ ∫ t in u..v, |p * t + q| := by
    intro u v huv hlen hdist
    have hpM : |p| ≤ M / r := by
      rw [le_div_iff₀ hr, hM]
      exact le_add_of_nonneg_left (abs_nonneg _)
    have hbound : ∀ t ∈ Set.Icc u v, M / 2 ≤ |p * t + q| := by
      intro t ht
      have hdt : |t₀ - t| ≤ r / 2 := by rw [abs_sub_comm]; exact hdist t ht
      have h1 : (p * t₀ + q) - (p * t + q) = p * (t₀ - t) := by ring
      have h2 : |p * t₀ + q| - |p * t + q| ≤ |p| * |t₀ - t| := by
        calc |p * t₀ + q| - |p * t + q| ≤ |(p * t₀ + q) - (p * t + q)| :=
              abs_sub_abs_le_abs_sub _ _
          _ = |p| * |t₀ - t| := by rw [h1, abs_mul]
      have h3 : |p| * |t₀ - t| ≤ M / r * (r / 2) :=
        mul_le_mul hpM hdt (abs_nonneg _) (div_nonneg hMnn hr.le)
      have h4 : M / r * (r / 2) = M / 2 := by field_simp
      rw [h4] at h3
      linarith [hPt₀]
    calc r * M / 4 = ∫ _ in u..v, (M / 2) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, hlen]; ring
      _ ≤ ∫ t in u..v, |p * t + q| :=
          intervalIntegral.integral_mono_on huv intervalIntegrable_const (hIntP u v) hbound
  -- Subset monotonicity of the integral of the non-negative integrand.
  have hsubset : ∀ u v : ℝ, c - r ≤ u → v ≤ c + r → u ≤ v →
      (∫ t in u..v, |p * t + q|) ≤ ∫ t in (c - r)..(c + r), |p * t + q| := by
    intro u v hu hv huv
    have hint : IntegrableOn (fun t => |p * t + q|) (Set.Ioc (c - r) (c + r)) volume := by
      have h := intervalIntegrable_iff.mp (hIntP (c - r) (c + r))
      rwa [Set.uIoc_of_le (by linarith : c - r ≤ c + r)] at h
    rw [intervalIntegral.integral_of_le huv,
      intervalIntegral.integral_of_le (by linarith : c - r ≤ c + r)]
    apply setIntegral_mono_set hint
      (Filter.Eventually.of_forall fun t => abs_nonneg _)
    exact Filter.Eventually.of_forall fun _ hx => Set.Ioc_subset_Ioc hu hv hx
  -- Lower bound on the small interval: `∫ |P| ≥ r·M/4`.
  have hlow : r * M / 4 ≤ ∫ t in (c - r)..(c + r), |p * t + q| := by
    rcases hε1 with rfl | rfl
    · refine (hkey (c + r / 2) (c + r) (by linarith) (by ring) ?_).trans
        (hsubset (c + r / 2) (c + r) (by linarith) (by linarith) (by linarith))
      intro t ht
      rw [ht₀def, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    · refine (hkey (c - r) (c - r / 2) (by linarith) (by ring) ?_).trans
        (hsubset (c - r) (c - r / 2) (by linarith) (by linarith) (by linarith))
      intro t ht
      rw [ht₀def, abs_le]
      constructor <;> linarith [ht.1, ht.2]
  -- Upper bound on the big interval: `|P| ≤ R·M` pointwise.
  have hup : ∫ t in (c - R * r)..(c + R * r), |p * t + q| ≤
      2 * (R * r) * (R * M) := by
    have hb : ∀ t ∈ Set.Icc (c - R * r) (c + R * r), |p * t + q| ≤ R * M := by
      intro t ht
      have htc : |t - c| ≤ R * r := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      have e1 : p * t + q = (p * c + q) + p * (t - c) := by ring
      calc |p * t + q| ≤ |p * c + q| + |p * (t - c)| := by rw [e1]; exact abs_add_le _ _
        _ = |p * c + q| + |p| * |t - c| := by rw [abs_mul]
        _ ≤ |p * c + q| + |p| * (R * r) := by
            linarith [mul_le_mul_of_nonneg_left htc (abs_nonneg p)]
        _ ≤ R * M := by
            have h1 : |p| * (R * r) = R * (|p| * r) := by ring
            rw [hM, h1]
            have h2 : |p * c + q| ≤ R * |p * c + q| := by
              nth_rewrite 1 [← one_mul (|p * c + q|)]
              exact mul_le_mul_of_nonneg_right hR (abs_nonneg _)
            linarith
    calc ∫ t in (c - R * r)..(c + R * r), |p * t + q|
        ≤ ∫ _ in (c - R * r)..(c + R * r), (R * M) :=
          intervalIntegral.integral_mono_on (by linarith : c - R * r ≤ c + R * r)
            (hIntP _ _) intervalIntegrable_const hb
      _ = 2 * (R * r) * (R * M) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  -- Convert to averages and combine.
  have havg_small : M / 8 ≤ intervalAvg (fun t => |p * t + q|) (c - r) (c + r) := by
    rw [intervalAvg, show (c + r) - (c - r) = 2 * r by ring,
      le_div_iff₀ (mul_pos two_pos hr)]
    calc M / 8 * (2 * r) = r * M / 4 := by ring
      _ ≤ ∫ t in (c - r)..(c + r), |p * t + q| := hlow
  have havg_big : intervalAvg (fun t => |p * t + q|) (c - R * r) (c + R * r) ≤ R * M := by
    rw [intervalAvg, show (c + R * r) - (c - R * r) = 2 * (R * r) by ring,
      div_le_iff₀ (mul_pos two_pos hRr)]
    calc ∫ t in (c - R * r)..(c + R * r), |p * t + q| ≤ 2 * (R * r) * (R * M) := hup
      _ = R * M * (2 * (R * r)) := by ring
  calc intervalAvg (fun t => |p * t + q|) (c - R * r) (c + R * r) ≤ R * M := havg_big
    _ = 8 * R * (M / 8) := by ring
    _ ≤ 8 * R * intervalAvg (fun t => |p * t + q|) (c - r) (c + r) :=
        mul_le_mul_of_nonneg_left havg_small (by linarith : (0 : ℝ) ≤ 8 * R)

/-- **Lemma (Crude Beta Bound)**: for `h` increasing, `β_h(I) ≤ 1` for every
interval `I`. -/
theorem crude_beta_bound (h : ℝ → ℝ) (hh : StrictMono h)
    (a b : ℝ) (hab : a < b) :
    beta h a b ≤ 1 := by
  have hab' : 0 < b - a := sub_pos.mpr hab
  have hhab : 0 < h b - h a := sub_pos.mpr (hh hab)
  have hM : 0 < (b - a) * (h b - h a) := mul_pos hab' hhab
  -- The endpoint affine map `A(t) = κt + τ` agreeing with `h` at `a` and `b`.
  set κ := (h b - h a) / (b - a) with hκ_def
  have hκ : 0 ≤ κ := div_nonneg hhab.le hab'.le
  set τ := h a - κ * a with hτ_def
  -- `A` maps `[a, b]` into `[h a, h b]`.
  have hA_mem : ∀ t ∈ Set.Icc a b, κ * t + τ ∈ Set.Icc (h a) (h b) := by
    intro t ht
    have heq : κ * t + τ = h a + κ * (t - a) := by ring
    rw [heq]
    have ht0 : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have ht1 : t - a ≤ b - a := by linarith [ht.2]
    have hle : κ * (t - a) ≤ h b - h a := by
      rw [hκ_def, div_mul_eq_mul_div, div_le_iff₀ hab']
      exact mul_le_mul_of_nonneg_left ht1 hhab.le
    constructor <;> linarith [mul_nonneg hκ ht0]
  -- Both `h(t)` and `A(t)` lie in `[h a, h b]`, hence `|h - A| ≤ |h(I)|`.
  have hbound : ∀ t ∈ Set.Icc a b, |h t - (κ * t + τ)| ≤ h b - h a := by
    intro t ht
    have h1 : h a ≤ h t := hh.monotone ht.1
    have h2 : h t ≤ h b := hh.monotone ht.2
    have hA := hA_mem t ht
    rw [abs_le]
    constructor <;> linarith [hA.1, hA.2]
  -- Integrability of the integrand.
  have hInt : IntervalIntegrable (fun t => |h t - (κ * t + τ)|) volume a b := by
    have hi1 : IntervalIntegrable h volume a b := hh.monotone.intervalIntegrable
    have hi2 : IntervalIntegrable (fun t => κ * t + τ) volume a b :=
      ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
    exact (hi1.sub hi2).abs
  -- Integrate: `∫ |h - A| ≤ |I| · |h(I)|`.
  have hint : ∫ t in a..b, |h t - (κ * t + τ)| ≤ (b - a) * (h b - h a) := by
    calc ∫ t in a..b, |h t - (κ * t + τ)|
        ≤ ∫ _ in a..b, (h b - h a) :=
          intervalIntegral.integral_mono_on hab.le hInt intervalIntegrable_const
            (fun t ht => hbound t ht)
      _ = (b - a) * (h b - h a) := by
          rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  -- Divide by `|I| · |h(I)|`.
  have hr0 : ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| ≤ 1 := by
    have hmul := mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hM.le)
    rwa [inv_mul_cancel₀ hM.ne'] at hmul
  have hr0_nonneg : 0 ≤ ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| :=
    mul_nonneg (inv_nonneg.mpr hM.le)
      (intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _))
  -- `β_h(I)` is the infimum over all affine maps, hence is at most this value.
  have hbdd : BddBelow { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
      r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| } :=
    ⟨0, fun _ ⟨_, _, hr, _⟩ => hr⟩
  have hmem : ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| ∈
      { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
        r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| } :=
    ⟨κ, τ, hr0_nonneg, rfl⟩
  exact (csInf_le hbdd hmem).trans hr0

/-- **Lemma (`L²`–`L¹` Comparison)**: if `A_opt(t) = κt + τ` attains the
infimum in `β_h(I)`, then
`⨍_I |L_I - A_opt| ≤ 4 |h(I)| β_h(I)`. -/
theorem l2_l1_comparison (h : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hh : StrictMono h) (κ τ : ℝ)
    (hopt : ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)| =
      beta h a b) :
    intervalAvg (fun t => |l2Proj h a b t - (κ * t + τ)|) a b ≤
      4 * (h b - h a) * beta h a b := by
  -- Basic nonvanishing facts.
  have hb0 : (b - a : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hy : (0 : ℝ) < (b - a) / 2 := by linarith [sub_pos.mpr hab]
  have hy0 : ((b - a) / 2 : ℝ) ≠ 0 := ne_of_gt hy
  have hy3 : ((b - a) / 2 : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hy0
  have hdh : (0 : ℝ) < h b - h a := sub_pos.mpr (hh hab)
  have hM : (0 : ℝ) < (b - a) * (h b - h a) := mul_pos (sub_pos.mpr hab) hdh
  -- Integrability.
  have h_int : IntervalIntegrable h volume a b := hh.monotone.intervalIntegrable
  have hA_int : IntervalIntegrable (fun t : ℝ => κ * t + τ) volume a b :=
    ((continuous_const.mul continuous_id').add continuous_const).intervalIntegrable _ _
  have f_int : IntervalIntegrable (fun t : ℝ => h t - (κ * t + τ)) volume a b :=
    h_int.sub hA_int
  have hid : IntervalIntegrable (fun t : ℝ => t) volume a b :=
    continuous_id'.intervalIntegrable _ _
  have hsc_cont : ContinuousOn (fun s : ℝ => s - (a + b) / 2) (Set.uIcc a b) :=
    (continuous_id'.sub continuous_const).continuousOn
  have hfw_int : IntervalIntegrable
      (fun s : ℝ => (h s - (κ * s + τ)) * (s - (a + b) / 2)) volume a b :=
    f_int.mul_continuousOn hsc_cont
  have hh1_int : IntervalIntegrable
      (fun s : ℝ => h s * (s - (a + b) / 2)) volume a b :=
    h_int.mul_continuousOn hsc_cont
  have hAw_int : IntervalIntegrable
      (fun s : ℝ => (κ * s + τ) * (s - (a + b) / 2)) volume a b :=
    hA_int.mul_continuousOn hsc_cont
  -- Moment integrals of the affine basis functions.
  have Hxc : ∫ t in a..b, (t - (a + b) / 2) = 0 := by
    rw [intervalIntegral.integral_sub hid intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have Hsq : ∫ t in a..b, (t - (a + b) / 2) ^ 2 = (b - a) ^ 3 / 12 := by
    have hExp : (fun t : ℝ => (t - (a + b) / 2) ^ 2) =
        fun t => t ^ 2 - 2 * ((a + b) / 2) * t + ((a + b) / 2) ^ 2 := by
      funext t; ring
    have hsq_int : IntervalIntegrable (fun t : ℝ => t ^ 2) volume a b :=
      (continuous_id'.pow 2).intervalIntegrable _ _
    have hlin_int : IntervalIntegrable (fun t : ℝ => 2 * ((a + b) / 2) * t) volume a b :=
      (continuous_const.mul continuous_id').intervalIntegrable _ _
    rw [hExp, intervalIntegral.integral_add (hsq_int.sub hlin_int) intervalIntegrable_const,
      intervalIntegral.integral_sub hsq_int hlin_int, integral_pow,
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  have HA : ∫ s in a..b, (κ * s + τ) = κ * ((b ^ 2 - a ^ 2) / 2) + τ * (b - a) := by
    have hk : IntervalIntegrable (fun s : ℝ => κ * s) volume a b :=
      (continuous_const.mul continuous_id').intervalIntegrable _ _
    rw [intervalIntegral.integral_add hk intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  have HB : ∫ s in a..b, (κ * s + τ) * (s - (a + b) / 2) = κ * ((b - a) ^ 3 / 12) := by
    have hExp : (fun s : ℝ => (κ * s + τ) * (s - (a + b) / 2)) =
        fun s => κ * (s - (a + b) / 2) ^ 2 +
          (κ * ((a + b) / 2) + τ) * (s - (a + b) / 2) := by
      funext s; ring
    have hp1 : IntervalIntegrable (fun s : ℝ => κ * (s - (a + b) / 2) ^ 2) volume a b :=
      (((continuous_id'.sub continuous_const).pow 2).const_mul κ).intervalIntegrable _ _
    have hp2 : IntervalIntegrable
        (fun s : ℝ => (κ * ((a + b) / 2) + τ) * (s - (a + b) / 2)) volume a b :=
      ((continuous_id'.sub continuous_const).const_mul _).intervalIntegrable _ _
    rw [hExp, intervalIntegral.integral_add hp1 hp2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, Hsq, Hxc]
    ring
  -- The residual `f = h - A` integrals.
  have hJf : ∫ s in a..b, (h s - (κ * s + τ)) =
      (∫ t in a..b, h t) - (κ * ((b ^ 2 - a ^ 2) / 2) + τ * (b - a)) := by
    rw [intervalIntegral.integral_sub h_int hA_int, HA]
  have hExp2 : (fun s : ℝ => (h s - (κ * s + τ)) * (s - (a + b) / 2)) =
      fun s => h s * (s - (a + b) / 2) - (κ * s + τ) * (s - (a + b) / 2) := by
    funext s; ring
  have hJfw : ∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2) =
      (∫ s in a..b, h s * (s - (a + b) / 2)) - κ * ((b - a) ^ 3 / 12) := by
    rw [hExp2, intervalIntegral.integral_sub hh1_int hAw_int, HB]
  -- Step 1: the pointwise identity `L - A = c₀ + B (t - x)`.
  have hId : ∀ t : ℝ, l2Proj h a b t - (κ * t + τ) =
      (∫ s in a..b, (h s - (κ * s + τ))) / (b - a) +
        (3 / (2 * ((b - a) / 2) ^ 3) *
          ∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2)) * (t - (a + b) / 2) := by
    intro t
    unfold l2Proj intervalAvg
    rw [hJf, hJfw]
    field_simp [hb0, hy0, hy3]; ring
  have hInt : ∫ t in a..b, |l2Proj h a b t - (κ * t + τ)| =
      ∫ t in a..b, |(∫ s in a..b, (h s - (κ * s + τ))) / (b - a) +
        (3 / (2 * ((b - a) / 2) ^ 3) *
          ∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2)) * (t - (a + b) / 2)| := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hId t]
  set c₀ : ℝ := (∫ s in a..b, (h s - (κ * s + τ))) / (b - a) with hc₀
  set B : ℝ := 3 / (2 * ((b - a) / 2) ^ 3) *
    ∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2) with hB
  set J : ℝ := ∫ t in a..b, |h t - (κ * t + τ)| with hJdef
  have hK : (0 : ℝ) ≤ 3 / (2 * ((b - a) / 2) ^ 3) := by positivity
  have hJnn : (0 : ℝ) ≤ J :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _)
  -- Step 2: operator norm bound on the affine correction.
  have hB2 : ∫ s in a..b, |(h s - (κ * s + τ)) * (s - (a + b) / 2)| ≤
      ∫ s in a..b, |h s - (κ * s + τ)| * ((b - a) / 2) := by
    apply intervalIntegral.integral_mono_on hab.le hfw_int.abs (f_int.abs.mul_const _)
    intro s hs
    rw [abs_mul]
    have hsc : |s - (a + b) / 2| ≤ (b - a) / 2 := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    exact mul_le_mul_of_nonneg_left hsc (abs_nonneg _)
  have hBabs : |B| ≤ (3 / (2 * ((b - a) / 2) ^ 3)) * (J * ((b - a) / 2)) := by
    rw [hB, abs_mul, abs_of_nonneg hK]
    apply mul_le_mul_of_nonneg_left _ hK
    calc |∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2)|
        ≤ ∫ s in a..b, |(h s - (κ * s + τ)) * (s - (a + b) / 2)| :=
          intervalIntegral.abs_integral_le_integral_abs hab.le
      _ ≤ ∫ s in a..b, |h s - (κ * s + τ)| * ((b - a) / 2) := hB2
      _ = J * ((b - a) / 2) := intervalIntegral.integral_mul_const _ _
  have h2 : (3 / (2 * ((b - a) / 2) ^ 3)) * (J * ((b - a) / 2)) * ((b - a) / 2) ^ 2 =
      (3 / 2) * J := by
    field_simp [hy0, hy3]
  have hBfinal : |B| * ((b - a) / 2) ^ 2 ≤ (3 / 2) * J :=
    (mul_le_mul_of_nonneg_right hBabs (sq_nonneg _)).trans h2.le
  have hc0 : |c₀| * (b - a) ≤ J := by
    have e1 : |c₀| * (b - a) = |∫ s in a..b, (h s - (κ * s + τ))| := by
      rw [hc₀, abs_div, abs_of_pos (sub_pos.mpr hab), div_mul_cancel₀ _ hb0]
    rw [e1]
    exact intervalIntegral.abs_integral_le_integral_abs hab.le
  -- `∫_a^b |t - x| = y²` by splitting at the centre `x`.
  have Habs : ∫ t in a..b, |t - (a + b) / 2| = ((b - a) / 2) ^ 2 := by
    have int_ax : IntervalIntegrable (fun t => |t - (a + b) / 2|) volume a ((a + b) / 2) :=
      ((continuous_id'.sub continuous_const).abs).intervalIntegrable _ _
    have int_xb : IntervalIntegrable (fun t => |t - (a + b) / 2|) volume ((a + b) / 2) b :=
      ((continuous_id'.sub continuous_const).abs).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals int_ax int_xb]
    have hid_ax : IntervalIntegrable (fun t : ℝ => t) volume a ((a + b) / 2) :=
      continuous_id'.intervalIntegrable _ _
    have hid_xb : IntervalIntegrable (fun t : ℝ => t) volume ((a + b) / 2) b :=
      continuous_id'.intervalIntegrable _ _
    have h1 : ∫ t in a..((a + b) / 2), |t - (a + b) / 2| = ((a + b) / 2 - a) ^ 2 / 2 := by
      have hEq : ∫ t in a..((a + b) / 2), |t - (a + b) / 2| =
          ∫ t in a..((a + b) / 2), ((a + b) / 2 - t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht2 : t ≤ (a + b) / 2 := by
          have hu : Set.uIcc a ((a + b) / 2) = Set.Icc a ((a + b) / 2) :=
            Set.uIcc_of_le (by linarith [hab])
          rw [hu] at ht
          exact ht.2
        show |t - (a + b) / 2| = (a + b) / 2 - t
        rw [abs_of_nonpos (sub_nonpos.mpr ht2)]
        ring
      rw [hEq, intervalIntegral.integral_sub intervalIntegrable_const hid_ax,
        intervalIntegral.integral_const, integral_id, smul_eq_mul]
      ring
    have h2' : ∫ t in (a + b) / 2..b, |t - (a + b) / 2| = (b - (a + b) / 2) ^ 2 / 2 := by
      have hEq : ∫ t in (a + b) / 2..b, |t - (a + b) / 2| =
          ∫ t in (a + b) / 2..b, (t - (a + b) / 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht1 : (a + b) / 2 ≤ t := by
          have hu : Set.uIcc ((a + b) / 2) b = Set.Icc ((a + b) / 2) b :=
            Set.uIcc_of_le (by linarith [hab])
          rw [hu] at ht
          exact ht.1
        show |t - (a + b) / 2| = t - (a + b) / 2
        rw [abs_of_nonneg (sub_nonneg.mpr ht1)]
      rw [hEq, intervalIntegral.integral_sub hid_xb intervalIntegrable_const, integral_id,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [h1, h2']
    ring
  have hTri : ∫ t in a..b, |c₀ + B * (t - (a + b) / 2)| ≤
      ∫ t in a..b, (|c₀| + |B| * |t - (a + b) / 2|) := by
    apply intervalIntegral.integral_mono_on hab.le
      ((continuous_const.add
        (continuous_const.mul (continuous_id'.sub continuous_const))).abs.intervalIntegrable _ _)
      ((continuous_const.add
        (continuous_const.mul
          ((continuous_id'.sub continuous_const).abs))).intervalIntegrable _ _)
    intro t _
    calc |c₀ + B * (t - (a + b) / 2)| ≤ |c₀| + |B * (t - (a + b) / 2)| := abs_add_le _ _
      _ = |c₀| + |B| * |t - (a + b) / 2| := by rw [abs_mul]
  have hSplit : ∫ t in a..b, (|c₀| + |B| * |t - (a + b) / 2|) =
      |c₀| * (b - a) + |B| * ((b - a) / 2) ^ 2 := by
    have i1 : IntervalIntegrable (fun _ : ℝ => |c₀|) volume a b := intervalIntegrable_const
    have i2 : IntervalIntegrable (fun t : ℝ => |B| * |t - (a + b) / 2|) volume a b :=
      (continuous_const.mul ((continuous_id'.sub continuous_const).abs)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul, Habs]
    ring
  have htotal : ∫ t in a..b, |l2Proj h a b t - (κ * t + τ)| ≤ (5 / 2) * J := by
    calc ∫ t in a..b, |l2Proj h a b t - (κ * t + τ)|
        = ∫ t in a..b, |c₀ + B * (t - (a + b) / 2)| := hInt
      _ ≤ ∫ t in a..b, (|c₀| + |B| * |t - (a + b) / 2|) := hTri
      _ = |c₀| * (b - a) + |B| * ((b - a) / 2) ^ 2 := hSplit
      _ ≤ J + (3 / 2) * J := add_le_add hc0 hBfinal
      _ = (5 / 2) * J := by ring
  -- Step 3: convert to `β` and compare constants `5/2 ≤ 4`.
  have hbeta : (0 : ℝ) ≤ beta h a b := by
    rw [← hopt]
    exact mul_nonneg (inv_nonneg.mpr hM.le) hJnn
  have hJeq : J = (b - a) * (h b - h a) * beta h a b := by
    have h2' := congrArg (fun z => (b - a) * (h b - h a) * z) hopt
    rwa [mul_inv_cancel_left₀ hM.ne'] at h2'
  have hJdiv : J / (b - a) = (h b - h a) * beta h a b := by
    rw [hJeq]
    field_simp [hb0]
  unfold intervalAvg
  calc (∫ t in a..b, |l2Proj h a b t - (κ * t + τ)|) / (b - a)
      ≤ (5 / 2) * J / (b - a) :=
        (div_le_div_iff_of_pos_right (sub_pos.mpr hab)).mpr htotal
    _ = (5 / 2) * ((h b - h a) * beta h a b) := by rw [mul_div_assoc, hJdiv]
    _ ≤ 4 * (h b - h a) * beta h a b := by
        have hX : (0 : ℝ) ≤ (h b - h a) * beta h a b := mul_nonneg hdh.le hbeta
        linarith [hX]

/-- Auxiliary form of the `L²`–`L¹` comparison (`l2_l1_comparison`), phrased directly in
terms of the raw deviation of an arbitrary affine map rather than through `β_h(I)`; this is what
lets `telescoping_decomposition` use it without an actual (or even near-optimal) minimizer for
the specific interval `I₀`, since only monotonicity of `h` is assumed there. -/
theorem l2_l1_comparison_raw (h : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hh : StrictMono h)
    (κ τ : ℝ) :
    intervalAvg (fun t => |l2Proj h a b t - (κ * t + τ)|) a b ≤
      (5 / 2) * (h b - h a) *
        (((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)|) := by
  -- Basic nonvanishing facts.
  have hb0 : (b - a : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  have hy : (0 : ℝ) < (b - a) / 2 := by linarith [sub_pos.mpr hab]
  have hy0 : ((b - a) / 2 : ℝ) ≠ 0 := ne_of_gt hy
  have hy3 : ((b - a) / 2 : ℝ) ^ 3 ≠ 0 := pow_ne_zero 3 hy0
  have hdh : (0 : ℝ) < h b - h a := sub_pos.mpr (hh hab)
  have hM : (0 : ℝ) < (b - a) * (h b - h a) := mul_pos (sub_pos.mpr hab) hdh
  -- Integrability.
  have h_int : IntervalIntegrable h volume a b := hh.monotone.intervalIntegrable
  have hA_int : IntervalIntegrable (fun t : ℝ => κ * t + τ) volume a b :=
    ((continuous_const.mul continuous_id').add continuous_const).intervalIntegrable _ _
  have f_int : IntervalIntegrable (fun t : ℝ => h t - (κ * t + τ)) volume a b :=
    h_int.sub hA_int
  have hid : IntervalIntegrable (fun t : ℝ => t) volume a b :=
    continuous_id'.intervalIntegrable _ _
  have hsc_cont : ContinuousOn (fun s : ℝ => s - (a + b) / 2) (Set.uIcc a b) :=
    (continuous_id'.sub continuous_const).continuousOn
  have hfw_int : IntervalIntegrable
      (fun s : ℝ => (h s - (κ * s + τ)) * (s - (a + b) / 2)) volume a b :=
    f_int.mul_continuousOn hsc_cont
  have hh1_int : IntervalIntegrable
      (fun s : ℝ => h s * (s - (a + b) / 2)) volume a b :=
    h_int.mul_continuousOn hsc_cont
  have hAw_int : IntervalIntegrable
      (fun s : ℝ => (κ * s + τ) * (s - (a + b) / 2)) volume a b :=
    hA_int.mul_continuousOn hsc_cont
  -- Moment integrals of the affine basis functions.
  have Hxc : ∫ t in a..b, (t - (a + b) / 2) = 0 := by
    rw [intervalIntegral.integral_sub hid intervalIntegrable_const, integral_id,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  have Hsq : ∫ t in a..b, (t - (a + b) / 2) ^ 2 = (b - a) ^ 3 / 12 := by
    have hExp : (fun t : ℝ => (t - (a + b) / 2) ^ 2) =
        fun t => t ^ 2 - 2 * ((a + b) / 2) * t + ((a + b) / 2) ^ 2 := by
      funext t; ring
    have hsq_int : IntervalIntegrable (fun t : ℝ => t ^ 2) volume a b :=
      (continuous_id'.pow 2).intervalIntegrable _ _
    have hlin_int : IntervalIntegrable (fun t : ℝ => 2 * ((a + b) / 2) * t) volume a b :=
      (continuous_const.mul continuous_id').intervalIntegrable _ _
    rw [hExp, intervalIntegral.integral_add (hsq_int.sub hlin_int) intervalIntegrable_const,
      intervalIntegral.integral_sub hsq_int hlin_int, integral_pow,
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  have HA : ∫ s in a..b, (κ * s + τ) = κ * ((b ^ 2 - a ^ 2) / 2) + τ * (b - a) := by
    have hk : IntervalIntegrable (fun s : ℝ => κ * s) volume a b :=
      (continuous_const.mul continuous_id').intervalIntegrable _ _
    rw [intervalIntegral.integral_add hk intervalIntegrable_const,
      intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const,
      smul_eq_mul]
    ring
  have HB : ∫ s in a..b, (κ * s + τ) * (s - (a + b) / 2) = κ * ((b - a) ^ 3 / 12) := by
    have hExp : (fun s : ℝ => (κ * s + τ) * (s - (a + b) / 2)) =
        fun s => κ * (s - (a + b) / 2) ^ 2 +
          (κ * ((a + b) / 2) + τ) * (s - (a + b) / 2) := by
      funext s; ring
    have hp1 : IntervalIntegrable (fun s : ℝ => κ * (s - (a + b) / 2) ^ 2) volume a b :=
      (((continuous_id'.sub continuous_const).pow 2).const_mul κ).intervalIntegrable _ _
    have hp2 : IntervalIntegrable
        (fun s : ℝ => (κ * ((a + b) / 2) + τ) * (s - (a + b) / 2)) volume a b :=
      ((continuous_id'.sub continuous_const).const_mul _).intervalIntegrable _ _
    rw [hExp, intervalIntegral.integral_add hp1 hp2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, Hsq, Hxc]
    ring
  -- The residual `f = h - A` integrals.
  have hJf : ∫ s in a..b, (h s - (κ * s + τ)) =
      (∫ t in a..b, h t) - (κ * ((b ^ 2 - a ^ 2) / 2) + τ * (b - a)) := by
    rw [intervalIntegral.integral_sub h_int hA_int, HA]
  have hExp2 : (fun s : ℝ => (h s - (κ * s + τ)) * (s - (a + b) / 2)) =
      fun s => h s * (s - (a + b) / 2) - (κ * s + τ) * (s - (a + b) / 2) := by
    funext s; ring
  have hJfw : ∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2) =
      (∫ s in a..b, h s * (s - (a + b) / 2)) - κ * ((b - a) ^ 3 / 12) := by
    rw [hExp2, intervalIntegral.integral_sub hh1_int hAw_int, HB]
  -- Step 1: the pointwise identity `L - A = c₀ + B (t - x)`.
  have hId : ∀ t : ℝ, l2Proj h a b t - (κ * t + τ) =
      (∫ s in a..b, (h s - (κ * s + τ))) / (b - a) +
        (3 / (2 * ((b - a) / 2) ^ 3) *
          ∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2)) * (t - (a + b) / 2) := by
    intro t
    unfold l2Proj intervalAvg
    rw [hJf, hJfw]
    field_simp [hb0, hy0, hy3]; ring
  have hInt : ∫ t in a..b, |l2Proj h a b t - (κ * t + τ)| =
      ∫ t in a..b, |(∫ s in a..b, (h s - (κ * s + τ))) / (b - a) +
        (3 / (2 * ((b - a) / 2) ^ 3) *
          ∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2)) * (t - (a + b) / 2)| := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hId t]
  set c₀ : ℝ := (∫ s in a..b, (h s - (κ * s + τ))) / (b - a) with hc₀
  set B : ℝ := 3 / (2 * ((b - a) / 2) ^ 3) *
    ∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2) with hB
  set J : ℝ := ∫ t in a..b, |h t - (κ * t + τ)| with hJdef
  have hK : (0 : ℝ) ≤ 3 / (2 * ((b - a) / 2) ^ 3) := by positivity
  have hJnn : (0 : ℝ) ≤ J :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _)
  -- Step 2: operator norm bound on the affine correction.
  have hB2 : ∫ s in a..b, |(h s - (κ * s + τ)) * (s - (a + b) / 2)| ≤
      ∫ s in a..b, |h s - (κ * s + τ)| * ((b - a) / 2) := by
    apply intervalIntegral.integral_mono_on hab.le hfw_int.abs (f_int.abs.mul_const _)
    intro s hs
    rw [abs_mul]
    have hsc : |s - (a + b) / 2| ≤ (b - a) / 2 := by
      rw [abs_le]
      constructor <;> linarith [hs.1, hs.2]
    exact mul_le_mul_of_nonneg_left hsc (abs_nonneg _)
  have hBabs : |B| ≤ (3 / (2 * ((b - a) / 2) ^ 3)) * (J * ((b - a) / 2)) := by
    rw [hB, abs_mul, abs_of_nonneg hK]
    apply mul_le_mul_of_nonneg_left _ hK
    calc |∫ s in a..b, (h s - (κ * s + τ)) * (s - (a + b) / 2)|
        ≤ ∫ s in a..b, |(h s - (κ * s + τ)) * (s - (a + b) / 2)| :=
          intervalIntegral.abs_integral_le_integral_abs hab.le
      _ ≤ ∫ s in a..b, |h s - (κ * s + τ)| * ((b - a) / 2) := hB2
      _ = J * ((b - a) / 2) := intervalIntegral.integral_mul_const _ _
  have h2 : (3 / (2 * ((b - a) / 2) ^ 3)) * (J * ((b - a) / 2)) * ((b - a) / 2) ^ 2 =
      (3 / 2) * J := by
    field_simp [hy0, hy3]
  have hBfinal : |B| * ((b - a) / 2) ^ 2 ≤ (3 / 2) * J :=
    (mul_le_mul_of_nonneg_right hBabs (sq_nonneg _)).trans h2.le
  have hc0 : |c₀| * (b - a) ≤ J := by
    have e1 : |c₀| * (b - a) = |∫ s in a..b, (h s - (κ * s + τ))| := by
      rw [hc₀, abs_div, abs_of_pos (sub_pos.mpr hab), div_mul_cancel₀ _ hb0]
    rw [e1]
    exact intervalIntegral.abs_integral_le_integral_abs hab.le
  -- `∫_a^b |t - x| = y²` by splitting at the centre `x`.
  have Habs : ∫ t in a..b, |t - (a + b) / 2| = ((b - a) / 2) ^ 2 := by
    have int_ax : IntervalIntegrable (fun t => |t - (a + b) / 2|) volume a ((a + b) / 2) :=
      ((continuous_id'.sub continuous_const).abs).intervalIntegrable _ _
    have int_xb : IntervalIntegrable (fun t => |t - (a + b) / 2|) volume ((a + b) / 2) b :=
      ((continuous_id'.sub continuous_const).abs).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals int_ax int_xb]
    have hid_ax : IntervalIntegrable (fun t : ℝ => t) volume a ((a + b) / 2) :=
      continuous_id'.intervalIntegrable _ _
    have hid_xb : IntervalIntegrable (fun t : ℝ => t) volume ((a + b) / 2) b :=
      continuous_id'.intervalIntegrable _ _
    have h1 : ∫ t in a..((a + b) / 2), |t - (a + b) / 2| = ((a + b) / 2 - a) ^ 2 / 2 := by
      have hEq : ∫ t in a..((a + b) / 2), |t - (a + b) / 2| =
          ∫ t in a..((a + b) / 2), ((a + b) / 2 - t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht2 : t ≤ (a + b) / 2 := by
          have hu : Set.uIcc a ((a + b) / 2) = Set.Icc a ((a + b) / 2) :=
            Set.uIcc_of_le (by linarith [hab])
          rw [hu] at ht
          exact ht.2
        show |t - (a + b) / 2| = (a + b) / 2 - t
        rw [abs_of_nonpos (sub_nonpos.mpr ht2)]
        ring
      rw [hEq, intervalIntegral.integral_sub intervalIntegrable_const hid_ax,
        intervalIntegral.integral_const, integral_id, smul_eq_mul]
      ring
    have h2' : ∫ t in (a + b) / 2..b, |t - (a + b) / 2| = (b - (a + b) / 2) ^ 2 / 2 := by
      have hEq : ∫ t in (a + b) / 2..b, |t - (a + b) / 2| =
          ∫ t in (a + b) / 2..b, (t - (a + b) / 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht1 : (a + b) / 2 ≤ t := by
          have hu : Set.uIcc ((a + b) / 2) b = Set.Icc ((a + b) / 2) b :=
            Set.uIcc_of_le (by linarith [hab])
          rw [hu] at ht
          exact ht.1
        show |t - (a + b) / 2| = t - (a + b) / 2
        rw [abs_of_nonneg (sub_nonneg.mpr ht1)]
      rw [hEq, intervalIntegral.integral_sub hid_xb intervalIntegrable_const, integral_id,
        intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [h1, h2']
    ring
  have hTri : ∫ t in a..b, |c₀ + B * (t - (a + b) / 2)| ≤
      ∫ t in a..b, (|c₀| + |B| * |t - (a + b) / 2|) := by
    apply intervalIntegral.integral_mono_on hab.le
      ((continuous_const.add
        (continuous_const.mul (continuous_id'.sub continuous_const))).abs.intervalIntegrable _ _)
      ((continuous_const.add
        (continuous_const.mul
          ((continuous_id'.sub continuous_const).abs))).intervalIntegrable _ _)
    intro t _
    calc |c₀ + B * (t - (a + b) / 2)| ≤ |c₀| + |B * (t - (a + b) / 2)| := abs_add_le _ _
      _ = |c₀| + |B| * |t - (a + b) / 2| := by rw [abs_mul]
  have hSplit : ∫ t in a..b, (|c₀| + |B| * |t - (a + b) / 2|) =
      |c₀| * (b - a) + |B| * ((b - a) / 2) ^ 2 := by
    have i1 : IntervalIntegrable (fun _ : ℝ => |c₀|) volume a b := intervalIntegrable_const
    have i2 : IntervalIntegrable (fun t : ℝ => |B| * |t - (a + b) / 2|) volume a b :=
      (continuous_const.mul ((continuous_id'.sub continuous_const).abs)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const, smul_eq_mul,
      intervalIntegral.integral_const_mul, Habs]
    ring
  have htotal : ∫ t in a..b, |l2Proj h a b t - (κ * t + τ)| ≤ (5 / 2) * J := by
    calc ∫ t in a..b, |l2Proj h a b t - (κ * t + τ)|
        = ∫ t in a..b, |c₀ + B * (t - (a + b) / 2)| := hInt
      _ ≤ ∫ t in a..b, (|c₀| + |B| * |t - (a + b) / 2|) := hTri
      _ = |c₀| * (b - a) + |B| * ((b - a) / 2) ^ 2 := hSplit
      _ ≤ J + (3 / 2) * J := add_le_add hc0 hBfinal
      _ = (5 / 2) * J := by ring
  -- Convert to the target form, without needing optimality.
  have hγeq : (5 / 2) * (h b - h a) *
      (((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)|) = (5 / 2) * J / (b - a) := by
    rw [← hJdef]
    field_simp
  rw [hγeq]
  unfold intervalAvg
  exact (div_le_div_iff_of_pos_right (sub_pos.mpr hab)).mpr htotal

/-- Interval-integrability of a finite sum, used in `telescoping_decomposition` where the
telescoped decomposition of `h - L_{I_0}` is a sum of `k` affine differences plus two end terms. -/
theorem intervalIntegrable_finsetSum' {n : ℕ} {f : ℕ → ℝ → ℝ} {a b : ℝ}
    (hf : ∀ i ∈ Finset.range n, IntervalIntegrable (f i) volume a b) :
    IntervalIntegrable (fun t => ∑ i ∈ Finset.range n, f i t) volume a b := by
  induction n with
  | zero => simp
  | succ m ih =>
    simp only [Finset.sum_range_succ]
    exact (ih (fun i hi => hf i (Finset.mem_range.mpr
      (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))))).add (hf m (Finset.self_mem_range_succ m))


/-- The normalized deviation
`Δ̃_h(x, y, k) = (|I_k| |h(I_k)|)⁻¹ ∫_{I_k} |h - L_{I₀}|`. -/
def deltaTilde (h : ℝ → ℝ) (x y : ℝ) (k : ℕ) : ℝ :=
  ((2 ^ (k + 1) * y) * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))⁻¹ *
    ∫ t in (x - 2 ^ k * y)..(x + 2 ^ k * y), |h t - l2Proj h (x - y) (x + y) t|

/-- **Lemma (Telescoping Decomposition)**:
`Δ̃_h(x, y, k) ≤ C ∑_{j=0}^k 2^{k-j} β_h(I_j)` with `C` an absolute constant.
Only the monotonicity of `h` is used. -/
theorem telescoping_decomposition :
    ∃ C : ℝ, 0 < C ∧
      ∀ h : ℝ → ℝ, StrictMono h → ∀ x y : ℝ, 0 < y → ∀ k : ℕ,
        deltaTilde h x y k ≤
          C * ∑ j ∈ Finset.range (k + 1), 2 ^ (k - j) * betaPt h x (2 ^ j * y) := by
  obtain ⟨CAG, hCAGpos, hAG⟩ := affine_growth
  refine ⟨1 + 15 * CAG, by positivity, ?_⟩
  intro h hh x y hy k
  set C : ℝ := 1 + 15 * CAG with hCdef
  -- Nested dyadic intervals `I_j = [p j, q j]`.
  set p : ℕ → ℝ := fun j => x - 2 ^ j * y with hpdef
  set q : ℕ → ℝ := fun j => x + 2 ^ j * y with hqdef
  have hlt : ∀ j : ℕ, p j < q j := by
    intro j
    simp only [hpdef, hqdef]
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) j, hy]
  have hlen : ∀ j : ℕ, q j - p j = 2 ^ (j + 1) * y := by
    intro j
    simp only [hpdef, hqdef, pow_succ]
    ring
  have hnest : ∀ j : ℕ, p (j + 1) ≤ p j ∧ q j ≤ q (j + 1) := by
    intro j
    simp only [hpdef, hqdef, pow_succ]
    constructor <;> nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) j, hy]
  have hnest' : ∀ i j : ℕ, i ≤ j → p j ≤ p i ∧ q i ≤ q j := by
    intro i j hij
    induction j with
    | zero => simp [Nat.le_zero.mp hij]
    | succ n ih =>
      rcases Nat.lt_or_ge i (n+1) with h1 | h1
      · obtain ⟨h2, h3⟩ := ih (Nat.lt_succ_iff.mp h1)
        obtain ⟨h4, h5⟩ := hnest n
        exact ⟨h4.trans h2, h3.trans h5⟩
      · have : i = n + 1 := le_antisymm hij h1
        simp [this]
  have hHmono : ∀ i j : ℕ, i ≤ j → h (q i) - h (p i) ≤ h (q j) - h (p j) := by
    intro i j hij
    obtain ⟨h1, h2⟩ := hnest' i j hij
    have := hh.monotone h1
    have := hh.monotone h2
    linarith
  -- `betaPt` and `deltaTilde` in terms of `p, q`.
  have hbP : ∀ j : ℕ, betaPt h x (2 ^ j * y) = beta h (p j) (q j) := fun j => rfl
  have hdT : deltaTilde h x y k = ((q k - p k) * (h (q k) - h (p k)))⁻¹ *
      ∫ t in (p k)..(q k), |h t - l2Proj h (p 0) (q 0) t| := by
    simp only [deltaTilde, hpdef, hqdef, pow_zero, one_mul]
    congr 2
    ring
  -- The set defining `beta h (p j) (q j)` is always nonempty.
  have hSne : ∀ j : ℕ, Set.Nonempty { r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
      r = ((q j - p j) * (h (q j) - h (p j)))⁻¹ * ∫ t in (p j)..(q j), |h t - (κ * t + τ)| } := by
    intro j
    refine ⟨((q j - p j) * (h (q j) - h (p j)))⁻¹ * ∫ t in (p j)..(q j), |h t - (0 * t + 0)|,
      0, 0, ?_, rfl⟩
    have hdh : (0:ℝ) ≤ h (q j) - h (p j) := sub_nonneg.mpr (hh.monotone (hlt j).le)
    have hlj : (0:ℝ) ≤ q j - p j := sub_nonneg.mpr (hlt j).le
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg hlj hdh))
      (intervalIntegral.integral_nonneg (hlt j).le (fun t _ => abs_nonneg _))
  -- For every `η > 0` and `j`, a near-optimal affine map for `I_j`.
  have hex : ∀ η : ℝ, 0 < η → ∀ j : ℕ, ∃ κ τ : ℝ, j ≤ k →
      ((q j - p j) * (h (q j) - h (p j)))⁻¹ * ∫ t in (p j)..(q j), |h t - (κ * t + τ)| ≤
        beta h (p j) (q j) + η := by
    intro η hη j
    by_cases hjk : j ≤ k
    · obtain ⟨a, ⟨κ, τ, -, ha⟩, halt⟩ := exists_lt_of_csInf_lt (hSne j)
        (b := beta h (p j) (q j) + η) (by unfold beta; linarith)
      exact ⟨κ, τ, fun _ => by rw [← ha]; exact halt.le⟩
    · exact ⟨0, 0, fun hc => absurd hc hjk⟩
  -- Reduce to a bound with slack `C * 2^(k+1) * η` for every `η > 0`.
  suffices H : ∀ η : ℝ, 0 < η → deltaTilde h x y k ≤
      C * ∑ j ∈ Finset.range (k + 1), 2 ^ (k - j) * betaPt h x (2 ^ j * y) +
        C * ((k:ℝ) + 1) * 2 ^ k * η by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hCk : (0:ℝ) < C * ((k:ℝ) + 1) * 2 ^ k + 1 := by positivity
    have := H (ε / (C * ((k:ℝ) + 1) * 2 ^ k + 1)) (by positivity)
    refine this.trans ?_
    have hle : C * ((k:ℝ) + 1) * 2 ^ k * (ε / (C * ((k:ℝ) + 1) * 2 ^ k + 1)) ≤ ε := by
      have hkey : C * ((k:ℝ) + 1) * 2 ^ k * (ε / (C * ((k:ℝ) + 1) * 2 ^ k + 1)) +
          ε / (C * ((k:ℝ) + 1) * 2 ^ k + 1) = ε := by field_simp
      nlinarith [hkey, div_nonneg hε.le hCk.le]
    linarith [hle]
  intro η hη
  choose κ τ hκτ using hex η hη
  set A : ℕ → ℝ → ℝ := fun j t => κ j * t + τ j with hAdef
  have hAcont : ∀ j : ℕ, Continuous (A j) := fun j =>
    (continuous_const.mul continuous_id').add continuous_const
  have hL0cont : Continuous (l2Proj h (p 0) (q 0)) := by
    unfold l2Proj; fun_prop
  have hhint : ∀ a b : ℝ, IntervalIntegrable h volume a b :=
    fun a b => hh.monotone.intervalIntegrable
  -- The pointwise telescoping identity and triangle inequality.
  have hptw : ∀ t : ℝ, |h t - l2Proj h (p 0) (q 0) t| ≤
      |h t - A k t| + (∑ i ∈ Finset.range k, |A (i + 1) t - A i t|) +
        |A 0 t - l2Proj h (p 0) (q 0) t| := by
    intro t
    have hid : h t - l2Proj h (p 0) (q 0) t =
        (h t - A k t) + (∑ i ∈ Finset.range k, (A (i + 1) t - A i t)) +
          (A 0 t - l2Proj h (p 0) (q 0) t) := by
      rw [Finset.sum_range_sub (fun i => A i t) k]
      ring
    rw [hid]
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    exact (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
  -- Integrate over `I_k`.
  have hintL0 : IntervalIntegrable (fun t => |h t - l2Proj h (p 0) (q 0) t|) volume (p k) (q k) :=
    ((hhint _ _).sub (hL0cont.intervalIntegrable _ _)).abs
  have hintRHS : IntervalIntegrable (fun t => |h t - A k t| +
      (∑ i ∈ Finset.range k, |A (i + 1) t - A i t|) + |A 0 t - l2Proj h (p 0) (q 0) t|)
      volume (p k) (q k) := by
    refine ((((hhint _ _).sub ((hAcont k).intervalIntegrable _ _)).abs).add ?_).add
      (((hAcont 0).intervalIntegrable _ _).sub (hL0cont.intervalIntegrable _ _)).abs
    exact intervalIntegrable_finsetSum'
      (fun i _ => (((hAcont (i+1)).intervalIntegrable _ _).sub
        ((hAcont i).intervalIntegrable _ _)).abs)
  have hstepInt : ∫ t in (p k)..(q k), |h t - l2Proj h (p 0) (q 0) t| ≤
      (∫ t in (p k)..(q k), |h t - A k t|) +
        (∑ i ∈ Finset.range k, ∫ t in (p k)..(q k), |A (i + 1) t - A i t|) +
        ∫ t in (p k)..(q k), |A 0 t - l2Proj h (p 0) (q 0) t| := by
    calc ∫ t in (p k)..(q k), |h t - l2Proj h (p 0) (q 0) t|
        ≤ ∫ t in (p k)..(q k), (|h t - A k t| +
            (∑ i ∈ Finset.range k, |A (i + 1) t - A i t|) +
            |A 0 t - l2Proj h (p 0) (q 0) t|) :=
          intervalIntegral.integral_mono_on (hlt k).le hintL0 hintRHS (fun t _ => hptw t)
      _ = (∫ t in (p k)..(q k), |h t - A k t|) +
            (∫ t in (p k)..(q k), ∑ i ∈ Finset.range k, |A (i + 1) t - A i t|) +
            ∫ t in (p k)..(q k), |A 0 t - l2Proj h (p 0) (q 0) t| := by
          rw [intervalIntegral.integral_add, intervalIntegral.integral_add]
          · exact ((hhint _ _).sub ((hAcont k).intervalIntegrable _ _)).abs
          · exact intervalIntegrable_finsetSum'
              (fun i _ => (((hAcont (i+1)).intervalIntegrable _ _).sub
                ((hAcont i).intervalIntegrable _ _)).abs)
          · refine (((hhint _ _).sub ((hAcont k).intervalIntegrable _ _)).abs).add ?_
            exact intervalIntegrable_finsetSum'
              (fun i _ => (((hAcont (i+1)).intervalIntegrable _ _).sub
                ((hAcont i).intervalIntegrable _ _)).abs)
          · exact ((hAcont 0).intervalIntegrable _ _).sub (hL0cont.intervalIntegrable _ _) |>.abs
      _ = (∫ t in (p k)..(q k), |h t - A k t|) +
            (∑ i ∈ Finset.range k, ∫ t in (p k)..(q k), |A (i + 1) t - A i t|) +
            ∫ t in (p k)..(q k), |A 0 t - l2Proj h (p 0) (q 0) t| := by
          rw [intervalIntegral.integral_finsetSum]
          exact fun i _ => (((hAcont (i+1)).intervalIntegrable _ _).sub
            ((hAcont i).intervalIntegrable _ _)).abs
  -- The exact/near-optimal bound for each interval `I_j`, `j ≤ k`.
  have hLHpos : ∀ j : ℕ, 0 < (q j - p j) * (h (q j) - h (p j)) := fun j =>
    mul_pos (sub_pos.mpr (hlt j)) (sub_pos.mpr (hh (hlt j)))
  have hΔbound : ∀ j : ℕ, j ≤ k → ∫ t in (p j)..(q j), |h t - A j t| ≤
      (beta h (p j) (q j) + η) * ((q j - p j) * (h (q j) - h (p j))) := by
    intro j hjk
    have hb := hκτ j hjk
    rw [inv_mul_le_iff₀ (hLHpos j)] at hb
    simp only [hAdef]
    linarith [hb]
  -- Step A (`j = k`, exact).
  have hstepA : ∫ t in (p k)..(q k), |h t - A k t| ≤
      (beta h (p k) (q k) + η) * ((q k - p k) * (h (q k) - h (p k))) :=
    hΔbound k le_rfl
  -- Step B: the `I_i`-scale bound on the telescoping terms, `i < k`.
  have hLratio : ∀ i : ℕ, q (i + 1) - p (i + 1) = 2 * (q i - p i) := by
    intro i; rw [hlen, hlen]; ring
  have hstepB : ∀ i : ℕ, i < k → ∫ t in (p i)..(q i), |A (i + 1) t - A i t| ≤
      (q i - p i) * (2 * (h (q (i + 1)) - h (p (i + 1))) * (beta h (p (i + 1)) (q (i + 1)) + η) +
        (h (q i) - h (p i)) * (beta h (p i) (q i) + η)) := by
    intro i hik
    have hikk : i + 1 ≤ k := hik
    have hik' : i ≤ k := le_of_lt hik
    have hAint : ∀ j : ℕ, IntervalIntegrable (A j) volume (p i) (q i) :=
      fun j => (hAcont j).intervalIntegrable _ _
    have hhinti : IntervalIntegrable h volume (p i) (q i) := hhint _ _
    have hptw2 : ∀ t : ℝ, |A (i + 1) t - A i t| ≤ |h t - A (i + 1) t| + |h t - A i t| := by
      intro t
      have e : A (i + 1) t - A i t = (h t - A i t) - (h t - A (i + 1) t) := by ring
      calc |A (i + 1) t - A i t| = |(h t - A i t) - (h t - A (i + 1) t)| := by rw [e]
        _ ≤ |h t - A i t| + |h t - A (i + 1) t| := abs_sub _ _
        _ = |h t - A (i + 1) t| + |h t - A i t| := by ring
    have hnest2 : p (i + 1) ≤ p i ∧ q i ≤ q (i + 1) := hnest i
    have hstep1 : ∫ t in (p i)..(q i), |A (i + 1) t - A i t| ≤
        (∫ t in (p i)..(q i), |h t - A (i + 1) t|) + ∫ t in (p i)..(q i), |h t - A i t| := by
      calc ∫ t in (p i)..(q i), |A (i + 1) t - A i t|
          ≤ ∫ t in (p i)..(q i), (|h t - A (i + 1) t| + |h t - A i t|) :=
            intervalIntegral.integral_mono_on (hlt i).le
              ((hAint (i+1)).sub (hAint i)).abs
              (((hhinti.sub (hAint (i+1))).abs).add ((hhinti.sub (hAint i)).abs))
              (fun t _ => hptw2 t)
        _ = (∫ t in (p i)..(q i), |h t - A (i + 1) t|) + ∫ t in (p i)..(q i), |h t - A i t| := by
            rw [intervalIntegral.integral_add ((hhinti.sub (hAint (i+1))).abs)
              ((hhinti.sub (hAint i)).abs)]
    have hstep2 : ∫ t in (p i)..(q i), |h t - A (i + 1) t| ≤
        ∫ t in (p (i+1))..(q (i+1)), |h t - A (i + 1) t| :=
      intervalIntegral.integral_mono_interval hnest2.1 (hlt i).le hnest2.2
        (Filter.Eventually.of_forall (fun t => abs_nonneg _))
        (((hhint (p (i+1)) (q (i+1))).sub ((hAcont (i+1)).intervalIntegrable _ _)).abs)
    have hb1 : ∫ t in (p (i+1))..(q (i+1)), |h t - A (i + 1) t| ≤
        (beta h (p (i+1)) (q (i+1)) + η) * ((q (i+1) - p (i+1)) * (h (q (i+1)) - h (p (i+1)))) :=
      hΔbound (i+1) hikk
    have hb2 : ∫ t in (p i)..(q i), |h t - A i t| ≤
        (beta h (p i) (q i) + η) * ((q i - p i) * (h (q i) - h (p i))) :=
      hΔbound i hik'
    have hratio := hLratio i
    calc ∫ t in (p i)..(q i), |A (i + 1) t - A i t|
        ≤ (∫ t in (p i)..(q i), |h t - A (i + 1) t|) + ∫ t in (p i)..(q i), |h t - A i t| :=
          hstep1
      _ ≤ (∫ t in (p (i+1))..(q (i+1)), |h t - A (i + 1) t|) +
            ∫ t in (p i)..(q i), |h t - A i t| := add_le_add hstep2 le_rfl
      _ ≤ (beta h (p (i+1)) (q (i+1)) + η) * ((q (i+1) - p (i+1)) * (h (q (i+1)) - h (p (i+1)))) +
            (beta h (p i) (q i) + η) * ((q i - p i) * (h (q i) - h (p i))) :=
          add_le_add hb1 hb2
      _ = (q i - p i) * (2 * (h (q (i + 1)) - h (p (i + 1))) * (beta h (p (i + 1)) (q (i + 1)) + η) +
            (h (q i) - h (p i)) * (beta h (p i) (q i) + η)) := by rw [hratio]; ring
  -- Transfer any `I_i`-scale average bound on an affine function to the `I_k` scale.
  have haffine : ∀ (κ' τ' : ℝ) (i : ℕ), i ≤ k →
      intervalAvg (fun t => |κ' * t + τ'|) (p k) (q k) ≤
        CAG * 2 ^ (k - i) * intervalAvg (fun t => |κ' * t + τ'|) (p i) (q i) := by
    intro κ' τ' i hik
    have hRr : (2 : ℝ) ^ (k - i) * (2 ^ i * y) = 2 ^ k * y := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hik]
    have e1 : p k = x - 2 ^ (k - i) * (2 ^ i * y) := by rw [hRr]
    have e2 : q k = x + 2 ^ (k - i) * (2 ^ i * y) := by rw [hRr]
    rw [e1, e2, show p i = x - 2 ^ i * y from rfl, show q i = x + 2 ^ i * y from rfl]
    exact hAG κ' τ' x (2 ^ i * y) (2 ^ (k - i)) (by positivity) (one_le_pow₀ (by norm_num))
  -- Transfer Step B to the `I_k` scale.
  have hstepBk : ∀ i : ℕ, i < k → ∫ t in (p k)..(q k), |A (i + 1) t - A i t| ≤
      (q k - p k) * (CAG * 2 ^ (k - i) *
        (2 * (h (q (i + 1)) - h (p (i + 1))) * (beta h (p (i + 1)) (q (i + 1)) + η) +
          (h (q i) - h (p i)) * (beta h (p i) (q i) + η))) := by
    intro i hik
    have hik' : i ≤ k := le_of_lt hik
    have hAiAvg : intervalAvg (fun t => |A (i + 1) t - A i t|) (p i) (q i) ≤
        2 * (h (q (i + 1)) - h (p (i + 1))) * (beta h (p (i + 1)) (q (i + 1)) + η) +
          (h (q i) - h (p i)) * (beta h (p i) (q i) + η) := by
      rw [intervalAvg, div_le_iff₀ (sub_pos.mpr (hlt i))]
      linarith [hstepB i hik]
    have heq : (fun t => |(κ (i + 1) - κ i) * t + (τ (i + 1) - τ i)|) =
        (fun t => |A (i + 1) t - A i t|) := by
      funext t; simp only [hAdef]; congr 1; ring
    have htransfer := haffine (κ (i + 1) - κ i) (τ (i + 1) - τ i) i hik'
    rw [heq] at htransfer
    have hcomb := htransfer.trans (mul_le_mul_of_nonneg_left hAiAvg (by positivity))
    rw [intervalAvg, div_le_iff₀ (sub_pos.mpr (hlt k))] at hcomb
    linarith [hcomb]
  -- Transfer the `L²-L¹` bound to the `I_k` scale.
  have hstep0k : ∫ t in (p k)..(q k), |A 0 t - l2Proj h (p 0) (q 0) t| ≤
      (q k - p k) * (CAG * 2 ^ k * ((5 / 2) * (h (q 0) - h (p 0)) * (beta h (p 0) (q 0) + η))) := by
    set M0 : ℝ := 3 / (2 * ((q 0 - p 0) / 2) ^ 3) * ∫ s in (p 0)..(q 0), h s * (s - (p 0 + q 0) / 2)
      with hM0def
    set κ'' : ℝ := κ 0 - M0 with hκ''def
    set τ'' : ℝ := τ 0 - intervalAvg h (p 0) (q 0) + M0 * ((p 0 + q 0) / 2) with hτ''def
    have heqfun : (fun t => |κ'' * t + τ''|) = (fun t => |A 0 t - l2Proj h (p 0) (q 0) t|) := by
      funext t
      simp only [hAdef, l2Proj, hκ''def, hτ''def, hM0def]
      congr 1
      ring
    have htransfer := haffine κ'' τ'' 0 (Nat.zero_le k)
    rw [Nat.sub_zero, heqfun] at htransfer
    have hraw := l2_l1_comparison_raw h (p 0) (q 0) (hlt 0) hh (κ 0) (τ 0)
    have hγ0 := hκτ 0 (Nat.zero_le k)
    have hHnn0 : (0 : ℝ) ≤ h (q 0) - h (p 0) := sub_nonneg.mpr (hh.monotone (hlt 0).le)
    have hstep0 : intervalAvg (fun t => |A 0 t - l2Proj h (p 0) (q 0) t|) (p 0) (q 0) ≤
        (5 / 2) * (h (q 0) - h (p 0)) * (beta h (p 0) (q 0) + η) := by
      have heq2 : (fun t => |A 0 t - l2Proj h (p 0) (q 0) t|) =
          (fun t => |l2Proj h (p 0) (q 0) t - (κ 0 * t + τ 0)|) := by
        funext t; rw [abs_sub_comm]
      rw [heq2]
      calc intervalAvg (fun t => |l2Proj h (p 0) (q 0) t - (κ 0 * t + τ 0)|) (p 0) (q 0)
          ≤ (5 / 2) * (h (q 0) - h (p 0)) *
              (((q 0 - p 0) * (h (q 0) - h (p 0)))⁻¹ *
                ∫ t in (p 0)..(q 0), |h t - (κ 0 * t + τ 0)|) := hraw
        _ ≤ (5 / 2) * (h (q 0) - h (p 0)) * (beta h (p 0) (q 0) + η) :=
            mul_le_mul_of_nonneg_left hγ0 (by positivity [hHnn0])
    have hcomb := htransfer.trans (mul_le_mul_of_nonneg_left hstep0 (by positivity))
    rw [intervalAvg, div_le_iff₀ (sub_pos.mpr (hlt k))] at hcomb
    linarith [hcomb]
  -- Assemble the three pieces into a bound on the raw integral over `I_k`.
  have hmid : (∑ i ∈ Finset.range k, ∫ t in (p k)..(q k), |A (i + 1) t - A i t|) ≤
      (q k - p k) * (∑ i ∈ Finset.range k, CAG * 2 ^ (k - i) *
        (2 * (h (q (i + 1)) - h (p (i + 1))) * (beta h (p (i + 1)) (q (i + 1)) + η) +
          (h (q i) - h (p i)) * (beta h (p i) (q i) + η))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i hi => hstepBk i (Finset.mem_range.mp hi))
  have hraw : ∫ t in (p k)..(q k), |h t - l2Proj h (p 0) (q 0) t| ≤
      (q k - p k) * ((beta h (p k) (q k) + η) * (h (q k) - h (p k))) +
        (q k - p k) * (∑ i ∈ Finset.range k, CAG * 2 ^ (k - i) *
          (2 * (h (q (i + 1)) - h (p (i + 1))) * (beta h (p (i + 1)) (q (i + 1)) + η) +
            (h (q i) - h (p i)) * (beta h (p i) (q i) + η))) +
        (q k - p k) * (CAG * 2 ^ k * ((5 / 2) * (h (q 0) - h (p 0)) * (beta h (p 0) (q 0) + η))) := by
    refine hstepInt.trans ?_
    have h1 : ∫ t in (p k)..(q k), |h t - A k t| ≤
        (q k - p k) * ((beta h (p k) (q k) + η) * (h (q k) - h (p k))) := by
      linarith [hstepA]
    linarith [h1, hmid, hstep0k]
  -- Normalize by `(q k - p k) * (h (q k) - h (p k))`.
  have hHkpos : (0 : ℝ) < h (q k) - h (p k) := sub_pos.mpr (hh (hlt k))
  set S1 : ℝ := ∑ i ∈ Finset.range k, CAG * 2 ^ (k - i) *
      (2 * (h (q (i + 1)) - h (p (i + 1))) * (beta h (p (i + 1)) (q (i + 1)) + η) +
        (h (q i) - h (p i)) * (beta h (p i) (q i) + η)) with hS1def
  have hqkpk : (q k - p k) ≠ 0 := (sub_pos.mpr (hlt k)).ne'
  have hcancel : ∀ W : ℝ, ((q k - p k) * (h (q k) - h (p k)))⁻¹ * ((q k - p k) * W) =
      (h (q k) - h (p k))⁻¹ * W := fun W => by field_simp
  have hnorm : deltaTilde h x y k ≤
      (beta h (p k) (q k) + η) + (h (q k) - h (p k))⁻¹ * S1 +
        (h (q k) - h (p k))⁻¹ *
          (CAG * 2 ^ k * ((5 / 2) * (h (q 0) - h (p 0)) * (beta h (p 0) (q 0) + η))) := by
    rw [hdT]
    have hstep := mul_le_mul_of_nonneg_left hraw
      (inv_nonneg.mpr (mul_pos (sub_pos.mpr (hlt k)) hHkpos).le)
    refine hstep.trans_eq ?_
    rw [mul_add, mul_add, hcancel, hcancel, hcancel,
      show (h (q k) - h (p k))⁻¹ * ((beta h (p k) (q k) + η) * (h (q k) - h (p k))) =
        beta h (p k) (q k) + η by field_simp]
  -- `beta` is always nonnegative.
  have hβnn : ∀ j : ℕ, 0 ≤ beta h (p j) (q j) := by
    intro j
    unfold beta
    exact Real.sInf_nonneg (fun r ⟨_, _, hr, _⟩ => hr)
  -- Bound the ratios `H_j / H_k ≤ 1` for `j ≤ k`.
  have hHratio : ∀ j : ℕ, j ≤ k → h (q j) - h (p j) ≤ h (q k) - h (p k) := fun j hj => hHmono j k hj
  have hS1bound : (h (q k) - h (p k))⁻¹ * S1 ≤
      ∑ i ∈ Finset.range k, CAG * 2 ^ (k - i) *
        (2 * (beta h (p (i + 1)) (q (i + 1)) + η) + (beta h (p i) (q i) + η)) := by
    rw [hS1def, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hik : i < k := Finset.mem_range.mp hi
    have hHi1 : h (q (i+1)) - h (p (i+1)) ≤ h (q k) - h (p k) := hHratio (i+1) hik
    have hHi : h (q i) - h (p i) ≤ h (q k) - h (p k) := hHratio i hik.le
    have hβη1 : (0:ℝ) ≤ beta h (p (i+1)) (q (i+1)) + η := by linarith [hβnn (i+1)]
    have hβη0 : (0:ℝ) ≤ beta h (p i) (q i) + η := by linarith [hβnn i]
    have hratio1 : (h (q k) - h (p k))⁻¹ * (h (q (i+1)) - h (p (i+1))) ≤ 1 := by
      rw [inv_mul_le_iff₀ hHkpos]; linarith [hHi1]
    have hratio0 : (h (q k) - h (p k))⁻¹ * (h (q i) - h (p i)) ≤ 1 := by
      rw [inv_mul_le_iff₀ hHkpos]; linarith [hHi]
    calc (h (q k) - h (p k))⁻¹ * (CAG * 2 ^ (k - i) *
        (2 * (h (q (i + 1)) - h (p (i + 1))) * (beta h (p (i + 1)) (q (i + 1)) + η) +
          (h (q i) - h (p i)) * (beta h (p i) (q i) + η)))
        = CAG * 2 ^ (k - i) * (2 * ((h (q k) - h (p k))⁻¹ * (h (q (i+1)) - h (p (i+1)))) *
            (beta h (p (i+1)) (q (i+1)) + η) +
          ((h (q k) - h (p k))⁻¹ * (h (q i) - h (p i))) * (beta h (p i) (q i) + η)) := by
          field_simp
      _ ≤ CAG * 2 ^ (k - i) * (2 * 1 * (beta h (p (i+1)) (q (i+1)) + η) + 1 * (beta h (p i) (q i) + η)) := by
          gcongr
      _ = CAG * 2 ^ (k - i) * (2 * (beta h (p (i+1)) (q (i+1)) + η) + (beta h (p i) (q i) + η)) := by
          ring
  -- The last (`j = 0`) term.
  have hlastbound : (h (q k) - h (p k))⁻¹ *
      (CAG * 2 ^ k * ((5 / 2) * (h (q 0) - h (p 0)) * (beta h (p 0) (q 0) + η))) ≤
      CAG * 2 ^ k * ((5 / 2) * (beta h (p 0) (q 0) + η)) := by
    have hH0 : h (q 0) - h (p 0) ≤ h (q k) - h (p k) := hHratio 0 (Nat.zero_le k)
    have hratio0 : (h (q k) - h (p k))⁻¹ * (h (q 0) - h (p 0)) ≤ 1 := by
      rw [inv_mul_le_iff₀ hHkpos]; linarith [hH0]
    have hβη0' : (0:ℝ) ≤ beta h (p 0) (q 0) + η := by linarith [hβnn 0]
    calc (h (q k) - h (p k))⁻¹ *
        (CAG * 2 ^ k * ((5 / 2) * (h (q 0) - h (p 0)) * (beta h (p 0) (q 0) + η)))
        = CAG * 2 ^ k * (5 / 2) * ((h (q k) - h (p k))⁻¹ * (h (q 0) - h (p 0))) *
            (beta h (p 0) (q 0) + η) := by field_simp
      _ ≤ CAG * 2 ^ k * (5 / 2) * 1 * (beta h (p 0) (q 0) + η) := by gcongr
      _ = CAG * 2 ^ k * ((5 / 2) * (beta h (p 0) (q 0) + η)) := by ring
  -- Combine into a bound in terms of the raw `beta`'s (still with slack `η`).
  have hcomb2 : deltaTilde h x y k ≤
      (beta h (p k) (q k) + η) +
        (∑ i ∈ Finset.range k, CAG * 2 ^ (k - i) *
          (2 * (beta h (p (i + 1)) (q (i + 1)) + η) + (beta h (p i) (q i) + η))) +
        CAG * 2 ^ k * ((5 / 2) * (beta h (p 0) (q 0) + η)) := by
    calc deltaTilde h x y k
        ≤ (beta h (p k) (q k) + η) + (h (q k) - h (p k))⁻¹ * S1 +
            (h (q k) - h (p k))⁻¹ *
              (CAG * 2 ^ k * ((5 / 2) * (h (q 0) - h (p 0)) * (beta h (p 0) (q 0) + η))) := hnorm
      _ ≤ (beta h (p k) (q k) + η) +
            (∑ i ∈ Finset.range k, CAG * 2 ^ (k - i) *
              (2 * (beta h (p (i + 1)) (q (i + 1)) + η) + (beta h (p i) (q i) + η))) +
            CAG * 2 ^ k * ((5 / 2) * (beta h (p 0) (q 0) + η)) :=
          add_le_add (add_le_add le_rfl hS1bound) hlastbound
  -- Reindex and combine into the master sum `∑_{j=0}^k 2^{k-j} (beta_j + η)`.
  set T : ℝ := ∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (k - j) * (beta h (p j) (q j) + η) with hTdef
  have hTnn : ∀ j ∈ Finset.range (k + 1), (0:ℝ) ≤ (2:ℝ) ^ (k - j) * (beta h (p j) (q j) + η) :=
    fun j _ => mul_nonneg (by positivity) (by linarith [hβnn j])
  have hextend : ∀ n : ℕ, n ≤ k → (2:ℝ) ^ (k - n) * (beta h (p n) (q n) + η) ≤ T := by
    intro n hn
    exact Finset.single_le_sum hTnn (Finset.mem_range.mpr (by omega))
  have hextendk : (beta h (p k) (q k) + η) ≤ T := by
    have := hextend k le_rfl
    simpa using this
  have hextend0 : (2:ℝ) ^ k * (beta h (p 0) (q 0) + η) ≤ T := by
    have := hextend 0 (Nat.zero_le k)
    simpa using this
  -- The second half of the middle sum.
  have hmid2 : (∑ i ∈ Finset.range k, (2:ℝ) ^ (k - i) * (beta h (p i) (q i) + η)) ≤ T := by
    rw [hTdef, Finset.sum_range_succ]
    have : (0:ℝ) ≤ (2:ℝ) ^ (k - k) * (beta h (p k) (q k) + η) :=
      mul_nonneg (by positivity) (by linarith [hβnn k])
    linarith [this]
  -- The first half of the middle sum, via reindexing.
  have hmid1 : (∑ i ∈ Finset.range k, (2:ℝ) ^ (k - i) * (beta h (p (i + 1)) (q (i + 1)) + η)) ≤
      2 * T := by
    set g : ℕ → ℝ := fun j => (2:ℝ) ^ (k - j + 1) * (beta h (p j) (q j) + η) with hgdef
    have heq1 : ∑ i ∈ Finset.range k, (2:ℝ) ^ (k - i) * (beta h (p (i + 1)) (q (i + 1)) + η) =
        ∑ i ∈ Finset.range k, g (i + 1) := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hshift : k - (i + 1) + 1 = k - i := by
        have hik : i < k := Finset.mem_range.mp hi
        omega
      simp only [hgdef, hshift]
    rw [heq1]
    have hsplit := Finset.sum_range_succ' g k
    have hg0nn : (0:ℝ) ≤ g 0 := by
      simp only [hgdef]
      exact mul_nonneg (by positivity) (by linarith [hβnn 0])
    have hle : ∑ i ∈ Finset.range k, g (i + 1) ≤ ∑ j ∈ Finset.range (k + 1), g j := by
      rw [hsplit]; linarith [hg0nn]
    refine hle.trans ?_
    have heq2 : ∑ j ∈ Finset.range (k + 1), g j = 2 * T := by
      rw [hTdef, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hgdef]
      rw [pow_succ]
      ring
    rw [heq2]
  -- Conclude.
  have hCeq : C = 1 + 15 * CAG := hCdef
  have hCpos : (0:ℝ) < C := by rw [hCeq]; positivity
  calc deltaTilde h x y k
      ≤ (beta h (p k) (q k) + η) +
          (∑ i ∈ Finset.range k, CAG * 2 ^ (k - i) *
            (2 * (beta h (p (i + 1)) (q (i + 1)) + η) + (beta h (p i) (q i) + η))) +
          CAG * 2 ^ k * ((5 / 2) * (beta h (p 0) (q 0) + η)) := hcomb2
    _ = (beta h (p k) (q k) + η) +
          (2 * CAG * ∑ i ∈ Finset.range k, (2:ℝ) ^ (k - i) * (beta h (p (i+1)) (q (i+1)) + η) +
            CAG * ∑ i ∈ Finset.range k, (2:ℝ) ^ (k - i) * (beta h (p i) (q i) + η)) +
          CAG * (2 ^ k * ((5 / 2) * (beta h (p 0) (q 0) + η))) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        congr 1
        · congr 1
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        · ring
    _ ≤ T + (2 * CAG * (2 * T) + CAG * T) + CAG * ((5/2) * T) := by
        have e0 : CAG * ((2:ℝ) ^ k * ((5 / 2) * (beta h (p 0) (q 0) + η))) =
            CAG * ((5 / 2) * ((2:ℝ) ^ k * (beta h (p 0) (q 0) + η))) := by ring
        rw [e0]
        have t1 := hextendk
        have t2 : 2 * CAG * (∑ i ∈ Finset.range k, (2:ℝ) ^ (k - i) *
            (beta h (p (i + 1)) (q (i + 1)) + η)) ≤ 2 * CAG * (2 * T) :=
          mul_le_mul_of_nonneg_left hmid1 (by positivity)
        have t3 : CAG * (∑ i ∈ Finset.range k, (2:ℝ) ^ (k - i) * (beta h (p i) (q i) + η)) ≤
            CAG * T := mul_le_mul_of_nonneg_left hmid2 hCAGpos.le
        have t4 : CAG * ((5 / 2) * ((2:ℝ) ^ k * (beta h (p 0) (q 0) + η))) ≤
            CAG * ((5 / 2) * T) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hextend0 (by norm_num)) hCAGpos.le
        linarith [t1, t2, t3, t4]
    _ = (1 + 15/2 * CAG) * T := by ring
    _ ≤ C * T := by
        rw [hCeq]; nlinarith [hTnn, mul_nonneg (Finset.sum_nonneg hTnn) hCAGpos.le,
          Finset.sum_nonneg hTnn]
    _ ≤ C * ∑ j ∈ Finset.range (k + 1), 2 ^ (k - j) * betaPt h x (2 ^ j * y) +
          C * ((k:ℝ) + 1) * 2 ^ k * η := by
        rw [hTdef]
        have heq3 : ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * (beta h (p j) (q j) + η) =
            (∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * betaPt h x (2 ^ j * y)) +
              η * ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hbP j]
          ring
        rw [heq3, mul_add]
        have hgeom : ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) ≤ ((k:ℝ) + 1) * 2 ^ k := by
          calc ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j)
              ≤ ∑ _j ∈ Finset.range (k + 1), (2:ℝ) ^ k :=
                Finset.sum_le_sum (fun j _ => pow_le_pow_right₀ (by norm_num) (Nat.sub_le k j))
            _ = ((k:ℝ) + 1) * 2 ^ k := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
                push_cast
                ring
        have hCη : C * (η * ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j)) ≤
            C * ((k:ℝ) + 1) * 2 ^ k * η := by
          have h1 : η * ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) ≤ η * (((k:ℝ) + 1) * 2 ^ k) :=
            mul_le_mul_of_nonneg_left hgeom hη.le
          have h2 := mul_le_mul_of_nonneg_left h1 hCpos.le
          have h3 : C * (η * (((k:ℝ) + 1) * 2 ^ k)) = C * ((k:ℝ) + 1) * 2 ^ k * η := by ring
          linarith [h2, h3]
        linarith [hCη]



/-! ## Section 5.4: the pointwise bound by `Θ_h` -/

/-- **Poisson decay on dyadic annuli**: for `t` with `|t - x| ≥ 2^{k-1} y`,
`P_z(t) ≤ C 4^{-k} y⁻¹`. -/
theorem poisson_annulus_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : ℝ, 0 < y → ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ,
        (2 : ℝ) ^ (k - 1) * y ≤ |t - x| →
          poissonKernelUHP ((x : ℂ) + (y : ℂ) * Complex.I) t ≤ C / ((4 : ℝ) ^ k * y) := by
  refine ⟨4 / Real.pi, by positivity, ?_⟩
  intro x y hy k hk t htx
  have hre : ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by simp
  have him : ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  unfold poissonKernelUHP
  rw [hre, him]
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have h0 : (0:ℝ) ≤ (2:ℝ) ^ (k - 1) * y := by positivity
  have hsq : ((2:ℝ) ^ (k - 1) * y) ^ 2 ≤ (t - x) ^ 2 := by
    have hpow := pow_le_pow_left₀ h0 htx 2
    rwa [sq_abs] at hpow
  have hpow4 : ((2:ℝ) ^ (k - 1)) ^ 2 = (4:ℝ) ^ (k - 1) := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, mul_comm]
  have hdenombound : (4:ℝ) ^ (k - 1) * y ^ 2 ≤ (t - x) ^ 2 := by
    calc (4:ℝ) ^ (k - 1) * y ^ 2 = ((2:ℝ) ^ (k - 1)) ^ 2 * y ^ 2 := by rw [hpow4]
      _ = ((2:ℝ) ^ (k - 1) * y) ^ 2 := by ring
      _ ≤ (t - x) ^ 2 := hsq
  have hk4 : (4:ℝ) ^ k = (4:ℝ) ^ (k - 1) * 4 := by
    conv_lhs => rw [← Nat.sub_add_cancel hk]
    rw [pow_succ]
  have hc_pos : (0:ℝ) < Real.pi * ((4:ℝ) ^ (k - 1) * y ^ 2) := by positivity
  have hle_denom : Real.pi * ((4:ℝ) ^ (k - 1) * y ^ 2) ≤ Real.pi * ((t - x) ^ 2 + y ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith [hdenombound, sq_nonneg y]) hpi.le
  have hstep : y / (Real.pi * ((t - x) ^ 2 + y ^ 2)) ≤
      y / (Real.pi * ((4:ℝ) ^ (k - 1) * y ^ 2)) :=
    div_le_div_of_nonneg_left hy.le hc_pos hle_denom
  have heq : y / (Real.pi * ((4:ℝ) ^ (k - 1) * y ^ 2)) = 4 / Real.pi / ((4:ℝ) ^ k * y) := by
    rw [hk4]
    have h4 : ((4:ℝ) ^ (k - 1)) ≠ 0 := by positivity
    field_simp
  rwa [heq] at hstep

/-- Weighted dyadic sum exchange: for a nonnegative sequence `a`,
`∑_{k=0}^n 4^{-k} ∑_{j=0}^k 2^{k-j} a_j ≤ 2 ∑_{j=0}^n 4^{-j} a_j`. -/
theorem weighted_dyadic_sum_le (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (4 : ℝ)⁻¹ ^ k *
        ∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (k - j) * a j ≤
      2 * ∑ j ∈ Finset.range (n + 1), (4 : ℝ)⁻¹ ^ j * a j := by
  have hTmono : ∀ m : ℕ, (∑ j ∈ Finset.range (m + 1), (4:ℝ)⁻¹ ^ j * a j) ≤
      ∑ j ∈ Finset.range (m + 1 + 1), (4:ℝ)⁻¹ ^ j * a j := by
    intro m
    have hpeel : (∑ j ∈ Finset.range (m + 1 + 1), (4:ℝ)⁻¹ ^ j * a j) =
        (∑ j ∈ Finset.range (m + 1), (4:ℝ)⁻¹ ^ j * a j) + (4:ℝ)⁻¹ ^ (m+1) * a (m+1) :=
      Finset.sum_range_succ _ _
    rw [hpeel]
    have : (0:ℝ) ≤ (4:ℝ)⁻¹ ^ (m+1) * a (m+1) := mul_nonneg (by positivity) (ha (m+1))
    linarith
  have hSrec : ∀ m : ℕ,
      (∑ k ∈ Finset.range (m + 1 + 1), (4:ℝ)⁻¹ ^ k *
          ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * a j) =
        (1/2) * (∑ k ∈ Finset.range (m + 1), (4:ℝ)⁻¹ ^ k *
          ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * a j) +
          (∑ j ∈ Finset.range (m + 1 + 1), (4:ℝ)⁻¹ ^ j * a j) := by
    intro m
    have herec : ∀ i : ℕ,
        (4:ℝ)⁻¹ ^ (i + 1) * (∑ j ∈ Finset.range (i + 1 + 1), (2:ℝ) ^ (i + 1 - j) * a j) =
          (1/2) * ((4:ℝ)⁻¹ ^ i * ∑ j ∈ Finset.range (i + 1), (2:ℝ) ^ (i - j) * a j) +
            (4:ℝ)⁻¹ ^ (i + 1) * a (i + 1) := by
      intro i
      rw [Finset.sum_range_succ]
      have hterm : (2:ℝ) ^ (i + 1 - (i + 1)) = 1 := by simp
      rw [hterm, one_mul]
      have hsum_eq : (∑ j ∈ Finset.range (i + 1), (2:ℝ) ^ (i + 1 - j) * a j) =
          2 * ∑ j ∈ Finset.range (i + 1), (2:ℝ) ^ (i - j) * a j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hexp : i + 1 - j = (i - j) + 1 := by omega
        rw [hexp, pow_succ]
        ring
      rw [hsum_eq]
      ring
    have hLHSpeel := Finset.sum_range_succ'
      (fun k => (4:ℝ)⁻¹ ^ k * ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * a j) (m + 1)
    have hRHSpeel := Finset.sum_range_succ' (fun j => (4:ℝ)⁻¹ ^ j * a j) (m + 1)
    rw [hLHSpeel, hRHSpeel]
    have hsum2 : (∑ i ∈ Finset.range (m + 1), (4:ℝ)⁻¹ ^ (i + 1) *
        ∑ j ∈ Finset.range (i + 1 + 1), (2:ℝ) ^ (i + 1 - j) * a j) =
        ∑ i ∈ Finset.range (m + 1), ((1/2) * ((4:ℝ)⁻¹ ^ i *
            ∑ j ∈ Finset.range (i + 1), (2:ℝ) ^ (i - j) * a j) + (4:ℝ)⁻¹ ^ (i + 1) * a (i + 1)) :=
      Finset.sum_congr rfl (fun i _ => herec i)
    rw [hsum2, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hc0 : (∑ j ∈ Finset.range (0 + 1), (2:ℝ) ^ (0 - j) * a j) = a 0 := by simp
    rw [hc0]
    ring
  induction n with
  | zero =>
    norm_num
    linarith [ha 0]
  | succ n ih =>
    rw [hSrec n]
    have h2 : (1/2:ℝ) * (∑ k ∈ Finset.range (n + 1), (4:ℝ)⁻¹ ^ k *
        ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * a j) ≤
        (1/2) * (2 * ∑ j ∈ Finset.range (n + 1), (4:ℝ)⁻¹ ^ j * a j) :=
      mul_le_mul_of_nonneg_left ih (by norm_num)
    have h3 := hTmono n
    linarith [h2, h3]

/-- Finite induction combining a base-interval bound and per-annulus bounds into a bound
on the integral of `f` over the dyadic interval `I_n = [x - 2^n y, x + 2^n y]`. -/
theorem dyadic_integral_induction (f : ℝ → ℝ) (x y : ℝ) (bound : ℕ → ℝ)
    (hfInt : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hbase : (∫ t in (x - y)..(x + y), f t) ≤ bound 0)
    (hann : ∀ k : ℕ, 1 ≤ k →
      (∫ t in (x - 2 ^ k * y)..(x - 2 ^ (k - 1) * y), f t) +
        (∫ t in (x + 2 ^ (k - 1) * y)..(x + 2 ^ k * y), f t) ≤ bound k) :
    ∀ n : ℕ, (∫ t in (x - 2 ^ n * y)..(x + 2 ^ n * y), f t) ≤ ∑ k ∈ Finset.range (n + 1), bound k := by
  intro n
  induction n with
  | zero => simpa using hbase
  | succ n ih =>
    have hann' := hann (n + 1) (Nat.le_add_left 1 n)
    have hkm1 : (n + 1) - 1 = n := by omega
    rw [hkm1] at hann'
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals
      (hfInt (x - 2 ^ (n + 1) * y) (x - 2 ^ n * y)) (hfInt (x - 2 ^ n * y) (x + 2 ^ (n + 1) * y))
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals
      (hfInt (x - 2 ^ n * y) (x + 2 ^ n * y)) (hfInt (x + 2 ^ n * y) (x + 2 ^ (n + 1) * y))
    rw [Finset.sum_range_succ]
    linarith only [hsplit1, hsplit2, ih, hann']

/-- If a nonnegative, locally integrable `f` has all its dyadic partial integrals
bounded by a fixed constant `I`, then `f` is integrable on all of `ℝ` and `∫ f ≤ I`. -/
theorem integral_le_of_dyadic_bound (f : ℝ → ℝ) (x y : ℝ) (hy : 0 < y) (I : ℝ)
    (hfInt : ∀ a b : ℝ, IntervalIntegrable f volume a b)
    (hfnonneg : ∀ t : ℝ, 0 ≤ f t)
    (hIn : ∀ n : ℕ, (∫ t in (x - 2 ^ n * y)..(x + 2 ^ n * y), f t) ≤ I) :
    (∫ t, f t) ≤ I := by
  have ha_tendsto : Filter.Tendsto (fun n : ℕ => x - 2 ^ n * y) Filter.atTop Filter.atBot := by
    rw [Filter.tendsto_atBot]
    intro b
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((x - b) / y) (show (1:ℝ) < 2 by norm_num)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have h2 : (2:ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hlt : (x - b) / y < 2 ^ n := lt_of_lt_of_le hN h2
    rw [div_lt_iff₀ hy] at hlt
    linarith only [hlt]
  have hb_tendsto : Filter.Tendsto (fun n : ℕ => x + 2 ^ n * y) Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro b
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt ((b - x) / y) (show (1:ℝ) < 2 by norm_num)
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have h2 : (2:ℝ) ^ N ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hlt : (b - x) / y < 2 ^ n := lt_of_lt_of_le hN h2
    rw [div_lt_iff₀ hy] at hlt
    linarith only [hlt]
  have hfi : ∀ i : ℕ, IntegrableOn f (Set.Ioc (x - 2 ^ i * y) (x + 2 ^ i * y)) volume :=
    fun i => (hfInt (x - 2 ^ i * y) (x + 2 ^ i * y)).1
  have hnormeq : ∀ i : ℕ,
      (∫ t in (x - 2 ^ i * y)..(x + 2 ^ i * y), ‖f t‖) = ∫ t in (x - 2 ^ i * y)..(x + 2 ^ i * y), f t :=
    fun i => intervalIntegral.integral_congr
      (fun t _ => by rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg t)])
  have hIbound : ∀ i : ℕ, (∫ t in (x - 2 ^ i * y)..(x + 2 ^ i * y), ‖f t‖) ≤ I := by
    intro i; rw [hnormeq i]; exact hIn i
  have hfIntegrable : Integrable f volume :=
    integrable_of_intervalIntegral_norm_bounded I hfi ha_tendsto hb_tendsto
      (Filter.Eventually.of_forall hIbound)
  have htendsto : Filter.Tendsto (fun i : ℕ => ∫ t in (x - 2 ^ i * y)..(x + 2 ^ i * y), f t)
      Filter.atTop (nhds (∫ t, f t)) :=
    intervalIntegral_tendsto_integral hfIntegrable ha_tendsto hb_tendsto
  exact le_of_tendsto' htendsto hIn

/-- **Proposition (Forward Inequality to Beta Deviation)**: for a
`ρ`-quasisymmetric increasing homeomorphism `h` and `z = x + iy ∈ 𝕌`,
`|μ_{e(h)}(z)| ≤ C(ρ) Θ_h(x, y)`. -/
theorem forward_to_theta (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ h : ℝ → ℝ, Quasisymmetric h ρ → ∀ x y : ℝ, 0 < y →
        ‖complexDilatation (douadyEarle h) (x + y * Complex.I)‖ ≤
          C * Theta h x y := by
  obtain ⟨Cfwd, hCfwdpos, hfwd⟩ := forward_inequality ρ hρ
  obtain ⟨cS, CS, hcSpos, _, hSlope⟩ := l2ProjSlope_comparable ρ hρ
  obtain ⟨cDE, CDE, hcDEpos, hcDEleCDE, hDEloc⟩ := de_localization ρ hρ
  have hCDEpos : (0:ℝ) < CDE := lt_of_lt_of_le hcDEpos hcDEleCDE
  obtain ⟨cD, hcDpos, hDenom⟩ := denominator_lower_bounds ρ hρ
  obtain ⟨Cpois, hCpoispos, hpois⟩ := poisson_annulus_bound
  obtain ⟨Ctel, hCtelpos, htel⟩ := telescoping_decomposition
  set Cann : ℝ := max (4 / (cDE * Real.pi)) (4 * CDE * Cpois / cD ^ 2) with hCanndef
  have hCannpos : (0:ℝ) < Cann := by rw [hCanndef]; positivity
  refine ⟨Cfwd * Cann * 2 * Ctel, by positivity, ?_⟩
  intro h hqsh x y hy
  have hh : StrictMono h := hqsh.1
  have hcont : Continuous h := hqsh.2.1
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hzdef
  have hzim : z.im = y := by simp [hzdef]
  have hzre : z.re = x := by simp [hzdef]
  have hzpos : (0:ℝ) < z.im := by rw [hzim]; exact hy
  set w := douadyEarle h z with hwdef
  set L : ℝ := h (x + y) - h (x - y) with hLdef
  have hLpos : (0:ℝ) < L := by
    have := hh (show x - y < x + y by linarith); rw [hLdef]; linarith
  -- Slope and intercept of the `L²` projection `L_{I₀}`.
  set m0 : ℝ := l2ProjSlope h (x - y) (x + y) with hm0def
  have hm0lb : cS * (L / (2 * y)) ≤ m0 := (hSlope h hqsh x y hy).1
  have hm0pos : (0:ℝ) < m0 := lt_of_lt_of_le (by positivity) hm0lb
  set c0 : ℝ := intervalAvg h (x - y) (x + y) with hc0def
  set τ0 : ℝ := c0 - m0 * x with hτ0def
  have hMeq : ∀ t : ℝ, m0 * t + τ0 = l2Proj h (x - y) (x + y) t := by
    intro t
    rw [l2Proj_eq_slope]
    show m0 * t + (c0 - m0 * x) = m0 * (t - (x - y + (x + y)) / 2) + c0
    rw [show (x - y + (x + y)) / 2 = x from by ring]
    ring
  -- Bounds on `v = Im w` from the localization lemma.
  have hvbound := hDEloc h hqsh z hzpos
  rw [hzre, hzim] at hvbound
  have hv1 : cDE * L ≤ w.im := hvbound.1
  have hv2 : w.im ≤ CDE * L := hvbound.2
  have hvpos : (0:ℝ) < w.im := lt_of_lt_of_le (by positivity) hv1
  -- Apply the forward inequality with `M = L_{I₀}`.
  have hbase := hfwd h hqsh z hzpos m0 τ0 hm0pos
  rw [← hwdef] at hbase
  have hintcongr : (fun t : ℝ =>
      2 * w.im * |h t - (m0 * t + τ0)| /
          (‖(h t : ℂ) - star w‖ * ‖(m0 : ℂ) * (t : ℂ) + (τ0 : ℂ) - star w‖) *
        poissonKernelUHP z t) =
      fun t : ℝ =>
        2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
            (‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖) *
          poissonKernelUHP z t := by
    funext t
    rw [← hMeq t]
    push_cast
    ring_nf
  rw [hintcongr] at hbase
  have hwe : douadyEarle h ((x : ℂ) + (y : ℂ) * Complex.I) = w := by rw [← hzdef, hwdef]
  set f : ℝ → ℝ := fun t => 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
      (‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖) *
        poissonKernelUHP z t with hfdef
  -- A real point is always at distance `≥ Im w` from `star w`.
  have hnorm_ge_v : ∀ q : ℝ, w.im ≤ ‖(q : ℂ) - star w‖ := by
    intro q
    have h1 : ((q : ℂ) - star w).im = w.im := by simp
    have h2 : |((q : ℂ) - star w).im| ≤ ‖(q : ℂ) - star w‖ := Complex.abs_im_le_norm _
    rw [h1] at h2
    exact (le_abs_self _).trans h2
  have hnorm_pos : ∀ q : ℝ, (0:ℝ) < ‖(q : ℂ) - star w‖ := fun q => lt_of_lt_of_le hvpos (hnorm_ge_v q)
  have hfnonneg : ∀ t : ℝ, (0:ℝ) ≤ f t := by
    intro t
    rw [hfdef]
    have hp1 := hnorm_pos (h t)
    have hp2 := hnorm_pos (l2Proj h (x - y) (x + y) t)
    have hpk : (0:ℝ) ≤ poissonKernelUHP z t := by
      unfold poissonKernelUHP
      have : (0:ℝ) < z.im := hzpos
      positivity
    have hvnn : (0:ℝ) ≤ w.im := hvpos.le
    positivity
  -- The Poisson kernel is bounded by `1/(π y)` everywhere.
  have hpoisson_global : ∀ t : ℝ, poissonKernelUHP z t ≤ 1 / (Real.pi * y) := by
    intro t
    unfold poissonKernelUHP
    rw [hzre, hzim]
    have hpi : (0:ℝ) < Real.pi := Real.pi_pos
    have hle : Real.pi * y ^ 2 ≤ Real.pi * ((t - x) ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (t - x)]
    have hstep : y / (Real.pi * ((t - x) ^ 2 + y ^ 2)) ≤ y / (Real.pi * y ^ 2) :=
      div_le_div_of_nonneg_left hy.le (by positivity) hle
    have heq : y / (Real.pi * y ^ 2) = 1 / (Real.pi * y) := by
      field_simp
    linarith [hstep, heq.le, heq.ge]
  have hl2cont : Continuous (fun t : ℝ => l2Proj h (x - y) (x + y) t) := by
    unfold l2Proj; fun_prop
  have hfcont_pt : Continuous f := by
    rw [hfdef]
    have hden1 : Continuous (fun t : ℝ => ‖(h t : ℂ) - star w‖) := by fun_prop
    have hden2 : Continuous (fun t : ℝ => ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖) := by fun_prop
    have hnum : Continuous (fun t : ℝ => 2 * w.im * |h t - l2Proj h (x - y) (x + y) t|) := by fun_prop
    have hpoi : Continuous (fun t : ℝ => poissonKernelUHP z t) := by
      unfold poissonKernelUHP
      have hne : ∀ t : ℝ, Real.pi * ((t - z.re) ^ 2 + z.im ^ 2) ≠ 0 := by
        intro t
        have : (0:ℝ) < Real.pi * ((t - z.re) ^ 2 + z.im ^ 2) := by
          have : (0:ℝ) < z.im ^ 2 := by positivity
          have := Real.pi_pos
          nlinarith [sq_nonneg (t - z.re)]
        exact this.ne'
      exact continuous_const.div (by fun_prop) hne
    exact (hnum.div (hden1.mul hden2)
      (fun t => (mul_pos (hnorm_pos (h t)) (hnorm_pos (l2Proj h (x - y) (x + y) t))).ne')).mul hpoi
  have hfIntOn : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b => hfcont_pt.intervalIntegrable a b
  have habsIntOn : ∀ a b : ℝ, IntervalIntegrable (fun t => |h t - l2Proj h (x - y) (x + y) t|) volume a b :=
    fun a b => (hcont.sub hl2cont).abs.intervalIntegrable a b
  set bound : ℕ → ℝ := fun k => Cann * (4:ℝ)⁻¹ ^ k * deltaTilde h x y k with hbounddef
  -- The `k = 0` (base interval `I₀`) bound.
  have hbound0 : (∫ t in (x - y)..(x + y), f t) ≤ bound 0 := by
    have hptwise : ∀ t : ℝ, f t ≤ (2 / (cDE * L * Real.pi * y)) * |h t - l2Proj h (x - y) (x + y) t| := by
      intro t
      rw [hfdef]
      have hD1 : w.im ≤ ‖(h t : ℂ) - star w‖ := hnorm_ge_v (h t)
      have hD2 : w.im ≤ ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖ := hnorm_ge_v _
      have hD1pos := hnorm_pos (h t)
      have hD2pos := hnorm_pos (l2Proj h (x - y) (x + y) t)
      have hvsq_le : w.im * w.im ≤
          ‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖ :=
        mul_le_mul hD1 hD2 hvpos.le hD1pos.le
      have hstep1 : 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
          (‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖) ≤
          2 * w.im * |h t - l2Proj h (x - y) (x + y) t| / (w.im * w.im) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hvsq_le
      have heq1 : 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| / (w.im * w.im) =
          2 * |h t - l2Proj h (x - y) (x + y) t| / w.im := by
        field_simp
      have hstep2 : 2 * |h t - l2Proj h (x - y) (x + y) t| / w.im ≤
          2 * |h t - l2Proj h (x - y) (x + y) t| / (cDE * L) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hv1
      have hpz := hpoisson_global t
      have hpz_nonneg : (0:ℝ) ≤ poissonKernelUHP z t := by
        unfold poissonKernelUHP; have : (0:ℝ) < z.im := hzpos; positivity
      have hfactor_le : 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
          (‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖) ≤
          2 * |h t - l2Proj h (x - y) (x + y) t| / (cDE * L) := by
        calc 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
              (‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖)
            ≤ 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| / (w.im * w.im) := hstep1
          _ = 2 * |h t - l2Proj h (x - y) (x + y) t| / w.im := heq1
          _ ≤ 2 * |h t - l2Proj h (x - y) (x + y) t| / (cDE * L) := hstep2
      calc 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
            (‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖) *
          poissonKernelUHP z t
          ≤ (2 * |h t - l2Proj h (x - y) (x + y) t| / (cDE * L)) * poissonKernelUHP z t :=
            mul_le_mul_of_nonneg_right hfactor_le hpz_nonneg
        _ ≤ (2 * |h t - l2Proj h (x - y) (x + y) t| / (cDE * L)) * (1 / (Real.pi * y)) :=
            mul_le_mul_of_nonneg_left hpz (by positivity)
        _ = 2 / (cDE * L * Real.pi * y) * |h t - l2Proj h (x - y) (x + y) t| := by
            field_simp
    have hmono : (∫ t in (x - y)..(x + y), f t) ≤
        ∫ t in (x - y)..(x + y), (2 / (cDE * L * Real.pi * y)) * |h t - l2Proj h (x - y) (x + y) t| :=
      intervalIntegral.integral_mono_on (by linarith) (hfIntOn _ _)
        ((continuous_const.mul (hcont.sub hl2cont).abs).intervalIntegrable _ _)
        (fun t _ => hptwise t)
    have heq2 : (∫ t in (x - y)..(x + y), (2 / (cDE * L * Real.pi * y)) *
        |h t - l2Proj h (x - y) (x + y) t|) =
        (2 / (cDE * L * Real.pi * y)) * ∫ t in (x - y)..(x + y), |h t - l2Proj h (x - y) (x + y) t| :=
      intervalIntegral.integral_const_mul _ _
    have hdt0 : deltaTilde h x y 0 =
        (2 * y * L)⁻¹ * ∫ t in (x - y)..(x + y), |h t - l2Proj h (x - y) (x + y) t| := by
      show ((2 ^ (0+1) * y) * (h (x + 2^0*y) - h (x - 2^0*y)))⁻¹ *
          ∫ t in (x - 2^0*y)..(x + 2^0*y), |h t - l2Proj h (x - y) (x + y) t| =
          (2 * y * L)⁻¹ * ∫ t in (x - y)..(x + y), |h t - l2Proj h (x - y) (x + y) t|
      norm_num [hLdef]
    have hJ_eq : (∫ t in (x - y)..(x + y), |h t - l2Proj h (x - y) (x + y) t|) =
        2 * y * L * deltaTilde h x y 0 := by
      rw [hdt0]; field_simp
    rw [hbounddef]
    show (∫ t in (x - y)..(x + y), f t) ≤ Cann * (4:ℝ)⁻¹ ^ (0:ℕ) * deltaTilde h x y 0
    rw [pow_zero, mul_one]
    calc (∫ t in (x - y)..(x + y), f t)
        ≤ (2 / (cDE * L * Real.pi * y)) * ∫ t in (x - y)..(x + y), |h t - l2Proj h (x - y) (x + y) t| := by
          rw [← heq2]; exact hmono
      _ = (2 / (cDE * L * Real.pi * y)) * (2 * y * L * deltaTilde h x y 0) := by rw [hJ_eq]
      _ = (4 / (cDE * Real.pi)) * deltaTilde h x y 0 := by field_simp; ring
      _ ≤ Cann * deltaTilde h x y 0 := by
          have hCge : 4 / (cDE * Real.pi) ≤ Cann := by rw [hCanndef]; exact le_max_left _ _
          have hdt0nn : (0:ℝ) ≤ deltaTilde h x y 0 := by
            rw [hdt0]
            have : (0:ℝ) ≤ ∫ t in (x - y)..(x + y), |h t - l2Proj h (x - y) (x + y) t| :=
              intervalIntegral.integral_nonneg (by linarith) (fun t _ => abs_nonneg _)
            positivity
          exact mul_le_mul_of_nonneg_right hCge hdt0nn
  -- The `k ≥ 1` (dyadic annulus) pointwise bound.
  set_option maxHeartbeats 1000000 in
  have hptwise_k : ∀ k : ℕ, 1 ≤ k → ∀ t : ℝ, (2:ℝ) ^ (k - 1) * y ≤ |t - x| → |t - x| ≤ 2 ^ k * y →
      f t ≤ (2 * CDE * Cpois / (cD ^ 2 * 2 ^ k * (4:ℝ) ^ k * y *
          (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) * |h t - l2Proj h (x - y) (x + y) t| := by
    clear Cfwd hCfwdpos hfwd hSlope m0 hm0def hm0lb hm0pos c0 hc0def τ0 hτ0def
      hMeq hbase hintcongr hbound0 bound hbounddef Ctel hCtelpos htel hzre
    intro k hk t ht1 ht2
    have hDk := hDenom h hqsh x y hy k hk t ht1 ht2
    rw [hwe] at hDk
    have hPk := hpois x y hy k hk t ht1
    rw [← hzdef] at hPk
    have hIkpos : (0:ℝ) < h (x + 2 ^ k * y) - h (x - 2 ^ k * y) :=
      sub_pos.mpr (hh (by nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) k, hy]))
    have hD1 : cD * 2 ^ k * L ≤ ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖ := hDk.1
    have hD2 : cD * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)) ≤ ‖(h t : ℂ) - star w‖ := hDk.2
    have hD1pos : (0:ℝ) < cD * 2 ^ k * L := by positivity
    have hD2pos : (0:ℝ) < cD * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)) := by positivity
    rw [hfdef]
    have hprod_le : cD * 2 ^ k * L * (cD * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) ≤
        ‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖ := by
      calc cD * 2 ^ k * L * (cD * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))
          ≤ ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖ *
              (cD * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) :=
            mul_le_mul_of_nonneg_right hD1 hD2pos.le
        _ ≤ ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖ * ‖(h t : ℂ) - star w‖ :=
            mul_le_mul_of_nonneg_left hD2 (hnorm_pos _).le
        _ = ‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖ := by ring
    have hstep1 : 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
        (‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖) ≤
        2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
          (cD * 2 ^ k * L * (cD * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hprod_le
    have heq1 : 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
        (cD * 2 ^ k * L * (cD * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) =
        (2 * w.im / (cD ^ 2 * 2 ^ k * L)) *
          (|h t - l2Proj h (x - y) (x + y) t| / (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) := by
      field_simp
    have hv2' : (2 * w.im / (cD ^ 2 * 2 ^ k * L)) ≤ 2 * CDE / (cD ^ 2 * 2 ^ k) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hcoef : (0:ℝ) ≤ cD ^ 2 * 2 ^ k * 2 := by positivity
      have := mul_le_mul_of_nonneg_left hv2 hcoef
      linarith [this]
    have hfrac_nonneg : (0:ℝ) ≤
        |h t - l2Proj h (x - y) (x + y) t| / (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)) := by positivity
    have hstep2 : (2 * w.im / (cD ^ 2 * 2 ^ k * L)) *
          (|h t - l2Proj h (x - y) (x + y) t| / (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) ≤
        (2 * CDE / (cD ^ 2 * 2 ^ k)) *
          (|h t - l2Proj h (x - y) (x + y) t| / (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) :=
      mul_le_mul_of_nonneg_right hv2' hfrac_nonneg
    have hpz_nonneg : (0:ℝ) ≤ poissonKernelUHP z t := by
      unfold poissonKernelUHP; have : (0:ℝ) < z.im := hzpos; positivity
    calc 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
          (‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖) *
        poissonKernelUHP z t
        ≤ (2 * w.im / (cD ^ 2 * 2 ^ k * L) *
            (|h t - l2Proj h (x - y) (x + y) t| / (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) *
          poissonKernelUHP z t := by
          apply mul_le_mul_of_nonneg_right _ hpz_nonneg
          calc 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
                (‖(h t : ℂ) - star w‖ * ‖(l2Proj h (x - y) (x + y) t : ℂ) - star w‖)
              ≤ 2 * w.im * |h t - l2Proj h (x - y) (x + y) t| /
                  (cD * 2 ^ k * L * (cD * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) := hstep1
            _ = 2 * w.im / (cD ^ 2 * 2 ^ k * L) *
                (|h t - l2Proj h (x - y) (x + y) t| / (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) := heq1
      _ ≤ (2 * CDE / (cD ^ 2 * 2 ^ k) *
            (|h t - l2Proj h (x - y) (x + y) t| / (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) *
          poissonKernelUHP z t :=
          mul_le_mul_of_nonneg_right hstep2 hpz_nonneg
      _ ≤ (2 * CDE / (cD ^ 2 * 2 ^ k) *
            (|h t - l2Proj h (x - y) (x + y) t| / (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) *
          (Cpois / ((4:ℝ) ^ k * y)) :=
          mul_le_mul_of_nonneg_left hPk (by positivity)
      _ = 2 * CDE * Cpois / (cD ^ 2 * 2 ^ k * (4:ℝ) ^ k * y *
            (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) * |h t - l2Proj h (x - y) (x + y) t| := by
          field_simp
  clear hSlope hcSpos m0 hm0def hm0lb hm0pos c0 hc0def τ0 hτ0def hMeq
    hintcongr hDEloc hvbound hv1 hv2 hvpos hcDEpos hcDEleCDE
  -- Nonnegativity and crude bound for beta-numbers, needed for summability of `Θ_h`.
  have ha_nonneg : ∀ j : ℕ, 0 ≤ betaPt h x (2 ^ j * y) := by
    intro j
    unfold betaPt beta
    exact Real.sInf_nonneg (fun r ⟨_, _, hr, _⟩ => hr)
  have habove : ∀ j : ℕ, betaPt h x (2 ^ j * y) ≤ 1 := by
    intro j
    have hlt : x - 2 ^ j * y < x + 2 ^ j * y := by
      have hpj := pow_pos (show (0:ℝ) < 2 by norm_num) j
      nlinarith only [hpj, hy]
    exact crude_beta_bound h hh (x - 2 ^ j * y) (x + 2 ^ j * y) hlt
  have hsummable : Summable (fun j : ℕ => (4:ℝ)⁻¹ ^ j * betaPt h x (2 ^ j * y)) := by
    refine Summable.of_nonneg_of_le (f := fun j : ℕ => (4:ℝ)⁻¹ ^ j) ?_ ?_ ?_
    · exact fun j => mul_nonneg (by positivity) (ha_nonneg j)
    · exact fun j => by
        nlinarith only [habove j, pow_nonneg (show (0:ℝ) ≤ (4:ℝ)⁻¹ by norm_num) j, ha_nonneg j]
    · exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hTheta_ge : ∀ n : ℕ,
      ∑ j ∈ Finset.range (n + 1), (4:ℝ)⁻¹ ^ j * betaPt h x (2 ^ j * y) ≤ Theta h x y := by
    intro n
    have heq : Theta h x y = ∑' j : ℕ, (4:ℝ)⁻¹ ^ j * betaPt h x (2 ^ j * y) := by
      unfold Theta
      congr 1
      funext j
      rw [one_div]
    rw [heq]
    exact hsummable.sum_le_tsum (Finset.range (n + 1))
      (fun j _ => mul_nonneg (by positivity) (ha_nonneg j))
  -- Integrate the per-annulus (and base) pointwise bounds to control `bound k` by `Θ_h`'s terms.
  have hbk : ∀ k : ℕ, bound k ≤
      Cann * Ctel * ((4:ℝ)⁻¹ ^ k *
        ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * betaPt h x (2 ^ j * y)) := by
    intro k
    rw [hbounddef]
    show Cann * (4:ℝ)⁻¹ ^ k * deltaTilde h x y k ≤ _
    have hstep := mul_le_mul_of_nonneg_left (htel h hh x y hy k)
      (show (0:ℝ) ≤ Cann * (4:ℝ)⁻¹ ^ k by positivity)
    calc Cann * (4:ℝ)⁻¹ ^ k * deltaTilde h x y k
        ≤ Cann * (4:ℝ)⁻¹ ^ k *
            (Ctel * ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * betaPt h x (2 ^ j * y)) := hstep
      _ = Cann * Ctel * ((4:ℝ)⁻¹ ^ k *
            ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * betaPt h x (2 ^ j * y)) := by ring
  have hbound_sum : ∀ n : ℕ,
      ∑ k ∈ Finset.range (n + 1), bound k ≤ Cann * Ctel * 2 * Theta h x y := by
    intro n
    have hstep1 : ∑ k ∈ Finset.range (n + 1), bound k ≤
        Cann * Ctel * ∑ k ∈ Finset.range (n + 1),
          ((4:ℝ)⁻¹ ^ k * ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * betaPt h x (2 ^ j * y)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun k _ => hbk k)
    have hstep2 := weighted_dyadic_sum_le (fun j => betaPt h x (2 ^ j * y)) ha_nonneg n
    have hstep2' : Cann * Ctel * ∑ k ∈ Finset.range (n + 1),
          ((4:ℝ)⁻¹ ^ k * ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * betaPt h x (2 ^ j * y)) ≤
        Cann * Ctel * (2 * ∑ j ∈ Finset.range (n + 1), (4:ℝ)⁻¹ ^ j * betaPt h x (2 ^ j * y)) :=
      mul_le_mul_of_nonneg_left hstep2 (by positivity)
    have hstep3 := hTheta_ge n
    calc ∑ k ∈ Finset.range (n + 1), bound k
        ≤ Cann * Ctel * ∑ k ∈ Finset.range (n + 1),
            ((4:ℝ)⁻¹ ^ k * ∑ j ∈ Finset.range (k + 1), (2:ℝ) ^ (k - j) * betaPt h x (2 ^ j * y)) := hstep1
      _ ≤ Cann * Ctel * (2 * ∑ j ∈ Finset.range (n + 1), (4:ℝ)⁻¹ ^ j * betaPt h x (2 ^ j * y)) := hstep2'
      _ ≤ Cann * Ctel * (2 * Theta h x y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hstep3 (by norm_num)) (by positivity)
      _ = Cann * Ctel * 2 * Theta h x y := by ring
  -- The two annuli making up `I_k ∖ I_{k-1}` (for `k ≥ 1`) contribute at most `bound k`.
  clear ha_nonneg habove hsummable hTheta_ge hbk htel hCtelpos hfwd hqsh
    hfdef habsIntOn hnorm_ge_v hnorm_pos hpoisson_global hzim hzre hzpos
    hwe hLdef hLpos
  set_option maxHeartbeats 1000000 in
  have hannulus : ∀ k : ℕ, 1 ≤ k →
      (∫ t in (x - 2 ^ k * y)..(x - 2 ^ (k - 1) * y), f t) +
        (∫ t in (x + 2 ^ (k - 1) * y)..(x + 2 ^ k * y), f t) ≤ bound k := by
    intro k hk
    have hpow_mono : (2:ℝ) ^ (k - 1) ≤ 2 ^ k := by
      apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
      omega
    have hb1a1 : x - 2 ^ k * y ≤ x - 2 ^ (k - 1) * y := by nlinarith only [hpow_mono, hy]
    have ha2b2 : x + 2 ^ (k - 1) * y ≤ x + 2 ^ k * y := by nlinarith only [hpow_mono, hy]
    have hIkpos : (0:ℝ) < h (x + 2 ^ k * y) - h (x - 2 ^ k * y) :=
      sub_pos.mpr (hh (by nlinarith only [pow_pos (show (0:ℝ) < 2 by norm_num) k, hy]))
    set g : ℝ → ℝ := fun t => (2 * CDE * Cpois / (cD ^ 2 * 2 ^ k * (4:ℝ) ^ k * y *
        (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) * |h t - l2Proj h (x - y) (x + y) t| with hgdef
    have hgIntOn : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
      intro a b
      rw [hgdef]
      exact (continuous_const.mul (hcont.sub hl2cont).abs).intervalIntegrable a b
    have hleft_le : (∫ t in (x - 2 ^ k * y)..(x - 2 ^ (k - 1) * y), f t) ≤
        ∫ t in (x - 2 ^ k * y)..(x - 2 ^ (k - 1) * y), g t := by
      apply intervalIntegral.integral_mono_on hb1a1 (hfIntOn _ _) (hgIntOn _ _)
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      have htx_nonpos : t - x ≤ 0 := by
        nlinarith only [ht2, pow_pos (show (0:ℝ) < 2 by norm_num) (k - 1), hy]
      have habsval : |t - x| = x - t := by rw [abs_of_nonpos htx_nonpos]; ring
      rw [hgdef]
      apply hptwise_k k hk t
      · rw [habsval]; linarith only [ht2]
      · rw [habsval]; linarith only [ht1]
    have hright_le : (∫ t in (x + 2 ^ (k - 1) * y)..(x + 2 ^ k * y), f t) ≤
        ∫ t in (x + 2 ^ (k - 1) * y)..(x + 2 ^ k * y), g t := by
      apply intervalIntegral.integral_mono_on ha2b2 (hfIntOn _ _) (hgIntOn _ _)
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      have htx_nonneg : (0:ℝ) ≤ t - x := by
        nlinarith only [ht1, pow_pos (show (0:ℝ) < 2 by norm_num) (k - 1), hy]
      have habsval : |t - x| = t - x := abs_of_nonneg htx_nonneg
      rw [hgdef]
      apply hptwise_k k hk t
      · rw [habsval]; linarith only [ht1]
      · rw [habsval]; linarith only [ht2]
    have hmid_nonneg : (0:ℝ) ≤ ∫ t in (x - 2 ^ (k - 1) * y)..(x + 2 ^ (k - 1) * y), g t := by
      apply intervalIntegral.integral_nonneg
        (by nlinarith only [pow_pos (show (0:ℝ) < 2 by norm_num) (k - 1), hy])
      intro t _
      rw [hgdef]
      have : (0:ℝ) ≤ 2 * CDE * Cpois / (cD ^ 2 * 2 ^ k * (4:ℝ) ^ k * y *
          (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) := by positivity
      positivity
    have hadj1 : (∫ t in (x - 2 ^ k * y)..(x - 2 ^ (k - 1) * y), g t) +
        (∫ t in (x - 2 ^ (k - 1) * y)..(x + 2 ^ (k - 1) * y), g t) =
        ∫ t in (x - 2 ^ k * y)..(x + 2 ^ (k - 1) * y), g t :=
      intervalIntegral.integral_add_adjacent_intervals (hgIntOn _ _) (hgIntOn _ _)
    have hadj2 : (∫ t in (x - 2 ^ k * y)..(x + 2 ^ (k - 1) * y), g t) +
        (∫ t in (x + 2 ^ (k - 1) * y)..(x + 2 ^ k * y), g t) =
        ∫ t in (x - 2 ^ k * y)..(x + 2 ^ k * y), g t :=
      intervalIntegral.integral_add_adjacent_intervals (hgIntOn _ _) (hgIntOn _ _)
    have houter_le_full : (∫ t in (x - 2 ^ k * y)..(x - 2 ^ (k - 1) * y), g t) +
        (∫ t in (x + 2 ^ (k - 1) * y)..(x + 2 ^ k * y), g t) ≤
        ∫ t in (x - 2 ^ k * y)..(x + 2 ^ k * y), g t := by
      linarith only [hadj1, hadj2, hmid_nonneg]
    have hgfull_eq : (∫ t in (x - 2 ^ k * y)..(x + 2 ^ k * y), g t) =
        (2 * CDE * Cpois / (cD ^ 2 * 2 ^ k * (4:ℝ) ^ k * y *
            (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) *
          ∫ t in (x - 2 ^ k * y)..(x + 2 ^ k * y), |h t - l2Proj h (x - y) (x + y) t| := by
      rw [hgdef]
      exact intervalIntegral.integral_const_mul _ _
    have hdeltatilde_eq : (∫ t in (x - 2 ^ k * y)..(x + 2 ^ k * y), |h t - l2Proj h (x - y) (x + y) t|) =
        (2 ^ (k + 1) * y * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) * deltaTilde h x y k := by
      unfold deltaTilde
      have hCne : (2:ℝ) ^ (k + 1) * y * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)) ≠ 0 := by positivity
      exact (mul_inv_cancel_left₀ hCne _).symm
    have hfinal_eq : (2 * CDE * Cpois / (cD ^ 2 * 2 ^ k * (4:ℝ) ^ k * y *
          (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) *
        ((2 ^ (k + 1) * y * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) * deltaTilde h x y k) =
        (4 * CDE * Cpois / cD ^ 2) * ((4:ℝ)⁻¹ ^ k * deltaTilde h x y k) := by
      rw [inv_pow]
      have hCne : h (x + 2 ^ k * y) - h (x - 2 ^ k * y) ≠ 0 := hIkpos.ne'
      have h2kne : (2:ℝ) ^ k ≠ 0 := by positivity
      have h4kne : (4:ℝ) ^ k ≠ 0 := by positivity
      field_simp
      ring
    have hCann_ge : 4 * CDE * Cpois / cD ^ 2 ≤ Cann := by
      rw [hCanndef]; exact le_max_right _ _
    have hdt_nonneg : (0:ℝ) ≤ deltaTilde h x y k := by
      unfold deltaTilde
      have hint_nonneg : (0:ℝ) ≤
          ∫ t in (x - 2 ^ k * y)..(x + 2 ^ k * y), |h t - l2Proj h (x - y) (x + y) t| :=
        intervalIntegral.integral_nonneg
          (by nlinarith only [pow_pos (show (0:ℝ) < 2 by norm_num) k, hy]) (fun t _ => abs_nonneg _)
      positivity
    calc (∫ t in (x - 2 ^ k * y)..(x - 2 ^ (k - 1) * y), f t) +
          (∫ t in (x + 2 ^ (k - 1) * y)..(x + 2 ^ k * y), f t)
        ≤ (∫ t in (x - 2 ^ k * y)..(x - 2 ^ (k - 1) * y), g t) +
            (∫ t in (x + 2 ^ (k - 1) * y)..(x + 2 ^ k * y), g t) := add_le_add hleft_le hright_le
      _ ≤ ∫ t in (x - 2 ^ k * y)..(x + 2 ^ k * y), g t := houter_le_full
      _ = (2 * CDE * Cpois / (cD ^ 2 * 2 ^ k * (4:ℝ) ^ k * y *
              (h (x + 2 ^ k * y) - h (x - 2 ^ k * y)))) *
            ((2 ^ (k + 1) * y * (h (x + 2 ^ k * y) - h (x - 2 ^ k * y))) * deltaTilde h x y k) := by
          rw [hgfull_eq, hdeltatilde_eq]
      _ = (4 * CDE * Cpois / cD ^ 2) * ((4:ℝ)⁻¹ ^ k * deltaTilde h x y k) := hfinal_eq
      _ ≤ Cann * ((4:ℝ)⁻¹ ^ k * deltaTilde h x y k) :=
          mul_le_mul_of_nonneg_right hCann_ge (by positivity)
      _ = bound k := by rw [hbounddef]; show _ = Cann * (4:ℝ)⁻¹ ^ k * deltaTilde h x y k; ring
  -- Finite induction: the integral over `I_n` is bounded by the partial sum of `bound`.
  clear hDenom hpois hCpoispos
  have hIn_le := dyadic_integral_induction f x y bound hfIntOn hbound0 hannulus
  have hIntfinal : (∫ t, f t) ≤ Cann * Ctel * 2 * Theta h x y :=
    integral_le_of_dyadic_bound f x y hy _ hfIntOn hfnonneg
      (fun i => (hIn_le i).trans (hbound_sum i))
  calc ‖complexDilatation (douadyEarle h) z‖
      ≤ Cfwd * (Cann * Ctel * 2 * Theta h x y) :=
        hbase.trans (mul_le_mul_of_nonneg_left hIntfinal hCfwdpos.le)
    _ = Cfwd * Cann * 2 * Ctel * Theta h x y := by ring

end VanishingCarleson

end
