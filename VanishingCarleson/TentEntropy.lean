/-
# The tent expansion and the entropy inequality (Sections 6 and 7)

The normalised second difference `ε_h`, the tent expansion of `β_h` and its
squared form; the entropy defect `D_w`, the quantity `E_h`, the entropy
inequality, its Carleson corollary and the two bounds for `E_h`:

* Definition (Normalised second difference) — `eps`
* Lemma (Tent expansion)                    — `tent_expansion`
* Lemma (Squared form)                      — `tent_squared`
* Definition (Entropy defect)               — `entropyDefect`, `entropyBound`
* Lemma (Entropy inequality)                — `entropy_inequality`
* Corollary (Carleson bound for `ε_h`)      — `eps_carleson_bound`
* Lemma (Two bounds for `E_h`)              — `entropy_bound_ainfty`, `entropy_bound_bmo`
-/
import Mathlib
import VanishingCarleson.BetaTheta

open MeasureTheory Real Set

noncomputable section

namespace VanishingCarleson

/-! ## Section 6: the tent expansion -/

/-- **Definition (Normalised second difference)**:
`ε_h(x, y) = (h(x+y) + h(x-y) - 2h(x)) / (h(x+y) - h(x-y)) ∈ (-1, 1)`. -/
def eps (h : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (h (x + y) + h (x - y) - 2 * h x) / (h (x + y) - h (x - y))

/-- The centre of the `j`-th dyadic subinterval of level `n` of `[a, b]`. -/
def dyadicCenter (a b : ℝ) (n j : ℕ) : ℝ :=
  a + (j + 1 / 2 : ℝ) * ((b - a) * (2 ^ n : ℝ)⁻¹)

/-- The half-length of a level-`n` dyadic subinterval of `[a, b]`. -/
def dyadicHalfLength (a b : ℝ) (n : ℕ) : ℝ := ((b - a) * (2 ^ n : ℝ)⁻¹) / 2

/-- The length of the `h`-image of the `j`-th level-`n` dyadic subinterval. -/
def dyadicImageLength (h : ℝ → ℝ) (a b : ℝ) (n j : ℕ) : ℝ :=
  h (a + (j + 1 : ℝ) * ((b - a) * (2 ^ n : ℝ)⁻¹)) -
    h (a + (j : ℝ) * ((b - a) * (2 ^ n : ℝ)⁻¹))

/-! ### Auxiliary machinery for the tent expansion proof -/

/-- The `j`-th level-`n` dyadic grid point of `[a, b]`. -/
private def dPt (a b : ℝ) (n j : ℕ) : ℝ := a + (j : ℝ) * ((b - a) * (2 ^ n : ℝ)⁻¹)

/-- The tent (hat) function on `[l, r]` with peak value `1` at the centre. -/
private def tentFn (l r : ℝ) (t : ℝ) : ℝ :=
  max 0 (1 - |t - (l + r) / 2| / ((r - l) / 2))

/-- The second difference of `h` at the centre of the `j`-th level-`n`
dyadic cell of `[a, b]`. -/
private def cellDiff (h : ℝ → ℝ) (a b : ℝ) (n j : ℕ) : ℝ :=
  h (dyadicCenter a b n j) - (h (dPt a b n j) + h (dPt a b n (j + 1))) / 2

/-- The affine interpolant of `h` at the endpoints of `[a, b]`. -/
private def endAffine (h : ℝ → ℝ) (a b : ℝ) (t : ℝ) : ℝ :=
  h a + (h b - h a) / (b - a) * (t - a)

/-- The `N`-th partial Schauder (tent) expansion of `h` on `[a, b]`. -/
private def schauder (h : ℝ → ℝ) (a b : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  endAffine h a b t + ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
    cellDiff h a b n j * tentFn (dPt a b n j) (dPt a b n (j + 1)) t

private lemma dPt_zero (a b : ℝ) (n : ℕ) : dPt a b n 0 = a := by simp [dPt]

private lemma dPt_last (a b : ℝ) (n : ℕ) : dPt a b n (2 ^ n) = b := by
  have h2 : ((2 : ℝ) ^ n) ≠ 0 := pow_ne_zero n two_ne_zero
  unfold dPt
  push_cast
  rw [mul_comm (b - a) ((2 : ℝ) ^ n)⁻¹, ← mul_assoc, mul_inv_cancel₀ h2, one_mul]
  ring

private lemma dPt_two_mul (a b : ℝ) (n j : ℕ) :
    dPt a b (n + 1) (2 * j) = dPt a b n j := by
  unfold dPt
  push_cast
  rw [pow_succ]
  field_simp [pow_ne_zero n two_ne_zero]

private lemma dPt_two_mul_add_one (a b : ℝ) (n j : ℕ) :
    dPt a b (n + 1) (2 * j + 1) = dyadicCenter a b n j := by
  unfold dPt dyadicCenter
  push_cast
  rw [pow_succ]
  field_simp [pow_ne_zero n two_ne_zero]

private lemma dPt_sub_succ (a b : ℝ) (n j : ℕ) :
    dPt a b n (j + 1) - dPt a b n j = (b - a) * (2 ^ n : ℝ)⁻¹ := by
  unfold dPt
  push_cast
  ring

private lemma dPt_mono (hab : a ≤ b) (n : ℕ) {j₁ j₂ : ℕ} (hj : j₁ ≤ j₂) :
    dPt a b n j₁ ≤ dPt a b n j₂ := by
  have hj' : (j₁ : ℝ) ≤ (j₂ : ℝ) := by exact_mod_cast hj
  have hu : (0 : ℝ) ≤ (b - a) * (2 ^ n : ℝ)⁻¹ := by
    have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
    positivity
  unfold dPt
  have hmul := mul_le_mul_of_nonneg_right hj' hu
  linarith

private lemma dPt_lt_succ (hab : a < b) (n j : ℕ) :
    dPt a b n j < dPt a b n (j + 1) := by
  have hu : (0 : ℝ) < (b - a) * (2 ^ n : ℝ)⁻¹ := by
    have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
    positivity
  have h := dPt_sub_succ a b n j
  linarith

private lemma dPt_lt_center (hab : a < b) (n j : ℕ) :
    dPt a b n j < dyadicCenter a b n j := by
  have hu : (0 : ℝ) < (b - a) * (2 ^ n : ℝ)⁻¹ := by
    have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
    positivity
  unfold dPt dyadicCenter
  linarith [hu]

private lemma center_lt_dPt_succ (hab : a < b) (n j : ℕ) :
    dyadicCenter a b n j < dPt a b n (j + 1) := by
  have hu : (0 : ℝ) < (b - a) * (2 ^ n : ℝ)⁻¹ := by
    have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
    positivity
  unfold dPt dyadicCenter
  push_cast
  linarith [hu]

private lemma center_eq_mid (a b : ℝ) (n j : ℕ) :
    dyadicCenter a b n j = (dPt a b n j + dPt a b n (j + 1)) / 2 := by
  unfold dPt dyadicCenter
  push_cast
  ring

private lemma cen_add_half (a b : ℝ) (n j : ℕ) :
    dyadicCenter a b n j + dyadicHalfLength a b n = dPt a b n (j + 1) := by
  unfold dPt dyadicCenter dyadicHalfLength
  push_cast
  ring

private lemma cen_sub_half (a b : ℝ) (n j : ℕ) :
    dyadicCenter a b n j - dyadicHalfLength a b n = dPt a b n j := by
  unfold dPt dyadicCenter dyadicHalfLength
  ring

private lemma imgLen_eq (h : ℝ → ℝ) (a b : ℝ) (n j : ℕ) :
    dyadicImageLength h a b n j = h (dPt a b n (j + 1)) - h (dPt a b n j) := by
  simp only [dyadicImageLength, dPt, Nat.cast_add, Nat.cast_one]

private lemma imgLen_sum_eq (h : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (2 ^ n), dyadicImageLength h a b n j = h b - h a := by
  have e : (∑ j ∈ Finset.range (2 ^ n), dyadicImageLength h a b n j) =
      ∑ j ∈ Finset.range (2 ^ n), (h (dPt a b n (j + 1)) - h (dPt a b n j)) :=
    Finset.sum_congr rfl fun j _ => imgLen_eq h a b n j
  rw [e, Finset.sum_range_sub (fun j => h (dPt a b n j)) (2 ^ n), dPt_last, dPt_zero]

private lemma tentFn_of_le {l r t : ℝ} (hlr : l < r) (ht : t ≤ l) : tentFn l r t = 0 := by
  have hy : (0 : ℝ) < (r - l) / 2 := by linarith
  have h1 : (r - l) / 2 ≤ |t - (l + r) / 2| := by
    rw [abs_of_neg (by linarith : t - (l + r) / 2 < 0)]
    linarith
  have h2 : 1 - |t - (l + r) / 2| / ((r - l) / 2) ≤ 0 := by
    have h3 : (1 : ℝ) ≤ |t - (l + r) / 2| / ((r - l) / 2) := by
      rw [le_div_iff₀ hy]
      simpa using h1
    linarith
  exact max_eq_left h2

private lemma tentFn_of_ge {l r t : ℝ} (hlr : l < r) (ht : r ≤ t) : tentFn l r t = 0 := by
  have hy : (0 : ℝ) < (r - l) / 2 := by linarith
  have h1 : (r - l) / 2 ≤ |t - (l + r) / 2| := by
    rw [abs_of_pos (by linarith : 0 < t - (l + r) / 2)]
    linarith
  have h2 : 1 - |t - (l + r) / 2| / ((r - l) / 2) ≤ 0 := by
    have h3 : (1 : ℝ) ≤ |t - (l + r) / 2| / ((r - l) / 2) := by
      rw [le_div_iff₀ hy]
      simpa using h1
    linarith
  exact max_eq_left h2

private lemma tentFn_center {l r : ℝ} : tentFn l r ((l + r) / 2) = 1 := by
  unfold tentFn
  rw [sub_self, abs_zero, zero_div, sub_zero]
  exact max_eq_right zero_le_one

private lemma tentFn_left {l r t : ℝ} (hlr : l < r) (hl : l ≤ t) (ht : t ≤ (l + r) / 2) :
    tentFn l r t = (t - l) / ((r - l) / 2) := by
  have hy : (0 : ℝ) < (r - l) / 2 := by linarith
  have hval : 1 - |t - (l + r) / 2| / ((r - l) / 2) = (t - l) / ((r - l) / 2) := by
    rw [abs_of_nonpos (by linarith : t - (l + r) / 2 ≤ 0), neg_div, sub_neg_eq_add,
      show (1 : ℝ) = ((r - l) / 2) / ((r - l) / 2) from (div_self hy.ne').symm, add_div]
    ring
  have hnn : (0 : ℝ) ≤ (t - l) / ((r - l) / 2) := div_nonneg (by linarith) hy.le
  unfold tentFn
  rw [hval]
  exact max_eq_right hnn

private lemma tentFn_right {l r t : ℝ} (hlr : l < r) (ht : (l + r) / 2 ≤ t) (hr : t ≤ r) :
    tentFn l r t = (r - t) / ((r - l) / 2) := by
  have hy : (0 : ℝ) < (r - l) / 2 := by linarith
  have hval : 1 - |t - (l + r) / 2| / ((r - l) / 2) = (r - t) / ((r - l) / 2) := by
    rw [abs_of_nonneg (by linarith : 0 ≤ t - (l + r) / 2),
      show (1 : ℝ) = ((r - l) / 2) / ((r - l) / 2) from (div_self hy.ne').symm, sub_div]
    ring
  have hnn : (0 : ℝ) ≤ (r - t) / ((r - l) / 2) := div_nonneg (by linarith) hy.le
  unfold tentFn
  rw [hval]
  exact max_eq_right hnn

private lemma tentFn_nonneg (l r : ℝ) (t : ℝ) : 0 ≤ tentFn l r t := le_max_left _ _

private lemma tentFn_continuous (l r : ℝ) : Continuous (tentFn l r) :=
  continuous_const.max
    (continuous_const.sub (((continuous_id'.sub continuous_const).abs).div_const _))

private lemma integral_tentFn {l r a b : ℝ} (hlr : l < r) (hal : a ≤ l) (hrb : r ≤ b) :
    ∫ t in a..b, tentFn l r t = (r - l) / 2 := by
  have hcont : ∀ u v : ℝ, IntervalIntegrable (tentFn l r) volume u v :=
    fun u v => (tentFn_continuous l r).intervalIntegrable _ _
  have hy : (0 : ℝ) < (r - l) / 2 := by linarith
  have h1 : ∫ t in a..l, tentFn l r t = 0 := by
    have e : ∫ t in a..l, tentFn l r t = ∫ _ in a..l, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht2 : t ≤ l := by
        have hu : Set.uIcc a l = Set.Icc a l := Set.uIcc_of_le hal
        rw [hu] at ht
        exact ht.2
      show tentFn l r t = 0
      exact tentFn_of_le hlr ht2
    rw [e, intervalIntegral.integral_zero]
  have h2 : ∫ t in r..b, tentFn l r t = 0 := by
    have e : ∫ t in r..b, tentFn l r t = ∫ _ in r..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have ht2 : r ≤ t := by
        have hu : Set.uIcc r b = Set.Icc r b := Set.uIcc_of_le hrb
        rw [hu] at ht
        exact ht.1
      show tentFn l r t = 0
      exact tentFn_of_ge hlr ht2
    rw [e, intervalIntegral.integral_zero]
  have hmid : ∫ t in l..r, tentFn l r t = (r - l) / 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hcont l ((l + r) / 2))
      (hcont ((l + r) / 2) r)]
    have hL : ∫ t in l..((l + r) / 2), tentFn l r t = (r - l) / 4 := by
      have e : ∫ t in l..((l + r) / 2), tentFn l r t =
          ∫ t in l..((l + r) / 2), (t - l) / ((r - l) / 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hu : Set.uIcc l ((l + r) / 2) = Set.Icc l ((l + r) / 2) :=
          Set.uIcc_of_le (by linarith)
        rw [hu] at ht
        show tentFn l r t = (t - l) / ((r - l) / 2)
        exact tentFn_left hlr ht.1 ht.2
      rw [e, intervalIntegral.integral_div,
        intervalIntegral.integral_comp_sub_right (f := fun x => x) l, sub_self,
        show (l + r) / 2 - l = (r - l) / 2 by ring, integral_id,
        zero_pow (show (2 : ℕ) ≠ 0 by norm_num), sub_zero]
      field_simp [hy.ne']
      ring
    have hR : ∫ t in (l + r) / 2..r, tentFn l r t = (r - l) / 4 := by
      have e : ∫ t in (l + r) / 2..r, tentFn l r t =
          ∫ t in (l + r) / 2..r, (r - t) / ((r - l) / 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have hu : Set.uIcc ((l + r) / 2) r = Set.Icc ((l + r) / 2) r :=
          Set.uIcc_of_le (by linarith)
        rw [hu] at ht
        show tentFn l r t = (r - t) / ((r - l) / 2)
        exact tentFn_right hlr ht.1 ht.2
      have e3 : (∫ t in (l + r) / 2..r, (r - t)) = ∫ t in (l + r) / 2..r, -(t - r) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      rw [e, intervalIntegral.integral_div, e3,
        intervalIntegral.integral_comp_sub_right (f := fun u => -u) r, sub_self,
        show (l + r) / 2 - r = -((r - l) / 2) by ring, intervalIntegral.integral_neg,
        integral_id, zero_pow (show (2 : ℕ) ≠ 0 by norm_num), zero_sub]
      field_simp [hy.ne']
      ring
    rw [hL, hR]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont a l) (hcont l b),
    ← intervalIntegral.integral_add_adjacent_intervals (hcont l r) (hcont r b),
    h1, h2, hmid, zero_add, add_zero]

private lemma schauder_zero (h : ℝ → ℝ) (a b t : ℝ) :
    schauder h a b 0 t = endAffine h a b t := by
  simp [schauder]

private lemma schauder_succ (h : ℝ → ℝ) (a b : ℝ) (N : ℕ) (t : ℝ) :
    schauder h a b (N + 1) t = schauder h a b N t +
      ∑ j ∈ Finset.range (2 ^ N),
        cellDiff h a b N j * tentFn (dPt a b N j) (dPt a b N (j + 1)) t := by
  unfold schauder
  rw [Finset.sum_range_succ]
  ring

/-- On the `j`-th level-`N` dyadic cell, the `N`-th partial Schauder expansion
is affine. -/
private lemma schauder_affine (h : ℝ → ℝ) (a b : ℝ) (hab : a < b) :
    ∀ (N j : ℕ), j < 2 ^ N → ∃ α β : ℝ, ∀ t : ℝ,
      t ∈ Set.Icc (dPt a b N j) (dPt a b N (j + 1)) →
        schauder h a b N t = α + β * (t - dPt a b N j) := by
  intro N
  induction N with
  | zero =>
    intro j hj
    obtain rfl : j = 0 := by
      rw [pow_zero] at hj
      exact Nat.lt_one_iff.mp hj
    refine ⟨h a, (h b - h a) / (b - a), fun t _ => ?_⟩
    rw [schauder_zero, dPt_zero]
    unfold endAffine
    ring
  | succ N ih =>
    intro j hj
    have h2N : (2 : ℕ) ^ (N + 1) = 2 ^ N * 2 := pow_succ 2 N
    rcases Nat.mod_two_eq_zero_or_one j with hpar | hpar
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = 2 * k := ⟨j / 2, by omega⟩
      rw [h2N] at hj
      have hk : k < 2 ^ N := by omega
      obtain ⟨α, β, hαβ⟩ := ih k hk
      refine ⟨α, β + cellDiff h a b N k / ((dPt a b N (k + 1) - dPt a b N k) / 2),
        fun t ht => ?_⟩
      rw [dPt_two_mul, dPt_two_mul_add_one] at ht
      have ht' : t ∈ Set.Icc (dPt a b N k) (dPt a b N (k + 1)) :=
        ⟨ht.1, ht.2.trans (center_lt_dPt_succ hab N k).le⟩
      have hsum : (∑ j' ∈ Finset.range (2 ^ N), cellDiff h a b N j' *
            tentFn (dPt a b N j') (dPt a b N (j' + 1)) t) =
          cellDiff h a b N k * tentFn (dPt a b N k) (dPt a b N (k + 1)) t := by
        apply Finset.sum_eq_single k
        · intro j' hj' hjk
          rcases lt_or_gt_of_ne hjk with hlt | hgt
          · rw [tentFn_of_ge (dPt_lt_succ hab N j')
              ((dPt_mono hab.le N (show j' + 1 ≤ k by omega)).trans ht.1), mul_zero]
          · rw [tentFn_of_le (dPt_lt_succ hab N j')
              (ht.2.trans ((center_lt_dPt_succ hab N k).le.trans
                (dPt_mono hab.le N (show k + 1 ≤ j' by omega)))), mul_zero]
        · intro hkn
          exact absurd (Finset.mem_range.mpr hk) hkn
      have htent : tentFn (dPt a b N k) (dPt a b N (k + 1)) t =
          (t - dPt a b N k) / ((dPt a b N (k + 1) - dPt a b N k) / 2) :=
        tentFn_left (dPt_lt_succ hab N k) ht.1 (by rw [← center_eq_mid]; exact ht.2)
      rw [schauder_succ, hsum, hαβ t ht', htent, dPt_two_mul]
      ring
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = 2 * k + 1 := ⟨j / 2, by omega⟩
      rw [h2N] at hj
      have hk : k < 2 ^ N := by omega
      obtain ⟨α, β, hαβ⟩ := ih k hk
      have hY0 : (0 : ℝ) < (dPt a b N (k + 1) - dPt a b N k) / 2 := by
        have hlt := dPt_lt_succ hab N k
        linarith
      refine ⟨α + β * ((dPt a b N (k + 1) - dPt a b N k) / 2) + cellDiff h a b N k,
        β - cellDiff h a b N k / ((dPt a b N (k + 1) - dPt a b N k) / 2), fun t ht => ?_⟩
      rw [dPt_two_mul_add_one, show 2 * k + 1 + 1 = 2 * (k + 1) by ring,
        dPt_two_mul] at ht
      have ht' : t ∈ Set.Icc (dPt a b N k) (dPt a b N (k + 1)) :=
        ⟨(dPt_lt_center hab N k).le.trans ht.1, ht.2⟩
      have hsum : (∑ j' ∈ Finset.range (2 ^ N), cellDiff h a b N j' *
            tentFn (dPt a b N j') (dPt a b N (j' + 1)) t) =
          cellDiff h a b N k * tentFn (dPt a b N k) (dPt a b N (k + 1)) t := by
        apply Finset.sum_eq_single k
        · intro j' hj' hjk
          rcases lt_or_gt_of_ne hjk with hlt | hgt
          · rw [tentFn_of_ge (dPt_lt_succ hab N j')
              ((dPt_mono hab.le N (show j' + 1 ≤ k by omega)).trans
                ((dPt_lt_center hab N k).le.trans ht.1)), mul_zero]
          · rw [tentFn_of_le (dPt_lt_succ hab N j')
              (ht.2.trans (dPt_mono hab.le N (show k + 1 ≤ j' by omega))), mul_zero]
        · intro hkn
          exact absurd (Finset.mem_range.mpr hk) hkn
      have htent : tentFn (dPt a b N k) (dPt a b N (k + 1)) t =
          (dPt a b N (k + 1) - t) / ((dPt a b N (k + 1) - dPt a b N k) / 2) :=
        tentFn_right (dPt_lt_succ hab N k) (by rw [← center_eq_mid]; exact ht.1) ht.2
      rw [schauder_succ, hsum, hαβ t ht', htent, dPt_two_mul_add_one, center_eq_mid]
      linear_combination div_mul_cancel₀ (cellDiff h a b N k) (ne_of_gt hY0)

/-- The `N`-th partial Schauder expansion interpolates `h` at level-`N`
dyadic grid points. -/
private lemma schauder_interp (h : ℝ → ℝ) (a b : ℝ) (hab : a < b) :
    ∀ (N j : ℕ), j ≤ 2 ^ N → schauder h a b N (dPt a b N j) = h (dPt a b N j) := by
  have hb0 : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  intro N
  induction N with
  | zero =>
    intro j hj
    rw [pow_zero] at hj
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · rw [dPt_zero, schauder_zero]
      unfold endAffine
      ring
    · have hd : dPt a b 0 1 = b := by
        have hdl := dPt_last a b 0
        rwa [pow_zero] at hdl
      rw [hd, schauder_zero]
      unfold endAffine
      rw [div_mul_cancel₀ _ hb0]
      ring
  | succ N ih =>
    intro j hj
    have h2N : (2 : ℕ) ^ (N + 1) = 2 ^ N * 2 := pow_succ 2 N
    rw [h2N] at hj
    rcases Nat.mod_two_eq_zero_or_one j with hpar | hpar
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = 2 * k := ⟨j / 2, by omega⟩
      have hk : k ≤ 2 ^ N := by omega
      rw [dPt_two_mul, schauder_succ]
      have hsum : (∑ j' ∈ Finset.range (2 ^ N), cellDiff h a b N j' *
            tentFn (dPt a b N j') (dPt a b N (j' + 1)) (dPt a b N k)) = 0 := by
        apply Finset.sum_eq_zero
        intro j' _
        rcases lt_or_ge j' k with hlt | hge
        · rw [tentFn_of_ge (dPt_lt_succ hab N j')
            (dPt_mono hab.le N (show j' + 1 ≤ k by omega)), mul_zero]
        · rw [tentFn_of_le (dPt_lt_succ hab N j') (dPt_mono hab.le N hge), mul_zero]
      rw [hsum, add_zero]
      exact ih k hk
    · obtain ⟨k, rfl⟩ : ∃ k : ℕ, j = 2 * k + 1 := ⟨j / 2, by omega⟩
      have hk : k < 2 ^ N := by omega
      have hkle : k ≤ 2 ^ N := hk.le
      have hk1 : k + 1 ≤ 2 ^ N := hk
      rw [dPt_two_mul_add_one, schauder_succ]
      have hsum : (∑ j' ∈ Finset.range (2 ^ N), cellDiff h a b N j' *
            tentFn (dPt a b N j') (dPt a b N (j' + 1)) (dyadicCenter a b N k)) =
          cellDiff h a b N k *
            tentFn (dPt a b N k) (dPt a b N (k + 1)) (dyadicCenter a b N k) := by
        apply Finset.sum_eq_single k
        · intro j' _ hjk
          rcases lt_or_gt_of_ne hjk with hlt | hgt
          · rw [tentFn_of_ge (dPt_lt_succ hab N j')
              ((dPt_mono hab.le N (show j' + 1 ≤ k by omega)).trans
                (dPt_lt_center hab N k).le), mul_zero]
          · rw [tentFn_of_le (dPt_lt_succ hab N j')
              ((center_lt_dPt_succ hab N k).le.trans
                (dPt_mono hab.le N (show k + 1 ≤ j' by omega))), mul_zero]
        · intro hkn
          exact absurd (Finset.mem_range.mpr hk) hkn
      have htent1 : tentFn (dPt a b N k) (dPt a b N (k + 1)) (dyadicCenter a b N k) = 1 := by
        rw [center_eq_mid]
        exact tentFn_center
      rw [hsum, htent1, mul_one]
      obtain ⟨α, β, hαβ⟩ := schauder_affine h a b hab N k hk
      have hα : α = h (dPt a b N k) := by
        have h1 := hαβ _ ⟨le_refl _, (dPt_lt_succ hab N k).le⟩
        rw [sub_self, mul_zero, add_zero] at h1
        exact h1.symm.trans (ih k hkle)
      have hβ : β * (dPt a b N (k + 1) - dPt a b N k) =
          h (dPt a b N (k + 1)) - h (dPt a b N k) := by
        have h2 := hαβ _ ⟨(dPt_lt_succ hab N k).le, le_refl _⟩
        rw [ih (k + 1) hk1, hα] at h2
        linarith
      have hcl : dyadicCenter a b N k - dPt a b N k =
          (dPt a b N (k + 1) - dPt a b N k) / 2 := by
        rw [center_eq_mid]
        ring
      have hmid : schauder h a b N (dyadicCenter a b N k) =
          (h (dPt a b N k) + h (dPt a b N (k + 1))) / 2 := by
        have h3 := hαβ _ ⟨(dPt_lt_center hab N k).le, (center_lt_dPt_succ hab N k).le⟩
        rw [hα, hcl, show β * ((dPt a b N (k + 1) - dPt a b N k) / 2) =
          (β * (dPt a b N (k + 1) - dPt a b N k)) / 2 by ring, hβ] at h3
        rw [h3]
        ring
      unfold cellDiff
      rw [hmid]
      ring

/-- Every point of `[a, b]` lies in some level-`N` dyadic cell. -/
private lemma exists_cell (a b : ℝ) (hab : a < b) (N : ℕ) (t : ℝ)
    (ht : t ∈ Set.Icc a b) :
    ∃ j < 2 ^ N, t ∈ Set.Icc (dPt a b N j) (dPt a b N (j + 1)) := by
  have h2Npos : 0 < 2 ^ N := pow_pos (by norm_num) N
  rcases eq_or_lt_of_le ht.2 with htb | htb
  · refine ⟨2 ^ N - 1, by omega, ?_, ?_⟩
    · rw [htb]
      have h1 : dPt a b N (2 ^ N - 1) ≤ dPt a b N (2 ^ N) :=
        dPt_mono hab.le N (by omega)
      rwa [dPt_last] at h1
    · have h2 : (2 ^ N - 1) + 1 = 2 ^ N := by omega
      rw [htb, h2, dPt_last]
  · set u := (b - a) * (2 ^ N : ℝ)⁻¹ with hu_def
    have hu : (0 : ℝ) < u := by
      rw [hu_def]
      have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
      positivity
    set q := (t - a) / u with hq_def
    have hq0 : (0 : ℝ) ≤ q := by
      rw [hq_def]
      exact div_nonneg (sub_nonneg.mpr ht.1) hu.le
    have h2u : (2 : ℝ) ^ N * u = b - a := by
      rw [hu_def]
      field_simp [pow_ne_zero N two_ne_zero]
    have hq_lt : q < (2 : ℝ) ^ N := by
      rw [hq_def, div_lt_iff₀ hu, h2u]
      exact sub_lt_sub_right htb a
    refine ⟨⌊q⌋₊, ?_, ?_, ?_⟩
    · rw [Nat.floor_lt hq0]
      exact_mod_cast hq_lt
    · have h1 : (⌊q⌋₊ : ℝ) ≤ q := Nat.floor_le hq0
      have h2 := mul_le_mul_of_nonneg_right h1 hu.le
      rw [hq_def, div_mul_cancel₀ _ hu.ne'] at h2
      unfold dPt
      rw [← hu_def]
      linarith
    · have h1 : q < ⌊q⌋₊ + 1 := Nat.lt_floor_add_one q
      have h2 := mul_lt_mul_of_pos_right h1 hu
      rw [hq_def, div_mul_cancel₀ _ hu.ne'] at h2
      unfold dPt
      rw [← hu_def]
      push_cast
      linarith

/-- Pointwise error bound: on the cell containing `t`, the Schauder
approximant differs from `h` by at most the cell's image length. -/
private lemma abs_sub_schauder_le (h : ℝ → ℝ) (hh : StrictMono h) (a b : ℝ)
    (hab : a < b) (N : ℕ) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∃ j < 2 ^ N, |h t - schauder h a b N t| ≤
      h (dPt a b N (j + 1)) - h (dPt a b N j) := by
  obtain ⟨j, hj, htj⟩ := exists_cell a b hab N t ht
  refine ⟨j, hj, ?_⟩
  obtain ⟨α, β, hαβ⟩ := schauder_affine h a b hab N j hj
  have hjl : j ≤ 2 ^ N := hj.le
  have hj1 : j + 1 ≤ 2 ^ N := hj
  have hl := schauder_interp h a b hab N j hjl
  have hr := schauder_interp h a b hab N (j + 1) hj1
  have hY : (0 : ℝ) < dPt a b N (j + 1) - dPt a b N j :=
    sub_pos.mpr (dPt_lt_succ hab N j)
  have hα : α = h (dPt a b N j) := by
    have h1 := hαβ _ ⟨le_refl _, (dPt_lt_succ hab N j).le⟩
    rw [sub_self, mul_zero, add_zero] at h1
    exact h1.symm.trans hl
  have hβ : β = (h (dPt a b N (j + 1)) - h (dPt a b N j)) /
      (dPt a b N (j + 1) - dPt a b N j) := by
    have h2 := hαβ _ ⟨(dPt_lt_succ hab N j).le, le_refl _⟩
    rw [hr, hα] at h2
    rw [eq_div_iff hY.ne']
    linarith
  have hst : schauder h a b N t = h (dPt a b N j) +
      (h (dPt a b N (j + 1)) - h (dPt a b N j)) *
        ((t - dPt a b N j) / (dPt a b N (j + 1) - dPt a b N j)) := by
    have h3 := hαβ t htj
    rw [hα, hβ] at h3
    rw [h3]
    ring
  set s := (t - dPt a b N j) / (dPt a b N (j + 1) - dPt a b N j) with hs_def
  have hs0 : (0 : ℝ) ≤ s := by
    rw [hs_def]
    exact div_nonneg (sub_nonneg.mpr htj.1) hY.le
  have hs1 : s ≤ 1 := by
    rw [hs_def, div_le_one hY]
    exact sub_le_sub_right htj.2 _
  have hD : (0 : ℝ) ≤ h (dPt a b N (j + 1)) - h (dPt a b N j) :=
    sub_nonneg.mpr (hh (dPt_lt_succ hab N j)).le
  have hX0 : (0 : ℝ) ≤ (h (dPt a b N (j + 1)) - h (dPt a b N j)) * s :=
    mul_nonneg hD hs0
  have hX1 : (h (dPt a b N (j + 1)) - h (dPt a b N j)) * s ≤
      h (dPt a b N (j + 1)) - h (dPt a b N j) :=
    mul_le_of_le_one_right hD hs1
  have htL : h (dPt a b N j) ≤ h t := hh.monotone htj.1
  have htR : h t ≤ h (dPt a b N (j + 1)) := hh.monotone htj.2
  rw [hst, abs_le]
  constructor <;> linarith

/-- The cell second difference factors as `-(1/2) ε |h(L)|`. -/
private lemma cellDiff_eq (h : ℝ → ℝ) (hh : StrictMono h) (a b : ℝ) (hab : a < b)
    (n j : ℕ) :
    cellDiff h a b n j = -(1 / 2) *
      eps h (dyadicCenter a b n j) (dyadicHalfLength a b n) *
        dyadicImageLength h a b n j := by
  have hrl : h (dPt a b n (j + 1)) - h (dPt a b n j) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (hh (dPt_lt_succ hab n j)))
  unfold eps cellDiff
  rw [cen_add_half, cen_sub_half, imgLen_eq]
  field_simp [hrl]
  ring

private lemma abs_cellDiff (h : ℝ → ℝ) (hh : StrictMono h) (a b : ℝ) (hab : a < b)
    (n j : ℕ) :
    |cellDiff h a b n j| = (1 / 2) *
      |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| *
        dyadicImageLength h a b n j := by
  have himg : (0 : ℝ) ≤ dyadicImageLength h a b n j := by
    rw [imgLen_eq h a b n j]
    exact sub_nonneg.mpr (hh.monotone (dPt_mono hab.le n (Nat.le_succ j)))
  rw [cellDiff_eq h hh a b hab n j, abs_mul, abs_mul, abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_nonneg himg]

private lemma abs_eps_le_one (h : ℝ → ℝ) (hh : StrictMono h) (a b : ℝ) (hab : a < b)
    (n j : ℕ) :
    |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| ≤ 1 := by
  have hrl : (0 : ℝ) < h (dPt a b n (j + 1)) - h (dPt a b n j) :=
    sub_pos.mpr (hh (dPt_lt_succ hab n j))
  have h1 : (0 : ℝ) ≤ h (dyadicCenter a b n j) - h (dPt a b n j) :=
    sub_nonneg.mpr (hh.monotone (dPt_lt_center hab n j).le)
  have h2 : (0 : ℝ) ≤ h (dPt a b n (j + 1)) - h (dyadicCenter a b n j) :=
    sub_nonneg.mpr (hh.monotone (center_lt_dPt_succ hab n j).le)
  unfold eps
  rw [cen_add_half, cen_sub_half, abs_div, abs_of_pos hrl, div_le_one hrl,
    show h (dPt a b n (j + 1)) + h (dPt a b n j) - 2 * h (dyadicCenter a b n j) =
      (h (dPt a b n (j + 1)) - h (dyadicCenter a b n j)) -
        (h (dyadicCenter a b n j) - h (dPt a b n j)) by ring, abs_le]
  constructor <;> linarith

private lemma sum_abs_cellDiff_le (h : ℝ → ℝ) (hh : StrictMono h) (a b : ℝ)
    (hab : a < b) (n : ℕ) :
    ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j| ≤ (h b - h a) / 2 := by
  have hterm : ∀ j ∈ Finset.range (2 ^ n),
      |cellDiff h a b n j| ≤ (1 / 2) * dyadicImageLength h a b n j := by
    intro j _
    rw [abs_cellDiff h hh a b hab n j]
    have himg : (0 : ℝ) ≤ dyadicImageLength h a b n j := by
      rw [imgLen_eq h a b n j]
      exact sub_nonneg.mpr (hh.monotone (dPt_mono hab.le n (Nat.le_succ j)))
    have hmul := mul_le_mul_of_nonneg_right (abs_eps_le_one h hh a b hab n j) himg
    linarith
  calc ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j|
      ≤ ∑ j ∈ Finset.range (2 ^ n), (1 / 2) * dyadicImageLength h a b n j :=
        Finset.sum_le_sum hterm
    _ = (h b - h a) / 2 := by
        rw [← Finset.mul_sum, imgLen_sum_eq]
        ring

private lemma summable_cellDiff_series (h : ℝ → ℝ) (hh : StrictMono h) (a b : ℝ)
    (hab : a < b) :
    Summable fun n : ℕ =>
      (2 ^ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j| := by
  refine Summable.of_nonneg_of_le
    (f := fun n : ℕ => (2 ^ n : ℝ)⁻¹ * ((h b - h a) / 2)) ?_ ?_ ?_
  · intro n
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => abs_nonneg _)
  · intro n
    exact mul_le_mul_of_nonneg_left (sum_abs_cellDiff_le h hh a b hab n) (by positivity)
  · have e : (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * ((h b - h a) / 2)) =
        fun n => ((h b - h a) / 2) * (2⁻¹ : ℝ) ^ n := by
      funext n
      rw [inv_pow]
      ring
    rw [e]
    exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- Integral commutes with finite sums of continuous functions. -/
private lemma integral_sum_range {f : ℕ → ℝ → ℝ} {u v : ℝ} (N : ℕ)
    (hf : ∀ n, Continuous (f n)) :
    ∫ x in u..v, ∑ n ∈ Finset.range N, f n x =
      ∑ n ∈ Finset.range N, ∫ x in u..v, f n x := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    rw [intervalIntegral.integral_add
        ((continuous_finsetSum _ fun n _ => hf n).intervalIntegrable _ _)
        ((hf N).intervalIntegrable _ _),
      ih]

/-- **Lemma (Tent expansion)**: for `h` increasing continuous and `I` a
bounded interval,
`β_h(I) ≤ (1/4) ∑_{n≥0} 2^{-n} ∑_{L ∈ 𝒯_n(I)} (|h(L)|/|h(I)|) |ε_h(L)|`.
In particular `β_h(I) ≤ 1/2`. -/
theorem tent_expansion (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (a b : ℝ) (hab : a < b) :
    beta h a b ≤
        (1 / 4) * ∑' n : ℕ, (2 ^ n : ℝ)⁻¹ *
          ∑ j ∈ Finset.range (2 ^ n),
            (dyadicImageLength h a b n j / (h b - h a)) *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| ∧
      beta h a b ≤ 1 / 2 := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hb0 : b - a ≠ 0 := ne_of_gt hba
  have hdh : (0 : ℝ) < h b - h a := sub_pos.mpr (hh hab)
  have hdh0 : h b - h a ≠ 0 := ne_of_gt hdh
  have hAcont : Continuous (endAffine h a b) := by
    unfold endAffine
    exact continuous_const.add (continuous_const.mul (continuous_id'.sub continuous_const))
  have hScont : ∀ N : ℕ, Continuous (schauder h a b N) := by
    intro N
    unfold schauder
    exact hAcont.add (continuous_finsetSum _ fun n _ =>
      continuous_finsetSum _ fun j _ => continuous_const.mul (tentFn_continuous _ _))
  have hhint : IntervalIntegrable h MeasureTheory.volume a b :=
    hh.monotone.intervalIntegrable
  have hAint : IntervalIntegrable (endAffine h a b) MeasureTheory.volume a b :=
    hAcont.intervalIntegrable _ _
  have hSint : ∀ N : ℕ, IntervalIntegrable (schauder h a b N) MeasureTheory.volume a b :=
    fun N => (hScont N).intervalIntegrable _ _
  set S := ∑' n : ℕ, (2 ^ n : ℝ)⁻¹ *
    ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j| with hS_def
  have hSum : Summable fun n : ℕ =>
      (2 ^ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j| :=
    summable_cellDiff_series h hh a b hab
  -- The key integral estimate, by uniform continuity and the tent expansion.
  have hkey : ∫ t in a..b, |h t - endAffine h a b t| ≤ ((b - a) / 2) * S := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have hε' : (0 : ℝ) < ε / (b - a) := div_pos hε hba
    have huc : UniformContinuousOn h (Set.Icc a b) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hc.continuousOn
    obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / (b - a)) hε'
    have htend : Filter.Tendsto (fun N : ℕ => (b - a) * (2 ^ N : ℝ)⁻¹)
        Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun N : ℕ => (2⁻¹ : ℝ) ^ N) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have h2 := h1.const_mul (b - a)
      rw [mul_zero] at h2
      have e : (fun N : ℕ => (b - a) * (2 ^ N : ℝ)⁻¹) =
          fun N => (b - a) * (2⁻¹ : ℝ) ^ N := by
        funext N
        rw [inv_pow]
      rw [e]
      exact h2
    obtain ⟨N, hN⟩ := (htend.eventually (Iio_mem_nhds hδ)).exists
    have hN' : (b - a) * (2 ^ N : ℝ)⁻¹ < δ := hN
    have hpt : ∀ t ∈ Set.Icc a b, |h t - schauder h a b N t| ≤ ε / (b - a) := by
      intro t ht
      obtain ⟨j, hj, hbound⟩ := abs_sub_schauder_le h hh a b hab N t ht
      have hj1 : j + 1 ≤ 2 ^ N := hj
      have hmem_l : dPt a b N j ∈ Set.Icc a b := by
        have e1 : dPt a b N 0 ≤ dPt a b N j := dPt_mono hab.le N (Nat.zero_le _)
        have e2 : dPt a b N j ≤ dPt a b N (2 ^ N) := dPt_mono hab.le N hj.le
        rw [dPt_zero] at e1
        rw [dPt_last] at e2
        exact ⟨e1, e2⟩
      have hmem_r : dPt a b N (j + 1) ∈ Set.Icc a b := by
        have e1 : dPt a b N 0 ≤ dPt a b N (j + 1) := dPt_mono hab.le N (Nat.zero_le _)
        have e2 : dPt a b N (j + 1) ≤ dPt a b N (2 ^ N) := dPt_mono hab.le N hj1
        rw [dPt_zero] at e1
        rw [dPt_last] at e2
        exact ⟨e1, e2⟩
      have hdist : dist (dPt a b N j) (dPt a b N (j + 1)) < δ := by
        rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (dPt_lt_succ hab N j)), neg_sub,
          dPt_sub_succ]
        exact hN'
      have hosc := hδ' _ hmem_l _ hmem_r hdist
      rw [Real.dist_eq] at hosc
      have hnonpos : h (dPt a b N j) - h (dPt a b N (j + 1)) ≤ 0 :=
        sub_nonpos.mpr (hh.monotone (dPt_mono hab.le N (Nat.le_succ j)))
      rw [abs_of_nonpos hnonpos] at hosc
      have hle : h (dPt a b N (j + 1)) - h (dPt a b N j) ≤ ε / (b - a) := by
        linarith
      exact hbound.trans hle
    have hInt1 : ∫ t in a..b, |h t - schauder h a b N t| ≤ (b - a) * (ε / (b - a)) := by
      have hmono := intervalIntegral.integral_mono_on hab.le ((hhint.sub (hSint N)).abs)
        intervalIntegrable_const (fun t ht => hpt t ht)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      linarith
    have hpt2 : ∀ t : ℝ, |schauder h a b N t - endAffine h a b t| ≤
        ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
          |cellDiff h a b n j| * tentFn (dPt a b n j) (dPt a b n (j + 1)) t := by
      intro t
      have e1 : schauder h a b N t - endAffine h a b t =
          ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
            cellDiff h a b n j * tentFn (dPt a b n j) (dPt a b n (j + 1)) t := by
        unfold schauder
        ring
      rw [e1]
      calc |∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
              cellDiff h a b n j * tentFn (dPt a b n j) (dPt a b n (j + 1)) t|
          ≤ ∑ n ∈ Finset.range N, |∑ j ∈ Finset.range (2 ^ n),
              cellDiff h a b n j * tentFn (dPt a b n j) (dPt a b n (j + 1)) t| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
              |cellDiff h a b n j * tentFn (dPt a b n j) (dPt a b n (j + 1)) t| :=
            Finset.sum_le_sum fun n _ => Finset.abs_sum_le_sum_abs _ _
        _ = ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
              |cellDiff h a b n j| * tentFn (dPt a b n j) (dPt a b n (j + 1)) t := by
            apply Finset.sum_congr rfl
            intro n _
            apply Finset.sum_congr rfl
            intro j _
            rw [abs_mul, abs_of_nonneg (tentFn_nonneg _ _ _)]
    have htentSumInt : IntervalIntegrable (fun t => ∑ n ∈ Finset.range N,
        ∑ j ∈ Finset.range (2 ^ n),
          |cellDiff h a b n j| * tentFn (dPt a b n j) (dPt a b n (j + 1)) t)
        MeasureTheory.volume a b :=
      (continuous_finsetSum _ fun n _ => continuous_finsetSum _ fun j _ =>
        continuous_const.mul (tentFn_continuous _ _)).intervalIntegrable _ _
    have hIntT : ∀ n j : ℕ, j < 2 ^ n →
        ∫ t in a..b, |cellDiff h a b n j| *
            tentFn (dPt a b n j) (dPt a b n (j + 1)) t =
          |cellDiff h a b n j| * ((b - a) * (2 ^ n : ℝ)⁻¹) / 2 := by
      intro n j hj
      rw [intervalIntegral.integral_const_mul]
      have hal : a ≤ dPt a b n j := by
        have e := dPt_mono hab.le n (Nat.zero_le j)
        rwa [dPt_zero] at e
      have hrb : dPt a b n (j + 1) ≤ b := by
        have e := dPt_mono hab.le n (Nat.succ_le_iff.mpr hj)
        rwa [dPt_last] at e
      rw [integral_tentFn (dPt_lt_succ hab n j) hal hrb, dPt_sub_succ]
      ring
    have hsum_int : ∫ t in a..b, ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
          |cellDiff h a b n j| * tentFn (dPt a b n j) (dPt a b n (j + 1)) t =
        ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
          |cellDiff h a b n j| * ((b - a) * (2 ^ n : ℝ)⁻¹) / 2 := by
      rw [integral_sum_range N ?_]
      apply Finset.sum_congr rfl
      intro n _
      rw [integral_sum_range (2 ^ n) ?_]
      apply Finset.sum_congr rfl
      intro j hj
      exact hIntT n j (Finset.mem_range.mp hj)
      · intro j
        exact continuous_const.mul (tentFn_continuous _ _)
      · intro n
        exact continuous_finsetSum _ fun j _ => continuous_const.mul (tentFn_continuous _ _)
    have hInt2 : ∫ t in a..b, |schauder h a b N t - endAffine h a b t| ≤
        ((b - a) / 2) * ∑ n ∈ Finset.range N, (2 ^ n : ℝ)⁻¹ *
          ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j| := by
      calc ∫ t in a..b, |schauder h a b N t - endAffine h a b t|
          ≤ ∫ t in a..b, ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
              |cellDiff h a b n j| * tentFn (dPt a b n j) (dPt a b n (j + 1)) t :=
            intervalIntegral.integral_mono_on hab.le (((hSint N).sub hAint).abs)
              htentSumInt (fun t _ => hpt2 t)
        _ = ∑ n ∈ Finset.range N, ∑ j ∈ Finset.range (2 ^ n),
              |cellDiff h a b n j| * ((b - a) * (2 ^ n : ℝ)⁻¹) / 2 := hsum_int
        _ = ((b - a) / 2) * ∑ n ∈ Finset.range N, (2 ^ n : ℝ)⁻¹ *
              ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j| := by
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n _
            apply Finset.sum_congr rfl
            intro j _
            ring
    have hcomb : ∫ t in a..b, |h t - endAffine h a b t| ≤
        (∫ t in a..b, |h t - schauder h a b N t|) +
          ∫ t in a..b, |schauder h a b N t - endAffine h a b t| := by
      have hpt3 : ∀ t : ℝ, |h t - endAffine h a b t| ≤
          |h t - schauder h a b N t| + |schauder h a b N t - endAffine h a b t| := by
        intro t
        have e : h t - endAffine h a b t =
            (h t - schauder h a b N t) + (schauder h a b N t - endAffine h a b t) := by
          ring
        rw [e]
        exact abs_add_le _ _
      calc ∫ t in a..b, |h t - endAffine h a b t|
          ≤ ∫ t in a..b, (|h t - schauder h a b N t| +
              |schauder h a b N t - endAffine h a b t|) :=
            intervalIntegral.integral_mono_on hab.le ((hhint.sub hAint).abs)
              (((hhint.sub (hSint N)).abs).add (((hSint N).sub hAint).abs))
              (fun t _ => hpt3 t)
        _ = (∫ t in a..b, |h t - schauder h a b N t|) +
              ∫ t in a..b, |schauder h a b N t - endAffine h a b t| :=
            intervalIntegral.integral_add ((hhint.sub (hSint N)).abs)
              (((hSint N).sub hAint).abs)
    have hpart : ∑ n ∈ Finset.range N, (2 ^ n : ℝ)⁻¹ *
        ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j| ≤ S :=
      hSum.sum_le_tsum (Finset.range N) (fun n _ =>
        mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => abs_nonneg _))
    have hcancel : (b - a) * (ε / (b - a)) = ε := by
      rw [mul_comm, div_mul_cancel₀ _ hb0]
    have hSbound : ((b - a) / 2) * (∑ n ∈ Finset.range N, (2 ^ n : ℝ)⁻¹ *
        ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j|) ≤ ((b - a) / 2) * S :=
      mul_le_mul_of_nonneg_left hpart (by positivity)
    have hfin := hcomb.trans (add_le_add hInt1 hInt2)
    rw [hcancel] at hfin
    linarith
  -- `β` is bounded by the normalised integral against the endpoint interpolant.
  have hβ1 : beta h a b ≤ ((b - a) * (h b - h a))⁻¹ *
      ∫ t in a..b, |h t - endAffine h a b t| := by
    apply csInf_le
    · exact ⟨0, fun r ⟨_, _, hr, _⟩ => hr⟩
    · refine ⟨(h b - h a) / (b - a), h a - ((h b - h a) / (b - a)) * a, ?_, ?_⟩
      · exact mul_nonneg (inv_nonneg.mpr (mul_nonneg hba.le hdh.le))
          (intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _))
      · congr 1
        apply intervalIntegral.integral_congr
        intro t _
        show |h t - endAffine h a b t| =
          |h t - (((h b - h a) / (b - a)) * t +
            (h a - ((h b - h a) / (b - a)) * a))|
        congr 1
        unfold endAffine
        ring
  have hβ2 : beta h a b ≤ (1 / (2 * (h b - h a))) * S := by
    refine hβ1.trans ?_
    calc ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - endAffine h a b t|
        ≤ ((b - a) * (h b - h a))⁻¹ * (((b - a) / 2) * S) :=
          mul_le_mul_of_nonneg_left hkey (inv_nonneg.mpr (mul_nonneg hba.le hdh.le))
      _ = (1 / (2 * (h b - h a))) * S := by
          field_simp [hb0, hdh0]
  -- Rewrite the series in terms of `ε` and the normalised image lengths.
  have hterm : ∀ n : ℕ, ∑ j ∈ Finset.range (2 ^ n), |cellDiff h a b n j| =
      (1 / 2) * ∑ j ∈ Finset.range (2 ^ n),
        dyadicImageLength h a b n j *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| := by
    intro n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_cellDiff h hh a b hab n j]
    ring
  have hST : S = (1 / 2) * ∑' n : ℕ, (2 ^ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 ^ n),
      dyadicImageLength h a b n j *
        |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| := by
    rw [hS_def, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [hterm n]
    ring
  set T := ∑' n : ℕ, (2 ^ n : ℝ)⁻¹ *
    ∑ j ∈ Finset.range (2 ^ n),
      (dyadicImageLength h a b n j / (h b - h a)) *
        |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| with hT_def
  have hterm2 : ∀ n : ℕ, ∑ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| =
      (h b - h a)⁻¹ * ∑ j ∈ Finset.range (2 ^ n),
        dyadicImageLength h a b n j *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| := by
    intro n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [div_eq_mul_inv]
    ring
  have hT'T : ∑' n : ℕ, (2 ^ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 ^ n),
        dyadicImageLength h a b n j *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| =
      (h b - h a) * T := by
    rw [hT_def, ← tsum_mul_left]
    apply tsum_congr
    intro n
    rw [hterm2 n]
    field_simp [hdh0]
  have hSid : (1 / (2 * (h b - h a))) * S = (1 / 4) * T := by
    rw [hST, hT'T]
    field_simp [hdh0]
    ring
  have hmain : beta h a b ≤ (1 / 4) * T := by
    rw [← hSid]
    exact hβ2
  -- The complementary bound `β ≤ 1/2`.
  have hinner : ∀ n : ℕ, ∑ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| ≤ 1 := by
    intro n
    have hterm_le : ∀ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| ≤
          dyadicImageLength h a b n j / (h b - h a) := by
      intro j _
      have himg : (0 : ℝ) ≤ dyadicImageLength h a b n j := by
        rw [imgLen_eq h a b n j]
        exact sub_nonneg.mpr (hh.monotone (dPt_mono hab.le n (Nat.le_succ j)))
      have hnn : (0 : ℝ) ≤ dyadicImageLength h a b n j / (h b - h a) :=
        div_nonneg himg hdh.le
      have hmul := mul_le_mul_of_nonneg_left (abs_eps_le_one h hh a b hab n j) hnn
      rwa [mul_one] at hmul
    calc ∑ j ∈ Finset.range (2 ^ n),
          (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|
        ≤ ∑ j ∈ Finset.range (2 ^ n), dyadicImageLength h a b n j / (h b - h a) :=
          Finset.sum_le_sum hterm_le
      _ = (∑ j ∈ Finset.range (2 ^ n), dyadicImageLength h a b n j) / (h b - h a) := by
          rw [Finset.sum_div]
      _ = (h b - h a) / (h b - h a) := by rw [imgLen_sum_eq]
      _ = 1 := div_self hdh0
  have hsumm2 : Summable fun n : ℕ => (2 ^ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 ^ n),
      (dyadicImageLength h a b n j / (h b - h a)) *
        |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => (2 ^ n : ℝ)⁻¹ * 1) ?_ ?_ ?_
    · intro n
      exact mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ =>
        mul_nonneg (div_nonneg (by
          rw [imgLen_eq h a b n j]
          exact sub_nonneg.mpr (hh.monotone (dPt_mono hab.le n (Nat.le_succ j))))
          hdh.le) (abs_nonneg _))
    · intro n
      exact mul_le_mul_of_nonneg_left (hinner n) (by positivity)
    · have e : (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * 1) = fun n => ((2 : ℝ)⁻¹) ^ n := by
        funext n
        rw [mul_one, inv_pow]
      rw [e]
      exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hgeo : (∑' n : ℕ, (2 ^ n : ℝ)⁻¹ * 1) = 2 := by
    have e : (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * 1) = fun n => (1 / 2 : ℝ) ^ n := by
      funext n
      rw [mul_one, div_pow, one_pow, one_div]
    rw [e]
    exact tsum_geometric_two
  have hsumle : T ≤ 2 := by
    have h1 : T ≤ ∑' n : ℕ, (2 ^ n : ℝ)⁻¹ * 1 := by
      rw [hT_def]
      exact hsumm2.tsum_le_tsum (fun n =>
        mul_le_mul_of_nonneg_left (hinner n) (by positivity))
        (by
          have e : (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * 1) = fun n => ((2 : ℝ)⁻¹) ^ n := by
            funext n
            rw [mul_one, inv_pow]
          rw [e]
          exact summable_geometric_of_lt_one (by norm_num) (by norm_num))
    exact h1.trans hgeo.le
  have hhalf : beta h a b ≤ 1 / 2 := by
    calc beta h a b ≤ (1 / 4) * T := hmain
      _ ≤ (1 / 4) * 2 := mul_le_mul_of_nonneg_left hsumle (by norm_num)
      _ = 1 / 2 := by norm_num
  exact ⟨hmain, hhalf⟩

/-- **Lemma (Squared form)**: for every bounded interval `I` and every
`θ ∈ (0, 1)`,
`β_h(I)² ≤ (1/8) ∑_{n≥0} 2^{-n(1-θ)} ∑_{L ∈ 𝒯_n(I)} (|h(L)|/|h(I)|) ε_h(L)²`. -/
theorem tent_squared (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1)
    (a b : ℝ) (hab : a < b) :
    (beta h a b) ^ 2 ≤
      (1 / 8) * ∑' n : ℕ, (2 : ℝ) ^ (-(n : ℝ) * (1 - θ)) *
        ∑ j ∈ Finset.range (2 ^ n),
          (dyadicImageLength h a b n j / (h b - h a)) *
            (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 := by
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hdh : (0 : ℝ) < h b - h a := sub_pos.mpr (hh hab)
  have hdh0 : h b - h a ≠ 0 := ne_of_gt hdh
  obtain ⟨hmain, -⟩ := tent_expansion h hh hc a b hab
  -- `β ≥ 0`, as an infimum of nonneg quantities.
  have hne : {r : ℝ | ∃ κ τ : ℝ, 0 ≤ r ∧
      r = ((b - a) * (h b - h a))⁻¹ * ∫ t in a..b, |h t - (κ * t + τ)|}.Nonempty := by
    refine ⟨_, (h b - h a) / (b - a), h a - ((h b - h a) / (b - a)) * a, ?_, rfl⟩
    exact mul_nonneg (inv_nonneg.mpr (mul_nonneg hba.le hdh.le))
      (intervalIntegral.integral_nonneg hab.le (fun t _ => abs_nonneg _))
  have hβ0 : (0 : ℝ) ≤ beta h a b :=
    le_csInf hne (fun r ⟨_, _, hr, _⟩ => hr)
  have himg : ∀ n j : ℕ, (0 : ℝ) ≤ dyadicImageLength h a b n j := by
    intro n j
    rw [imgLen_eq h a b n j]
    exact sub_nonneg.mpr (hh.monotone (dPt_mono hab.le n (Nat.le_succ j)))
  have hw : ∀ n j : ℕ, (0 : ℝ) ≤ dyadicImageLength h a b n j / (h b - h a) :=
    fun n j => div_nonneg (himg n j) hdh.le
  have hsumw : ∀ n : ℕ,
      ∑ j ∈ Finset.range (2 ^ n), dyadicImageLength h a b n j / (h b - h a) = 1 := by
    intro n
    rw [← Finset.sum_div, imgLen_sum_eq, div_self hdh0]
  -- Per-level Cauchy–Schwarz: `A_n² ≤ B_n` (the weights sum to `1`).
  have hA2B : ∀ n : ℕ,
      (∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 ≤
        ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
          (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 := by
    intro n
    have hcs : (∑ j ∈ Finset.range (2 ^ n),
          (dyadicImageLength h a b n j / (h b - h a)).sqrt *
            ((dyadicImageLength h a b n j / (h b - h a)).sqrt *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|)) ^ 2 ≤
        (∑ j ∈ Finset.range (2 ^ n),
            ((dyadicImageLength h a b n j / (h b - h a)).sqrt) ^ 2) *
          ∑ j ∈ Finset.range (2 ^ n),
            ((dyadicImageLength h a b n j / (h b - h a)).sqrt *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have e1 : ∀ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)).sqrt *
            ((dyadicImageLength h a b n j / (h b - h a)).sqrt *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) =
          (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| := by
      intro j _
      rw [← mul_assoc, Real.mul_self_sqrt (hw n j)]
    have e2 : ∀ j ∈ Finset.range (2 ^ n),
        ((dyadicImageLength h a b n j / (h b - h a)).sqrt) ^ 2 =
          dyadicImageLength h a b n j / (h b - h a) := by
      intro j _
      exact Real.sq_sqrt (hw n j)
    have e3 : ∀ j ∈ Finset.range (2 ^ n),
        ((dyadicImageLength h a b n j / (h b - h a)).sqrt *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 =
          (dyadicImageLength h a b n j / (h b - h a)) *
            (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 := by
      intro j _
      rw [mul_pow, Real.sq_sqrt (hw n j), sq_abs]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3,
      hsumw n, one_mul] at hcs
    exact hcs
  -- `A_n ≤ 1` and `B_n ≤ 1` (using `|ε| ≤ 1`).
  have hA1 : ∀ n : ℕ, ∑ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| ≤ 1 := by
    intro n
    have hterm : ∀ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| ≤
          dyadicImageLength h a b n j / (h b - h a) := by
      intro j _
      have hmul := mul_le_mul_of_nonneg_left (abs_eps_le_one h hh a b hab n j) (hw n j)
      rwa [mul_one] at hmul
    calc ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|
        ≤ ∑ j ∈ Finset.range (2 ^ n),
            dyadicImageLength h a b n j / (h b - h a) :=
          Finset.sum_le_sum hterm
      _ = 1 := hsumw n
  have hB1 : ∀ n : ℕ, ∑ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
          (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 ≤ 1 := by
    intro n
    have hterm : ∀ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
            (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 ≤
          dyadicImageLength h a b n j / (h b - h a) := by
      intro j _
      have he2 : (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 ≤ 1 :=
        (sq_le_one_iff_abs_le_one _).mpr (abs_eps_le_one h hh a b hab n j)
      have hmul := mul_le_mul_of_nonneg_left he2 (hw n j)
      rwa [mul_one] at hmul
    calc ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
            (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2
        ≤ ∑ j ∈ Finset.range (2 ^ n),
            dyadicImageLength h a b n j / (h b - h a) :=
          Finset.sum_le_sum hterm
      _ = 1 := hsumw n
  have hA0 : ∀ n : ℕ, (0 : ℝ) ≤ ∑ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| :=
    fun n => Finset.sum_nonneg fun j _ => mul_nonneg (hw n j) (abs_nonneg _)
  have hB0 : ∀ n : ℕ, (0 : ℝ) ≤ ∑ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
          (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 :=
    fun n => Finset.sum_nonneg fun j _ => mul_nonneg (hw n j) (sq_nonneg _)
  -- The geometric weights.
  set r := (2 : ℝ) ^ (-(1 - θ) : ℝ) with hr_def
  have hr0 : (0 : ℝ) < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := by
    rw [hr_def, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by linarith))
  set r2 := (2 : ℝ) ^ (-(1 + θ) : ℝ) with hr2_def
  have hr20 : (0 : ℝ) < r2 := Real.rpow_pos_of_pos (by norm_num) _
  have hr2l1 : r2 < 1 := by
    rw [hr2_def, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) (by linarith))
  have hr21 : r2 ≤ 1 / 2 := by
    have h1 : (2 : ℝ) ^ (-θ : ℝ) ≤ 1 := by
      rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num) hθ.le)
    have e : r2 = (1 / 2) * (2 : ℝ) ^ (-θ : ℝ) := by
      rw [hr2_def,
        show (1 / 2 : ℝ) = (2 : ℝ) ^ ((-1 : ℝ)) from by
          rw [Real.rpow_neg_one]
          norm_num,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    rw [e]
    have hpos := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (-θ)
    linarith
  set rs := (2 : ℝ) ^ (-(1 - θ) / 2 : ℝ) with hrs_def
  set r2s := (2 : ℝ) ^ (-(1 + θ) / 2 : ℝ) with hr2s_def
  have hrs2 : rs ^ 2 = r := by
    rw [hrs_def, hr_def, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  have hr2s2 : r2s ^ 2 = r2 := by
    rw [hr2s_def, hr2_def, ← Real.rpow_natCast _ 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  have hprod : r2s * rs = 1 / 2 := by
    rw [hr2s_def, hrs_def, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      show (-(1 + θ) / 2 + -(1 - θ) / 2 : ℝ) = -1 by ring, Real.rpow_neg_one]
    norm_num
  have hpow2 : ∀ n : ℕ, (r2s ^ n) * (rs ^ n) = (2 ^ n : ℝ)⁻¹ := by
    intro n
    rw [← mul_pow, hprod, div_pow, one_pow, one_div]
  have hfsq : ∀ n : ℕ, (r2s ^ n) ^ 2 = r2 ^ n := by
    intro n
    rw [← pow_mul, mul_comm n 2, pow_mul, hr2s2]
  have hgsq : ∀ n : ℕ, (rs ^ n) ^ 2 = r ^ n := by
    intro n
    rw [← pow_mul, mul_comm n 2, pow_mul, hrs2]
  -- Cauchy–Schwarz across levels, on partial sums.
  have hCS : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (2 ^ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 ^ n),
          (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 ≤
        (∑ n ∈ Finset.range N, r2 ^ n) *
          ∑ n ∈ Finset.range N, r ^ n *
            (∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 := by
    intro N
    have hcs : (∑ n ∈ Finset.range N, r2s ^ n * (rs ^ n *
          ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|)) ^ 2 ≤
        (∑ n ∈ Finset.range N, (r2s ^ n) ^ 2) *
          ∑ n ∈ Finset.range N, (rs ^ n *
            ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    have e1 : ∀ n ∈ Finset.range N, r2s ^ n * (rs ^ n *
          ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) =
        (2 ^ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 ^ n),
          (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| := by
      intro n _
      rw [← mul_assoc, hpow2 n]
    have e3 : ∀ n ∈ Finset.range N, (rs ^ n *
          ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 =
        r ^ n * (∑ j ∈ Finset.range (2 ^ n),
          (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 := by
      intro n _
      rw [mul_pow, hgsq n]
    rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl (fun n _ => hfsq n),
      Finset.sum_congr rfl e3] at hcs
    exact hcs
  -- Summability of the three series.
  have hS1sum : Summable fun n : ℕ => r2 ^ n :=
    summable_geometric_of_lt_one hr20.le hr2l1
  have hS1 : (∑' n : ℕ, r2 ^ n) ≤ 2 := by
    rw [tsum_geometric_of_lt_one hr20.le hr2l1]
    have hpos : (0 : ℝ) < 1 - r2 := sub_pos.mpr hr2l1
    rw [← one_div, div_le_iff₀ hpos]
    linarith [hr21]
  have hS2sum : Summable fun n : ℕ => r ^ n *
      (∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
        |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => r ^ n * 1) ?_ ?_ ?_
    · intro n
      exact mul_nonneg (pow_nonneg hr0.le n) (sq_nonneg _)
    · intro n
      exact mul_le_mul_of_nonneg_left (pow_le_one₀ (hA0 n) (hA1 n)) (pow_nonneg hr0.le n)
    · have e : (fun n : ℕ => r ^ n * 1) = fun n => r ^ n := by
        funext n
        rw [mul_one]
      rw [e]
      exact summable_geometric_of_lt_one hr0.le hr1
  have hUsum : Summable fun n : ℕ => r ^ n *
      ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
        (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => r ^ n * 1) ?_ ?_ ?_
    · intro n
      exact mul_nonneg (pow_nonneg hr0.le n) (hB0 n)
    · intro n
      exact mul_le_mul_of_nonneg_left (hB1 n) (pow_nonneg hr0.le n)
    · have e : (fun n : ℕ => r ^ n * 1) = fun n => r ^ n := by
        funext n
        rw [mul_one]
      rw [e]
      exact summable_geometric_of_lt_one hr0.le hr1
  have hS2leU : (∑' n : ℕ, r ^ n *
        (∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2) ≤
      ∑' n : ℕ, r ^ n * ∑ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
          (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 :=
    hS2sum.tsum_le_tsum
      (fun n => mul_le_mul_of_nonneg_left (hA2B n) (pow_nonneg hr0.le n)) hUsum
  have hTsum : Summable fun n : ℕ => (2 ^ n : ℝ)⁻¹ *
      ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
        |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)| := by
    refine Summable.of_nonneg_of_le (f := fun n : ℕ => (2 ^ n : ℝ)⁻¹ * 1) ?_ ?_ ?_
    · intro n
      exact mul_nonneg (by positivity) (hA0 n)
    · intro n
      exact mul_le_mul_of_nonneg_left (hA1 n) (by positivity)
    · have e : (fun n : ℕ => (2 ^ n : ℝ)⁻¹ * 1) = fun n => (1 / 2 : ℝ) ^ n := by
        funext n
        rw [mul_one, div_pow, one_pow, one_div]
      rw [e]
      exact summable_geometric_of_lt_one (by norm_num) (by norm_num)
  -- Pass the partial-sum Cauchy–Schwarz to the limit.
  have hPbound : ∀ N : ℕ,
      (∑ n ∈ Finset.range N, (2 ^ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 ^ n),
          (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 ≤
        (∑' n : ℕ, r2 ^ n) * ∑' n : ℕ, r ^ n *
          (∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
            |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 := by
    intro N
    refine (hCS N).trans (mul_le_mul ?_ ?_ ?_ ?_)
    · exact hS1sum.sum_le_tsum _ (fun n _ => pow_nonneg hr20.le n)
    · exact hS2sum.sum_le_tsum _ (fun n _ =>
        mul_nonneg (pow_nonneg hr0.le n) (sq_nonneg _))
    · exact Finset.sum_nonneg fun n _ => mul_nonneg (pow_nonneg hr0.le n) (sq_nonneg _)
    · exact tsum_nonneg fun n => pow_nonneg hr20.le n
  have hT2 : (∑' n : ℕ, (2 ^ n : ℝ)⁻¹ * ∑ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 ≤
      (∑' n : ℕ, r2 ^ n) * ∑' n : ℕ, r ^ n *
        (∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
          |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 :=
    le_of_tendsto_of_tendsto' (hTsum.hasSum.tendsto_sum_nat.pow 2) tendsto_const_nhds
      hPbound
  -- Assemble the constant `1/8`.
  have hchain : (beta h a b) ^ 2 ≤ (1 / 8) * ∑' n : ℕ, r ^ n *
      ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
        (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 := by
    calc (beta h a b) ^ 2 ≤ ((1 / 4) * ∑' n : ℕ, (2 ^ n : ℝ)⁻¹ *
            ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 :=
          pow_le_pow_left₀ hβ0 hmain 2
      _ = (1 / 16) * (∑' n : ℕ, (2 ^ n : ℝ)⁻¹ *
            ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 := by
          ring
      _ ≤ (1 / 16) * ((∑' n : ℕ, r2 ^ n) * ∑' n : ℕ, r ^ n *
            (∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2) :=
          mul_le_mul_of_nonneg_left hT2 (by norm_num)
      _ ≤ (1 / 16) * (2 * ∑' n : ℕ, r ^ n *
            (∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hS1
            (tsum_nonneg fun n => mul_nonneg (pow_nonneg hr0.le n) (sq_nonneg _))
      _ = (1 / 8) * ∑' n : ℕ, r ^ n *
            (∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
              |eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)|) ^ 2 := by
          ring
      _ ≤ (1 / 8) * ∑' n : ℕ, r ^ n *
            ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
              (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 :=
          mul_le_mul_of_nonneg_left hS2leU (by norm_num)
  -- Rewrite the target power as `r ^ n`.
  have htarget : (∑' n : ℕ, (2 : ℝ) ^ (-(n : ℝ) * (1 - θ)) *
        ∑ j ∈ Finset.range (2 ^ n), (dyadicImageLength h a b n j / (h b - h a)) *
          (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2) =
      ∑' n : ℕ, r ^ n * ∑ j ∈ Finset.range (2 ^ n),
        (dyadicImageLength h a b n j / (h b - h a)) *
          (eps h (dyadicCenter a b n j) (dyadicHalfLength a b n)) ^ 2 := by
    apply tsum_congr
    intro n
    have e : (-(n : ℝ) * (1 - θ)) = (-(1 - θ)) * (n : ℝ) := by ring
    rw [hr_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← e]
  rw [htarget]
  exact hchain

/-! ## Section 7: the entropy inequality -/

/-- **The derivative is the LAC density a.e.**: on `[u, v]` the LAC density
`g` satisfies `h = h u + ∫ g`; by the Lebesgue differentiation theorem the
indefinite integral of `g` has derivative `g` a.e., and since the two
functions agree in a neighbourhood of every interior point, `h' = g` a.e. -/
private theorem deriv_eq_density_ae (h : ℝ → ℝ)
    (hac : LocallyAbsolutelyContinuous h) {u v : ℝ} (huv : u < v) :
    ∃ g : ℝ → ℝ, IntervalIntegrable g volume u v ∧
      (∀ t : ℝ, t ∈ Set.Icc u v → h t = h u + ∫ s in u..t, g s) ∧
      ∀ᵐ x ∂volume, x ∈ Set.uIoc u v → deriv h x = g x := by
  obtain ⟨g, hg, hrep⟩ := hac.2 u v huv
  refine ⟨g, hg, hrep, ?_⟩
  have ht_ne : ∀ᵐ x ∂volume, x ≠ v := by simp [ae_iff, measure_singleton]
  filter_upwards [hg.ae_hasDerivAt_integral, ht_ne] with x hxL hxne hxI
  rw [Set.uIoc_of_le huv.le] at hxI
  have hxIoo : x ∈ Set.Ioo u v := ⟨hxI.1, lt_of_le_of_ne hxI.2 hxne⟩
  have hxmem : x ∈ Set.uIcc u v :=
    Set.uIcc_of_le huv.le ▸ Set.Ioc_subset_Icc_self hxI
  have hG : HasDerivAt (fun r => h u + ∫ q in u..r, g q) (g x) x :=
    (hxL hxmem u Set.left_mem_uIcc).const_add (h u)
  have heq : (fun r => h u + ∫ q in u..r, g q) =ᶠ[nhds x] h := by
    filter_upwards [Ioo_mem_nhds hxIoo.1 hxIoo.2] with r hr
    exact (hrep r (Set.Ioo_subset_Icc_self hr)).symm
  exact heq.deriv_eq ▸ hG.deriv

/-- **FTC from local absolute continuity**: `∫ t in u..v, h' = h v - h u`. -/
private theorem integral_deriv_eq_sub (h : ℝ → ℝ)
    (hac : LocallyAbsolutelyContinuous h) (u v : ℝ) :
    ∫ t in u..v, deriv h t = h v - h u := by
  have key : ∀ s t : ℝ, s < t → ∫ x in s..t, deriv h x = h t - h s := by
    intro s t hst
    obtain ⟨g, _hg, hrep, hae⟩ := deriv_eq_density_ae h hac hst
    calc ∫ x in s..t, deriv h x = ∫ x in s..t, g x :=
          intervalIntegral.integral_congr_ae hae
      _ = h t - h s := by
          have ht := hrep t (Set.right_mem_Icc.mpr hst.le)
          linarith
  rcases lt_trichotomy u v with hlt | rfl | hgt
  · exact key u v hlt
  · simp [intervalIntegral.integral_same]
  · rw [intervalIntegral.integral_symm, key v u hgt]; ring

/-- `h'` is integrable on every bounded interval. -/
private theorem integrableOn_deriv (h : ℝ → ℝ)
    (hac : LocallyAbsolutelyContinuous h) {u v : ℝ} (huv : u < v) :
    IntegrableOn (deriv h) (Set.Ioc u v) volume := by
  obtain ⟨g, hg, _, hae⟩ := deriv_eq_density_ae h hac huv
  apply hg.1.congr_fun_ae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  rw [Set.uIoc_of_le huv.le] at hae
  filter_upwards [hae] with x hx hxI
  exact (hx hxI).symm

/-- The arithmetic mean of `w = h'` over `[u, v]` is the difference quotient
of `h`. -/
private theorem weightMean_deriv (h : ℝ → ℝ)
    (hac : LocallyAbsolutelyContinuous h)
    {u v : ℝ} (_huv : u ≠ v) :
    weightMean (deriv h) u v = (h v - h u) / (v - u) := by
  unfold weightMean intervalAvg
  rw [integral_deriv_eq_sub h hac u v]

/-- For strictly monotone `h`, the mean of `h'` over a nontrivial interval is
strictly positive. -/
private theorem weightMean_deriv_pos (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    {u v : ℝ} (huv : u < v) :
    0 < weightMean (deriv h) u v := by
  rw [weightMean_deriv h hac (ne_of_lt huv)]
  exact div_pos (sub_pos.mpr (hh huv)) (sub_pos.mpr huv)

/-- `|ε_h(x, y)| ≤ 1` for every `y ≠ 0`: the numerator of `ε_h` is the
difference of two nonnegative increments of `h` whose sum is the
denominator. -/
private theorem abs_eps_le (h : ℝ → ℝ) (hh : StrictMono h)
    (x y : ℝ) (hy : y ≠ 0) : |eps h x y| ≤ 1 := by
  unfold eps
  rcases lt_or_gt_of_ne hy with hyneg | hypos
  · have h1 : h (x + y) < h x := hh (by linarith)
    have h2 : h x < h (x - y) := hh (by linarith)
    have hD : h (x + y) - h (x - y) < 0 := by linarith
    rw [abs_div, abs_of_neg hD, div_le_one (by linarith : 0 < -(h (x + y) - h (x - y)))]
    rw [abs_le]
    constructor <;> linarith
  · have h1 : h (x - y) < h x := hh (by linarith)
    have h2 : h x < h (x + y) := hh (by linarith)
    have hD : 0 < h (x + y) - h (x - y) := by linarith
    rw [abs_div, abs_of_pos hD, div_le_one hD, abs_le]
    constructor <;> linarith

/-- `ε_h(·, y)` is continuous for `y ≠ 0`: the denominator never vanishes for
strictly monotone `h`. -/
private theorem eps_continuous (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) {y : ℝ} (hy : y ≠ 0) :
    Continuous fun x => eps h x y := by
  have hden : ∀ x, h (x + y) - h (x - y) ≠ 0 := by
    intro x
    have hne : h (x - y) ≠ h (x + y) := fun he => hy (by
      have hxy : x - y = x + y := hh.injective he
      linarith)
    exact sub_ne_zero.mpr (Ne.symm hne)
  have hnum : Continuous fun x => h (x + y) + h (x - y) - 2 * h x :=
    ((hac.1.comp (continuous_id.add continuous_const)).add
      (hac.1.comp (continuous_id.sub continuous_const))).sub
      (continuous_const.mul hac.1)
  have hdenom : Continuous fun x => h (x + y) - h (x - y) :=
    (hac.1.comp (continuous_id.add continuous_const)).sub
      (hac.1.comp (continuous_id.sub continuous_const))
  exact hnum.div hdenom hden

/-- **The eps-split identity**: the product of the means of `w = h'` over the
two half-intervals `I⁻ = [x - y, x]`, `I⁺ = [x, x + y]` equals the squared
mean over the whole interval times `1 - ε_h(x, y)²`. -/
private theorem eps_split (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (x y : ℝ) (hy : y ≠ 0) :
    weightMean (deriv h) (x - y) x * weightMean (deriv h) x (x + y) =
      weightMean (deriv h) (x - y) (x + y) ^ 2 * (1 - eps h x y ^ 2) := by
  have hCA : h (x + y) - h (x - y) ≠ 0 := by
    have hne : h (x - y) ≠ h (x + y) := fun he => hy (by
      have hxy : x - y = x + y := hh.injective he
      linarith)
    exact sub_ne_zero.mpr (Ne.symm hne)
  have h2y : 2 * y ≠ 0 := mul_ne_zero (by norm_num) hy
  rw [weightMean_deriv h hac (show x - y ≠ x by intro he; apply hy; linarith),
      weightMean_deriv h hac (show x ≠ x + y by intro he; apply hy; linarith),
      weightMean_deriv h hac (show x - y ≠ x + y by intro he; apply hy; linarith)]
  have e1 : x - (x - y) = y := by ring
  have e2 : x + y - x = y := by ring
  have e3 : x + y - (x - y) = 2 * y := by ring
  rw [e1, e2, e3]
  unfold eps
  field_simp [hy, h2y, hCA]
  ring

/-- **Definition (Entropy defect)**: `D_w(K) = log((w)_K / m_K) ≥ 0`, the
arithmetic–geometric mean defect of the weight over `K = [a, b]`. -/
def entropyDefect (w : ℝ → ℝ) (a b : ℝ) : ℝ :=
  Real.log (weightMean w a b / weightGeomMean w a b)

/-- The set average over `Ioc u v` equals the interval average. -/
private theorem setAverage_Ioc_eq_intervalAvg (f : ℝ → ℝ) {u v : ℝ} (huv : u ≤ v) :
    ⨍ x in Set.Ioc u v, f x = intervalAvg f u v := by
  rw [MeasureTheory.setAverage_eq]
  unfold intervalAvg
  rw [Measure.real, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr huv),
    intervalIntegral.integral_of_le huv, smul_eq_mul]
  ring

/-- **Jensen for the entropy defect**: `D_w(K) ≥ 0`, the arithmetic mean of
`w = h'` dominates the geometric mean. -/
private theorem entropyDefect_nonneg (h : ℝ → ℝ)
    (_hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (hw : ∀ᵐ t ∂volume, 0 < deriv h t)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    {u v : ℝ} (huv : u < v) :
    0 ≤ entropyDefect (deriv h) u v := by
  have h0 : volume (Set.Ioc u v) ≠ 0 := by
    rw [Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr huv)).ne'
  have ht : volume (Set.Ioc u v) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hfi : IntegrableOn (fun t => Real.log (deriv h t)) (Set.Ioc u v) volume :=
    (hα u v huv).1
  have hgi : IntegrableOn (Real.exp ∘ fun t => Real.log (deriv h t))
      (Set.Ioc u v) volume := by
    apply (integrableOn_deriv h hac huv).congr_fun_ae
    filter_upwards [MeasureTheory.ae_restrict_of_ae hw] with x hx
    exact (Real.exp_log hx).symm
  have hJensen : Real.exp (⨍ x in Set.Ioc u v, Real.log (deriv h x)) ≤
      ⨍ x in Set.Ioc u v, Real.exp (Real.log (deriv h x)) :=
    convexOn_exp.map_set_average_le Real.continuous_exp.continuousOn
      isClosed_univ h0 ht
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hfi hgi
  have havg_eq : (⨍ x in Set.Ioc u v, Real.exp (Real.log (deriv h x))) =
      ⨍ x in Set.Ioc u v, deriv h x := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    congr 1
    apply setIntegral_congr_ae measurableSet_Ioc
    filter_upwards [hw] with x hx _
    exact Real.exp_log hx
  have hle : weightGeomMean (deriv h) u v ≤ weightMean (deriv h) u v := by
    unfold weightGeomMean weightMean
    rw [← setAverage_Ioc_eq_intervalAvg (fun t => Real.log (deriv h t)) huv.le,
      ← setAverage_Ioc_eq_intervalAvg (deriv h) huv.le, ← havg_eq]
    exact hJensen
  unfold entropyDefect
  apply Real.log_nonneg
  rw [one_le_div (by unfold weightGeomMean; positivity)]
  exact hle

/-- The entropy defect splits as the log of the arithmetic mean minus the
average of `log w`. -/
private theorem entropyDefect_eq (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    {u v : ℝ} (huv : u < v) :
    entropyDefect (deriv h) u v =
      Real.log (weightMean (deriv h) u v) -
        intervalAvg (fun t => Real.log (deriv h t)) u v := by
  unfold entropyDefect weightGeomMean
  rw [Real.log_div (ne_of_gt (weightMean_deriv_pos h hh hac huv))
    (Real.exp_ne_zero _), Real.log_exp]

/-- The dyadic radii `yₙ = 2⁻ⁿ y₀`. -/
private noncomputable def yRad (y₀ : ℝ) (n : ℕ) : ℝ := (2 ^ n : ℝ)⁻¹ * y₀

private theorem yRad_pos (hy₀ : 0 < y₀) (n : ℕ) : 0 < yRad y₀ n :=
  mul_pos (by positivity) hy₀

private theorem yRad_ne_zero (hy₀ : 0 < y₀) (n : ℕ) : yRad y₀ n ≠ 0 :=
  (yRad_pos hy₀ n).ne'

private theorem yRad_succ (y₀ : ℝ) (n : ℕ) : yRad y₀ (n + 1) = yRad y₀ n / 2 := by
  unfold yRad
  rw [pow_succ, mul_inv_rev]
  ring

/-- The test functions `ψₙ`: `ψ₀ = 1_{3J}` and
`ψ_{n+1}(u) = (ψₙ(u + yₙ/2) + ψₙ(u - yₙ/2))/2`. -/
private noncomputable def psiFn (a b y₀ : ℝ) : ℕ → ℝ → ℝ
  | 0 => Set.indicator (Set.Icc (a - (b - a)) (b + (b - a))) 1
  | n + 1 => fun u =>
      (psiFn a b y₀ n (u + yRad y₀ n / 2) + psiFn a b y₀ n (u - yRad y₀ n / 2)) / 2

private theorem psiFn_zero_apply (a b y₀ : ℝ) (u : ℝ) :
    psiFn a b y₀ 0 u =
      Set.indicator (Set.Icc (a - (b - a)) (b + (b - a))) 1 u := rfl

private theorem psiFn_succ_apply (a b y₀ : ℝ) (n : ℕ) (u : ℝ) :
    psiFn a b y₀ (n + 1) u =
      (psiFn a b y₀ n (u + yRad y₀ n / 2) +
        psiFn a b y₀ n (u - yRad y₀ n / 2)) / 2 := rfl

private theorem psiFn_nonneg (a b y₀ : ℝ) : ∀ n u, 0 ≤ psiFn a b y₀ n u := by
  intro n
  induction n with
  | zero =>
      intro u
      rw [psiFn_zero_apply]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) u
  | succ n ih =>
      intro u
      rw [psiFn_succ_apply]
      exact div_nonneg (add_nonneg (ih _) (ih _)) (by norm_num)

private theorem psiFn_le_one (a b y₀ : ℝ) : ∀ n u, psiFn a b y₀ n u ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro u
      rw [psiFn_zero_apply]
      by_cases hu : u ∈ Set.Icc (a - (b - a)) (b + (b - a))
      · rw [Set.indicator_of_mem hu]; exact le_rfl
      · rw [Set.indicator_of_notMem hu]; exact zero_le_one
  | succ n ih =>
      intro u
      rw [psiFn_succ_apply]
      have h1 := ih (u + yRad y₀ n / 2)
      have h2 := ih (u - yRad y₀ n / 2)
      linarith

private theorem psiFn_measurable (a b y₀ : ℝ) : ∀ n, Measurable (psiFn a b y₀ n) := by
  intro n
  induction n with
  | zero =>
      exact measurable_const.indicator measurableSet_Icc
  | succ n ih =>
      exact ((ih.comp (measurable_add_const _)).add
        (ih.comp (measurable_sub_const _))).div_const _

/-- `ψₙ = 1` on the interval `[a - yₙ, b + yₙ]`, by induction using
`y_{n+1} + yₙ/2 = yₙ`; the base case uses `y₀ ≤ |J|` so that
`[a - y₀, b + y₀] ⊆ 3J`. -/
private theorem psiFn_eq_one (a b y₀ : ℝ) (hy₀ : 0 < y₀) (hy₀le : y₀ ≤ b - a) :
    ∀ n, ∀ u ∈ Set.Icc (a - yRad y₀ n) (b + yRad y₀ n), psiFn a b y₀ n u = 1 := by
  intro n
  induction n with
  | zero =>
      intro u hu
      have hu' : u ∈ Set.Icc (a - y₀) (b + y₀) := by
        have : yRad y₀ 0 = y₀ := by simp [yRad]
        rwa [this] at hu
      rw [psiFn_zero_apply, Set.indicator_of_mem
        (show u ∈ Set.Icc (a - (b - a)) (b + (b - a)) from
          ⟨by linarith [hu'.1], by linarith [hu'.2]⟩)]
      rfl
  | succ n ih =>
      intro u hu
      rw [psiFn_succ_apply]
      have hc2 : yRad y₀ (n + 1) = yRad y₀ n / 2 := yRad_succ y₀ n
      rw [hc2] at hu
      have hnn : 0 ≤ yRad y₀ n / 2 := by linarith [yRad_pos hy₀ n]
      have hmem1 : u + yRad y₀ n / 2 ∈ Set.Icc (a - yRad y₀ n) (b + yRad y₀ n) :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have hmem2 : u - yRad y₀ n / 2 ∈ Set.Icc (a - yRad y₀ n) (b + yRad y₀ n) :=
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [ih _ hmem1, ih _ hmem2]
      norm_num

/-- `ψₙ = 1` on `J = [a, b]` itself. -/
private theorem psiFn_eq_one_of_mem (a b y₀ : ℝ) (hy₀ : 0 < y₀) (hy₀le : y₀ ≤ b - a)
    (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc a b) : psiFn a b y₀ n u = 1 := by
  apply psiFn_eq_one a b y₀ hy₀ hy₀le n u
  have hy : 0 ≤ yRad y₀ n := (yRad_pos hy₀ n).le
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- The support of `ψₙ` is contained in `3J` enlarged by
`sₙ = y₀(1 - 2⁻ⁿ)`: induction with `s_{n+1} = sₙ + yₙ/2`. -/
private theorem psiFn_eq_zero_of_far (a b y₀ : ℝ) (hy₀ : 0 < y₀) :
    ∀ n, ∀ u, u ∉ Set.Icc (a - (b - a) - y₀ * (1 - (2 ^ n : ℝ)⁻¹))
        (b + (b - a) + y₀ * (1 - (2 ^ n : ℝ)⁻¹)) → psiFn a b y₀ n u = 0 := by
  intro n
  induction n with
  | zero =>
      intro u hu
      simp only [pow_zero, inv_one, sub_self, mul_zero, sub_zero, add_zero] at hu
      rw [psiFn_zero_apply]
      exact Set.indicator_of_notMem hu _
  | succ n ih =>
      intro u hu
      have hs : y₀ * (1 - (2 ^ (n + 1) : ℝ)⁻¹) =
          y₀ * (1 - (2 ^ n : ℝ)⁻¹) + yRad y₀ n / 2 := by
        unfold yRad
        rw [pow_succ, mul_inv_rev]
        ring
      rw [hs] at hu
      rw [psiFn_succ_apply]
      have hc : 0 ≤ yRad y₀ n / 2 := by linarith [yRad_pos hy₀ n]
      have h1 : psiFn a b y₀ n (u + yRad y₀ n / 2) = 0 := by
        apply ih
        intro hmem
        rw [Set.mem_Icc] at hu hmem
        exact hu ⟨by linarith [hmem.1, hc], by linarith [hmem.2, hc]⟩
      have h2 : psiFn a b y₀ n (u - yRad y₀ n / 2) = 0 := by
        apply ih
        intro hmem
        rw [Set.mem_Icc] at hu hmem
        exact hu ⟨by linarith [hmem.1, hc], by linarith [hmem.2, hc]⟩
      rw [h1, h2]
      norm_num

/-- The support of `ψₙ` is contained in the fixed compact interval
`3J` enlarged by `y₀`. -/
private theorem psiFn_eq_zero_of_far' (a b y₀ : ℝ) (hy₀ : 0 < y₀) (n : ℕ) (u : ℝ)
    (hu : u ∉ Set.Icc (a - (b - a) - y₀) (b + (b - a) + y₀)) :
    psiFn a b y₀ n u = 0 := by
  apply psiFn_eq_zero_of_far a b y₀ hy₀ n u
  intro hmem
  have ht : 0 ≤ (2 ^ n : ℝ)⁻¹ := by positivity
  have hs : y₀ * (1 - (2 ^ n : ℝ)⁻¹) ≤ y₀ := by nlinarith
  rw [Set.mem_Icc] at hu hmem
  exact hu ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

/-- `ψₙ · F` is integrable for every continuous `F`: `ψₙ` is measurable,
bounded by `1`, vanishes outside a compact interval on which the continuous
`F` is bounded. -/
private theorem integrable_psiFn_mul (a b y₀ : ℝ) (hab : a < b) (hy₀ : 0 < y₀)
    (n : ℕ) {F : ℝ → ℝ} (hF : Continuous F) :
    Integrable (fun u => psiFn a b y₀ n u * F u) volume := by
  set K := Set.Icc (a - (b - a) - y₀) (b + (b - a) + y₀) with hK
  have hKne : K.Nonempty := ⟨a, by
    simp only [hK, Set.mem_Icc]
    constructor <;> linarith⟩
  obtain ⟨x₀, hx₀, hx₀max⟩ :=
    isCompact_Icc.exists_isMaxOn hKne (hF.abs.continuousOn)
  have hKfin : volume K ≠ ⊤ := by
    rw [hK, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hG : Integrable (Set.indicator K fun _ => |F x₀|) volume :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (hs := hKfin))
  apply hG.mono' ((psiFn_measurable a b y₀ n).fun_mul hF.measurable).aestronglyMeasurable
  filter_upwards with u
  by_cases hu : u ∈ K
  · have hbound : |F u| ≤ |F x₀| := hx₀max hu
    have hψ : |psiFn a b y₀ n u| ≤ 1 :=
      abs_le.mpr ⟨by linarith [psiFn_nonneg a b y₀ n u], psiFn_le_one a b y₀ n u⟩
    rw [Set.indicator_of_mem hu]
    simp only [Real.norm_eq_abs, abs_mul]
    calc |psiFn a b y₀ n u| * |F u| ≤ 1 * |F x₀| :=
          mul_le_mul hψ hbound (abs_nonneg _) (by norm_num)
      _ = |F x₀| := one_mul _
  · rw [psiFn_eq_zero_of_far' a b y₀ hy₀ n u (by rwa [hK] at hu),
      Set.indicator_of_notMem hu]
    simp

/-- `Uₙ(x) = log (w)_{I(x, yₙ)}`, the log arithmetic mean of `w = h'` over
the interval of radius `yₙ` around `x`. -/
private noncomputable def UFn (h : ℝ → ℝ) (y₀ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.log (weightMean (deriv h) (x - yRad y₀ n) (x + yRad y₀ n))

/-- `Vₙ(x) = α_{I(x, yₙ)}`, the mean of `α = log w` over the same interval. -/
private noncomputable def VFn (h : ℝ → ℝ) (y₀ : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  intervalAvg (fun t => Real.log (deriv h t)) (x - yRad y₀ n) (x + yRad y₀ n)

/-- `Uₙ` is continuous: by the FTC it is the log of a positive difference
quotient of the continuous `h`. -/
private theorem UFn_continuous (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (hy₀ : 0 < y₀) (n : ℕ) :
    Continuous (UFn h y₀ n) := by
  have hadd : Continuous fun x : ℝ => x + yRad y₀ n :=
    continuous_id.add continuous_const
  have hsub : Continuous fun x : ℝ => x - yRad y₀ n :=
    continuous_id.sub continuous_const
  have hc : Continuous fun x =>
      (h (x + yRad y₀ n) - h (x - yRad y₀ n)) / (2 * yRad y₀ n) :=
    ((hac.1.comp hadd).sub (hac.1.comp hsub)).div_const _
  have hne : ∀ x, (h (x + yRad y₀ n) - h (x - yRad y₀ n)) / (2 * yRad y₀ n) ≠ 0 := by
    intro x
    have hlt : h (x - yRad y₀ n) < h (x + yRad y₀ n) :=
      hh (by linarith [yRad_pos hy₀ n])
    exact div_ne_zero (sub_ne_zero.mpr (ne_of_gt hlt))
      (mul_ne_zero (by norm_num) (yRad_ne_zero hy₀ n))
  apply (hc.log hne).congr
  intro x
  unfold UFn
  rw [weightMean_deriv h hac
    (show x - yRad y₀ n ≠ x + yRad y₀ n by intro he; linarith [yRad_pos hy₀ n])]
  congr 1
  ring

/-- `Vₙ` is continuous: it is a difference quotient of the (continuous)
indefinite integral of `α = log w`. -/
private theorem VFn_continuous (h : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (_hy₀ : 0 < y₀) (n : ℕ) :
    Continuous (VFn h y₀ n) := by
  have hint : ∀ s t : ℝ,
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume s t := by
    intro s t
    rcases lt_trichotomy s t with hlt | rfl | hgt
    · exact hα s t hlt
    · simp [IntervalIntegrable]
    · exact (hα t s hgt).symm
  have hA : Continuous fun t => ∫ s in (0 : ℝ)..t, Real.log (deriv h s) :=
    intervalIntegral.continuous_primitive hint 0
  have hadd : Continuous fun x : ℝ => x + yRad y₀ n :=
    continuous_id.add continuous_const
  have hsub : Continuous fun x : ℝ => x - yRad y₀ n :=
    continuous_id.sub continuous_const
  have e1 : Continuous fun x : ℝ =>
      ∫ s in (0 : ℝ)..(x + yRad y₀ n), Real.log (deriv h s) := by
    simpa [Function.comp_def] using hA.comp hadd
  have e2 : Continuous fun x : ℝ =>
      ∫ s in (0 : ℝ)..(x - yRad y₀ n), Real.log (deriv h s) := by
    simpa [Function.comp_def] using hA.comp hsub
  have hcont : Continuous fun x =>
      ((∫ s in (0 : ℝ)..(x + yRad y₀ n), Real.log (deriv h s)) -
        ∫ s in (0 : ℝ)..(x - yRad y₀ n), Real.log (deriv h s)) / (2 * yRad y₀ n) :=
    (e1.sub e2).div_const (2 * yRad y₀ n)
  apply hcont.congr
  intro x
  show ((∫ s in (0 : ℝ)..(x + yRad y₀ n), Real.log (deriv h s)) -
      ∫ s in (0 : ℝ)..(x - yRad y₀ n), Real.log (deriv h s)) / (2 * yRad y₀ n) = _
  unfold VFn intervalAvg
  rw [intervalIntegral.integral_interval_sub_left (hint 0 (x + yRad y₀ n))
    (hint 0 (x - yRad y₀ n))]
  congr 1
  ring

/-- `Uₙ - Vₙ = D_w(I(x, yₙ))` pointwise. -/
private theorem UFn_sub_VFn (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (hy₀ : 0 < y₀) (n : ℕ) (x : ℝ) :
    UFn h y₀ n x - VFn h y₀ n x =
      entropyDefect (deriv h) (x - yRad y₀ n) (x + yRad y₀ n) := by
  rw [entropyDefect_eq h hh hac (by linarith [yRad_pos hy₀ n])]
  rfl

/-- **Step 1 (pointwise)**: the drop of `U` across one dyadic scale controls
`ε_h(x, yₙ)² / 2`, via the eps-split identity and `-log(1 - u) ≥ u`. -/
private theorem step1_pointwise (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (hy₀ : 0 < y₀) (n : ℕ) (x : ℝ) :
    (eps h x (yRad y₀ n)) ^ 2 / 2 ≤ UFn h y₀ n x -
      (UFn h y₀ (n + 1) (x - yRad y₀ n / 2) +
        UFn h y₀ (n + 1) (x + yRad y₀ n / 2)) / 2 := by
  have hc : 0 < yRad y₀ n := yRad_pos hy₀ n
  have hc2 : yRad y₀ (n + 1) = yRad y₀ n / 2 := yRad_succ y₀ n
  have hA : 0 < weightMean (deriv h) (x - yRad y₀ n) x :=
    weightMean_deriv_pos h hh hac (by linarith)
  have hB : 0 < weightMean (deriv h) x (x + yRad y₀ n) :=
    weightMean_deriv_pos h hh hac (by linarith)
  have hW : 0 < weightMean (deriv h) (x - yRad y₀ n) (x + yRad y₀ n) :=
    weightMean_deriv_pos h hh hac (by linarith)
  have hsplit := eps_split h hh hac x (yRad y₀ n) hc.ne'
  have h1ε : 0 < 1 - eps h x (yRad y₀ n) ^ 2 := by
    have hpos := mul_pos hA hB
    rw [hsplit] at hpos
    exact pos_of_mul_pos_right hpos (sq_nonneg _)
  have e1 : UFn h y₀ (n + 1) (x - yRad y₀ n / 2) =
      Real.log (weightMean (deriv h) (x - yRad y₀ n) x) := by
    unfold UFn
    rw [hc2, show x - yRad y₀ n / 2 - yRad y₀ n / 2 = x - yRad y₀ n by ring,
      show x - yRad y₀ n / 2 + yRad y₀ n / 2 = x by ring]
  have e2 : UFn h y₀ (n + 1) (x + yRad y₀ n / 2) =
      Real.log (weightMean (deriv h) x (x + yRad y₀ n)) := by
    unfold UFn
    rw [hc2, show x + yRad y₀ n / 2 - yRad y₀ n / 2 = x by ring,
      show x + yRad y₀ n / 2 + yRad y₀ n / 2 = x + yRad y₀ n by ring]
  rw [e1, e2]
  have hlogAB : Real.log (weightMean (deriv h) (x - yRad y₀ n) x) +
        Real.log (weightMean (deriv h) x (x + yRad y₀ n)) =
      2 * Real.log (weightMean (deriv h) (x - yRad y₀ n) (x + yRad y₀ n)) +
        Real.log (1 - eps h x (yRad y₀ n) ^ 2) := by
    rw [← Real.log_mul hA.ne' hB.ne', hsplit,
      Real.log_mul (sq_pos_of_pos hW).ne' h1ε.ne', Real.log_pow]
    ring
  rw [hlogAB]
  unfold UFn
  have hlog := Real.log_le_sub_one_of_pos h1ε
  linarith

/-- **The `V` averaging identity**: the mean of `α = log w` over
`I(x, yₙ)` is the average of the means over the two half-intervals. -/
private theorem VFn_avg (h : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (hy₀ : 0 < y₀) (n : ℕ) (x : ℝ) :
    VFn h y₀ n x =
      (VFn h y₀ (n + 1) (x - yRad y₀ n / 2) +
        VFn h y₀ (n + 1) (x + yRad y₀ n / 2)) / 2 := by
  have hc : 0 < yRad y₀ n := yRad_pos hy₀ n
  have hc2 : yRad y₀ (n + 1) = yRad y₀ n / 2 := yRad_succ y₀ n
  have hsum : ∫ t in (x - yRad y₀ n)..(x + yRad y₀ n), Real.log (deriv h t) =
      (∫ t in (x - yRad y₀ n)..x, Real.log (deriv h t)) +
        ∫ t in x..(x + yRad y₀ n), Real.log (deriv h t) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hα _ _ (by linarith)) (hα _ _ (by linarith))).symm
  unfold VFn intervalAvg
  rw [hc2, show x - yRad y₀ n / 2 - yRad y₀ n / 2 = x - yRad y₀ n by ring,
    show x - yRad y₀ n / 2 + yRad y₀ n / 2 = x by ring,
    show x + yRad y₀ n / 2 - yRad y₀ n / 2 = x by ring,
    show x + yRad y₀ n / 2 + yRad y₀ n / 2 = x + yRad y₀ n by ring,
    show x - (x - yRad y₀ n) = yRad y₀ n by ring,
    show x + yRad y₀ n - x = yRad y₀ n by ring,
    show x + yRad y₀ n - (x - yRad y₀ n) = 2 * yRad y₀ n by ring, hsum]
  field_simp [hc.ne']

/-- **Integration against the recursion**: for continuous `F`,
`∫ ψ_{n+1} · F = ∫ ψₙ · ((F(· - yₙ/2) + F(· + yₙ/2))/2)`, by the defining
recursion of `ψ` and translation invariance of Lebesgue measure. -/
private theorem integral_psiFn_succ (a b y₀ : ℝ) (hab : a < b) (hy₀ : 0 < y₀)
    (n : ℕ) {F : ℝ → ℝ} (hF : Continuous F) :
    ∫ x, psiFn a b y₀ (n + 1) x * F x =
      ∫ x, psiFn a b y₀ n x *
        ((F (x - yRad y₀ n / 2) + F (x + yRad y₀ n / 2)) / 2) := by
  set c := yRad y₀ n / 2 with hc_def
  have hG : Integrable (fun z => psiFn a b y₀ n z * F (z - c)) volume :=
    integrable_psiFn_mul a b y₀ hab hy₀ n (hF.comp (continuous_id.sub continuous_const))
  have hG' : Integrable (fun z => psiFn a b y₀ n z * F (z + c)) volume :=
    integrable_psiFn_mul a b y₀ hab hy₀ n (hF.comp (continuous_id.add continuous_const))
  have hi1 : Integrable (fun x => psiFn a b y₀ n (x + c) * F x) volume := by
    apply (hG.comp_add_right c).congr
    filter_upwards with x
    simp [add_sub_cancel_right]
  have hi2 : Integrable (fun x => psiFn a b y₀ n (x - c) * F x) volume := by
    apply (hG'.comp_sub_right c).congr
    filter_upwards with x
    simp [sub_add_cancel]
  have ht1 : ∫ x, psiFn a b y₀ n (x + c) * F x =
      ∫ z, psiFn a b y₀ n z * F (z - c) := by
    have h := integral_add_right_eq_self (μ := volume)
      (fun z => psiFn a b y₀ n z * F (z - c)) c
    simp only [add_sub_cancel_right] at h
    exact h
  have ht2 : ∫ x, psiFn a b y₀ n (x - c) * F x =
      ∫ z, psiFn a b y₀ n z * F (z + c) := by
    have h := integral_sub_right_eq_self (μ := volume)
      (fun z => psiFn a b y₀ n z * F (z + c)) c
    simp only [sub_add_cancel] at h
    exact h
  have heq : ∫ x, psiFn a b y₀ (n + 1) x * F x =
      ((∫ x, psiFn a b y₀ n (x + c) * F x) +
        ∫ x, psiFn a b y₀ n (x - c) * F x) / 2 := by
    have hpw : ∀ x, psiFn a b y₀ (n + 1) x * F x =
        (psiFn a b y₀ n (x + c) * F x + psiFn a b y₀ n (x - c) * F x) / 2 := by
      intro x
      rw [psiFn_succ_apply, ← hc_def]
      ring
    have hadd : (∫ x, psiFn a b y₀ n (x + c) * F x +
        psiFn a b y₀ n (x - c) * F x) =
        (∫ x, psiFn a b y₀ n (x + c) * F x) +
          ∫ x, psiFn a b y₀ n (x - c) * F x :=
      integral_add hi1 hi2
    exact (integral_congr_ae (Filter.Eventually.of_forall hpw)).trans
      ((integral_div 2 _).trans (congrArg (· / 2) hadd))
  have hcomb : ((∫ z, psiFn a b y₀ n z * F (z - c)) +
      ∫ z, psiFn a b y₀ n z * F (z + c)) / 2 =
      ∫ z, (psiFn a b y₀ n z * F (z - c) + psiFn a b y₀ n z * F (z + c)) / 2 :=
    (congrArg (· / 2) (integral_add hG hG').symm).trans (integral_div 2 _).symm
  rw [heq, ht1, ht2, hcomb]
  apply integral_congr_ae
  filter_upwards with x
  ring

/-- **Step 2 (one scale)**: the drop of `∫ ψₙ · Uₙ` dominates
`(1/2) ∫ ψₙ · ε_h(·, yₙ)²`. -/
private theorem step2 (a b y₀ : ℝ) (hab : a < b) (hy₀ : 0 < y₀) (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h) (n : ℕ) :
    (1 / 2) * ∫ x, psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2 ≤
      (∫ x, psiFn a b y₀ n x * UFn h y₀ n x) -
        ∫ x, psiFn a b y₀ (n + 1) x * UFn h y₀ (n + 1) x := by
  rw [integral_psiFn_succ a b y₀ hab hy₀ n (UFn_continuous h hh hac hy₀ (n + 1))]
  have havg_cont : Continuous fun x =>
      (UFn h y₀ (n + 1) (x - yRad y₀ n / 2) + UFn h y₀ (n + 1) (x + yRad y₀ n / 2)) / 2 :=
    (((UFn_continuous h hh hac hy₀ (n + 1)).comp (continuous_id.sub continuous_const)).add
      ((UFn_continuous h hh hac hy₀ (n + 1)).comp (continuous_id.add continuous_const))).div_const _
  have hiU : Integrable (fun x => psiFn a b y₀ n x * UFn h y₀ n x) volume :=
    integrable_psiFn_mul a b y₀ hab hy₀ n (UFn_continuous h hh hac hy₀ n)
  have hiAvg : Integrable (fun x => psiFn a b y₀ n x *
      ((UFn h y₀ (n + 1) (x - yRad y₀ n / 2) + UFn h y₀ (n + 1) (x + yRad y₀ n / 2)) / 2))
      volume :=
    integrable_psiFn_mul a b y₀ hab hy₀ n havg_cont
  have heps_cont : Continuous fun x => (eps h x (yRad y₀ n)) ^ 2 := by
    have hden : ∀ x, h (x + yRad y₀ n) - h (x - yRad y₀ n) ≠ 0 := by
      intro x
      have hlt : h (x - yRad y₀ n) < h (x + yRad y₀ n) :=
        hh (by linarith [yRad_pos hy₀ n])
      exact sub_ne_zero.mpr (ne_of_gt hlt)
    have hnum : Continuous fun x =>
        h (x + yRad y₀ n) + h (x - yRad y₀ n) - 2 * h x :=
      ((hac.1.comp (continuous_id.add continuous_const)).add
        (hac.1.comp (continuous_id.sub continuous_const))).sub
        (continuous_const.mul hac.1)
    have hdenom : Continuous fun x => h (x + yRad y₀ n) - h (x - yRad y₀ n) :=
      (hac.1.comp (continuous_id.add continuous_const)).sub
        (hac.1.comp (continuous_id.sub continuous_const))
    exact ((hnum.div hdenom hden).pow 2)
  have hiE : Integrable (fun x => psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2) volume :=
    integrable_psiFn_mul a b y₀ hab hy₀ n heps_cont
  have hpoint : ∀ x, psiFn a b y₀ n x * ((eps h x (yRad y₀ n)) ^ 2 / 2) ≤
      psiFn a b y₀ n x * (UFn h y₀ n x -
        ((UFn h y₀ (n + 1) (x - yRad y₀ n / 2) + UFn h y₀ (n + 1) (x + yRad y₀ n / 2)) / 2)) := by
    intro x
    apply mul_le_mul_of_nonneg_left _ (psiFn_nonneg a b y₀ n x)
    exact step1_pointwise h hh hac hy₀ n x
  have hsub : (∫ x, psiFn a b y₀ n x * UFn h y₀ n x) -
      ∫ x, psiFn a b y₀ n x * ((UFn h y₀ (n + 1) (x - yRad y₀ n / 2) +
        UFn h y₀ (n + 1) (x + yRad y₀ n / 2)) / 2) =
    ∫ x, psiFn a b y₀ n x * (UFn h y₀ n x -
      ((UFn h y₀ (n + 1) (x - yRad y₀ n / 2) + UFn h y₀ (n + 1) (x + yRad y₀ n / 2)) / 2)) :=
    (integral_sub hiU hiAvg).symm.trans
      (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring))
  have hhalf : ∫ x, psiFn a b y₀ n x * ((eps h x (yRad y₀ n)) ^ 2 / 2) =
      (1 / 2) * ∫ x, psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2 :=
    (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)).trans
      (integral_const_mul (1 / 2) _)
  rw [hsub, ← hhalf]
  exact MeasureTheory.integral_mono
    (integrable_psiFn_mul a b y₀ hab hy₀ n (heps_cont.div_const 2))
    (integrable_psiFn_mul a b y₀ hab hy₀ n
      ((UFn_continuous h hh hac hy₀ n).sub havg_cont))
    hpoint

/-- **Step 3 (one scale)**: `∫ ψₙ · Vₙ` is conserved, by the same translation
computation together with the `V` averaging identity. -/
private theorem step3 (a b y₀ : ℝ) (hab : a < b) (hy₀ : 0 < y₀) (h : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v) (n : ℕ) :
    ∫ x, psiFn a b y₀ (n + 1) x * VFn h y₀ (n + 1) x =
      ∫ x, psiFn a b y₀ n x * VFn h y₀ n x := by
  rw [integral_psiFn_succ a b y₀ hab hy₀ n (VFn_continuous h hα hy₀ (n + 1))]
  apply integral_congr_ae
  filter_upwards with x
  rw [VFn_avg h hα hy₀ n x]

/-- **Step 3 (iterated)**: `∫ ψₙ · Vₙ = ∫ ψ₀ · V₀` for every `n`. -/
private theorem step3_iterate (a b y₀ : ℝ) (hab : a < b) (hy₀ : 0 < y₀) (h : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v) (N : ℕ) :
    ∫ x, psiFn a b y₀ N x * VFn h y₀ N x =
      ∫ x, psiFn a b y₀ 0 x * VFn h y₀ 0 x := by
  induction N with
  | zero => rfl
  | succ k ih => rw [step3 a b y₀ hab hy₀ h hα k, ih]

/-- The interval `3J` concentric with `J = [a, b]`. -/
def tripleInterval (a b : ℝ) : ℝ × ℝ := (a - (b - a), b + (b - a))


/-- The set of rescaled entropy-defect averages whose supremum is
`entropyBound`: for each `y₀` with `0 < y₀ ≤ |J|`, the quantity
`(1/|3J|) ∫_{3J} D_w(I(x, y₀)) dx`. -/
def entropyBoundSet (w : ℝ → ℝ) (a b : ℝ) : Set ℝ :=
  { r : ℝ | ∃ y₀ : ℝ, 0 < y₀ ∧ y₀ ≤ b - a ∧
    r = (∫ x in (a - (b - a))..(b + (b - a)), entropyDefect w (x - y₀) (x + y₀)) /
        (3 * (b - a)) }

/-- **Definition**: `E_h(J) = sup_{0 < y₀ ≤ |J|} (1/|3J|) ∫_{3J} D_w(I(x, y₀)) dx`,
with `w = h'`.
Note: the supremum ranges over all `0 < y₀ ≤ |J|`, enlarging the paper's top
dyadic band `|J|/2 < y₀ ≤ |J|`; the enlarged supremum keeps every
`E_h`-statement of the paper true. -/
def entropyBound (w : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (entropyBoundSet w a b)

/-- **Lemma (Entropy inequality)**: for a bounded interval `J = [a, b]`,
`0 < y₀ ≤ |J|` and `y_n = 2^{-n} y₀`, every partial sum satisfies
`(1/2) ∑_{n < N} ∫_J ε_h(x, y_n)² dx ≤ ∫_{3J} D_w(I(x, y₀)) dx` —
from which summability of the series (and hence the `∑'` form of the
statement) follows. The hypotheses `h' > 0` a.e. and
`log h' ∈ L¹_loc` make `weightGeomMean` and `entropyDefect` meaningful. -/
theorem entropy_inequality (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (hw : ∀ᵐ t ∂volume, 0 < deriv h t)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (a b y₀ : ℝ) (hab : a < b) (hy₀ : 0 < y₀) (hy₀le : y₀ ≤ b - a) :
    ∀ N : ℕ, (1 / 2) * ∑ n ∈ Finset.range N,
        ∫ x in a..b, (eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 ≤
      ∫ x in (a - (b - a))..(b + (b - a)),
        entropyDefect (deriv h) (x - y₀) (x + y₀) := by
  intro N
  show (1 / 2) * ∑ n ∈ Finset.range N, ∫ x in a..b, (eps h x (yRad y₀ n)) ^ 2 ≤ _
  -- (i) each interval integral is dominated by the `ψₙ`-weighted one, since
  -- `ψₙ = 1` on `J` and the integrand is nonnegative.
  have hdom : ∀ n, (∫ x in a..b, (eps h x (yRad y₀ n)) ^ 2) ≤
      ∫ x, psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2 := by
    intro n
    have hcont : Continuous fun x => (eps h x (yRad y₀ n)) ^ 2 :=
      (eps_continuous h hh hac (yRad_ne_zero hy₀ n)).pow 2
    have h1 : ∀ x ∈ Set.Ioc a b, psiFn a b y₀ n x = 1 := fun x hx =>
      psiFn_eq_one_of_mem a b y₀ hy₀ hy₀le n (Set.Ioc_subset_Icc_self hx)
    have h2 : (∫ x in Set.Ioc a b, (eps h x (yRad y₀ n)) ^ 2) =
        ∫ x in Set.Ioc a b, psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      show (eps h x (yRad y₀ n)) ^ 2 = psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2
      rw [h1 x hx, one_mul]
    rw [intervalIntegral.integral_of_le hab.le, h2]
    exact setIntegral_le_integral (integrable_psiFn_mul a b y₀ hab hy₀ n hcont)
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (psiFn_nonneg a b y₀ n x) (sq_nonneg _))
  -- (ii) telescoping the per-scale inequalities of Step 2.
  have htele : ∀ M : ℕ, (1 / 2) * ∑ n ∈ Finset.range M,
        ∫ x, psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2 ≤
      (∫ x, psiFn a b y₀ 0 x * UFn h y₀ 0 x) -
        ∫ x, psiFn a b y₀ M x * UFn h y₀ M x := by
    intro M
    induction M with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ]
        have hk := step2 a b y₀ hab hy₀ h hh hac k
        have heq : (1 / 2) * ((∑ n ∈ Finset.range k,
              ∫ x, psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2) +
            ∫ x, psiFn a b y₀ k x * (eps h x (yRad y₀ k)) ^ 2) =
          (1 / 2) * (∑ n ∈ Finset.range k,
              ∫ x, psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2) +
            (1 / 2) * ∫ x, psiFn a b y₀ k x * (eps h x (yRad y₀ k)) ^ 2 := by ring
        rw [heq]
        linarith [ih, hk]
  -- (iii) the sum over `J` is dominated by the telescoped `ψ`-sum.
  have hsum : (1 / 2) * ∑ n ∈ Finset.range N,
        ∫ x in a..b, (eps h x (yRad y₀ n)) ^ 2 ≤
      (1 / 2) * ∑ n ∈ Finset.range N,
        ∫ x, psiFn a b y₀ n x * (eps h x (yRad y₀ n)) ^ 2 :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => hdom n) (by norm_num)
  -- (iv) endpoint decomposition: `U - V = D_w ≥ 0` and `∫ ψₙ Vₙ` is conserved.
  have hsplit0 : ∫ x, psiFn a b y₀ 0 x * (UFn h y₀ 0 x - VFn h y₀ 0 x) =
      (∫ x, psiFn a b y₀ 0 x * UFn h y₀ 0 x) -
        ∫ x, psiFn a b y₀ 0 x * VFn h y₀ 0 x :=
    (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)).trans
      (integral_sub (integrable_psiFn_mul a b y₀ hab hy₀ 0 (UFn_continuous h hh hac hy₀ 0))
        (integrable_psiFn_mul a b y₀ hab hy₀ 0 (VFn_continuous h hα hy₀ 0)))
  have hsplitN : ∫ x, psiFn a b y₀ N x * (UFn h y₀ N x - VFn h y₀ N x) =
      (∫ x, psiFn a b y₀ N x * UFn h y₀ N x) -
        ∫ x, psiFn a b y₀ N x * VFn h y₀ N x :=
    (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)).trans
      (integral_sub (integrable_psiFn_mul a b y₀ hab hy₀ N (UFn_continuous h hh hac hy₀ N))
        (integrable_psiFn_mul a b y₀ hab hy₀ N (VFn_continuous h hα hy₀ N)))
  have hVN : (∫ x, psiFn a b y₀ N x * VFn h y₀ N x) =
      ∫ x, psiFn a b y₀ 0 x * VFn h y₀ 0 x :=
    step3_iterate a b y₀ hab hy₀ h hα N
  have hnonneg : 0 ≤ ∫ x, psiFn a b y₀ N x * (UFn h y₀ N x - VFn h y₀ N x) := by
    apply MeasureTheory.integral_nonneg
    intro x
    show 0 ≤ psiFn a b y₀ N x * (UFn h y₀ N x - VFn h y₀ N x)
    rw [UFn_sub_VFn h hh hac hy₀ N x]
    exact mul_nonneg (psiFn_nonneg a b y₀ N x)
      (entropyDefect_nonneg h hh hac hw hα (by linarith [yRad_pos hy₀ N]))
  -- (v) the remaining `ψ₀`-integral is exactly the right-hand side.
  have hfinal : (∫ x, psiFn a b y₀ 0 x * (UFn h y₀ 0 x - VFn h y₀ 0 x)) =
      ∫ x in (a - (b - a))..(b + (b - a)),
        entropyDefect (deriv h) (x - y₀) (x + y₀) := by
    have hy0 : yRad y₀ 0 = y₀ := by simp [yRad]
    have hpw : ∀ x, psiFn a b y₀ 0 x * (UFn h y₀ 0 x - VFn h y₀ 0 x) =
        Set.indicator (Set.Icc (a - (b - a)) (b + (b - a)))
          (fun x => entropyDefect (deriv h) (x - y₀) (x + y₀)) x := by
      intro x
      rw [psiFn_zero_apply, UFn_sub_VFn h hh hac hy₀ 0 x, hy0]
      by_cases hx : x ∈ Set.Icc (a - (b - a)) (b + (b - a))
      · rw [Set.indicator_of_mem hx (1 : ℝ → ℝ), Set.indicator_of_mem hx]
        simp
      · rw [Set.indicator_of_notMem hx (1 : ℝ → ℝ), Set.indicator_of_notMem hx]
        simp
    rw [integral_congr_ae (Filter.Eventually.of_forall hpw),
      MeasureTheory.integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : a - (b - a) ≤ b + (b - a))]
  have hcomb : (1 / 2) * ∑ n ∈ Finset.range N,
        ∫ x in a..b, (eps h x (yRad y₀ n)) ^ 2 ≤
      ∫ x, psiFn a b y₀ 0 x * (UFn h y₀ 0 x - VFn h y₀ 0 x) := by
    have hN : (∫ x, psiFn a b y₀ N x * UFn h y₀ N x) =
        (∫ x, psiFn a b y₀ N x * (UFn h y₀ N x - VFn h y₀ N x)) +
          ∫ x, psiFn a b y₀ 0 x * VFn h y₀ 0 x := by
      linarith [hsplitN, hVN]
    have h0 : (∫ x, psiFn a b y₀ 0 x * UFn h y₀ 0 x) =
        (∫ x, psiFn a b y₀ 0 x * (UFn h y₀ 0 x - VFn h y₀ 0 x)) +
          ∫ x, psiFn a b y₀ 0 x * VFn h y₀ 0 x := by
      linarith [hsplit0]
    linarith [hsum, htele N, hN, h0, hnonneg]
  exact hcomb.trans hfinal.le

/-- `ε_h` is jointly measurable in `(x, y)`: it is a ratio of continuous
expressions in `h` (the diagonal `y = 0` only creates a harmless junk value). -/
private theorem eps_measurable (h : ℝ → ℝ) (hac : LocallyAbsolutelyContinuous h) :
    Measurable fun p : ℝ × ℝ => eps h p.1 p.2 := by
  have hc : Continuous h := hac.1
  have hnum : Continuous fun p : ℝ × ℝ => h (p.1 + p.2) + h (p.1 - p.2) - 2 * h p.1 :=
    ((hc.comp (continuous_fst.add continuous_snd)).add
      (hc.comp (continuous_fst.sub continuous_snd))).sub
        (continuous_const.mul (hc.comp continuous_fst))
  have hden : Continuous fun p : ℝ × ℝ => h (p.1 + p.2) - h (p.1 - p.2) :=
    (hc.comp (continuous_fst.add continuous_snd)).sub
      (hc.comp (continuous_fst.sub continuous_snd))
  show Measurable fun p : ℝ × ℝ =>
    (h (p.1 + p.2) + h (p.1 - p.2) - 2 * h p.1) / (h (p.1 + p.2) - h (p.1 - p.2))
  exact hnum.measurable.div hden.measurable

/-- The dyadic slabs `(2^{-(n+1)} L, 2^{-n} L]` for `n ≥ 0` cover `(0, L]`. -/
private theorem slab_iUnion {L : ℝ} (hL : 0 < L) :
    ⋃ n : ℕ, Set.Ioc (((2 : ℝ) ^ (n + 1))⁻¹ * L) (((2 : ℝ) ^ n)⁻¹ * L) =
      Set.Ioc 0 L := by
  ext y
  simp only [Set.mem_iUnion, Set.mem_Ioc]
  constructor
  · rintro ⟨n, h1, h2⟩
    have h2p1 : (0 : ℝ) < 2 ^ (n + 1) := pow_pos (by norm_num) _
    have h2p : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num) _
    refine ⟨(mul_pos (inv_pos.mpr h2p1) hL).trans h1, h2.trans ?_⟩
    have hone : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ h2p]
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    calc ((2 : ℝ) ^ n)⁻¹ * L ≤ 1 * L := mul_le_mul_of_nonneg_right hone hL.le
    _ = L := one_mul L
  · rintro ⟨h0, hyL⟩
    have hs : 1 ≤ L / y := by
      rw [le_div_iff₀ h0]
      simpa using hyL
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hs (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_, ?_⟩
    · -- `(2^{n+1})⁻¹ * L < y`, from `L / y < 2^{n+1}`
      have h2p1 : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := pow_pos (by norm_num) _
      have hn2' : L < y * (2 : ℝ) ^ (n + 1) := by
        have hlt := (div_lt_iff₀ h0).mp hn2
        nlinarith [hlt, mul_comm y ((2 : ℝ) ^ (n + 1))]
      have e : ((2 : ℝ) ^ (n + 1))⁻¹ * (y * (2 : ℝ) ^ (n + 1)) = y := by
        field_simp [h2p1.ne']
      rw [← e]
      exact mul_lt_mul_of_pos_left hn2' (inv_pos.mpr h2p1)
    · -- `y ≤ (2^n)⁻¹ * L`, from `2^n ≤ L / y`
      have h2p : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
      have hn1' : y * (2 : ℝ) ^ n ≤ L := by
        have hle := (le_div_iff₀ h0).mp hn1
        nlinarith [hle, mul_comm y ((2 : ℝ) ^ n)]
      have e : ((2 : ℝ) ^ n)⁻¹ * (y * (2 : ℝ) ^ n) = y := by
        field_simp [h2p.ne']
      rw [← e]
      exact mul_le_mul_of_nonneg_left hn1' (inv_pos.mpr h2p).le

/-- The dyadic slabs are pairwise disjoint. -/
private theorem slab_pairwise_disjoint {L : ℝ} (hL : 0 < L) :
    Pairwise (fun n m : ℕ =>
      Disjoint (Set.Ioc (((2 : ℝ) ^ (n + 1))⁻¹ * L) (((2 : ℝ) ^ n)⁻¹ * L))
        (Set.Ioc (((2 : ℝ) ^ (m + 1))⁻¹ * L) (((2 : ℝ) ^ m)⁻¹ * L))) := by
  have key : ∀ n m : ℕ, n < m →
      Disjoint (Set.Ioc (((2 : ℝ) ^ (n + 1))⁻¹ * L) (((2 : ℝ) ^ n)⁻¹ * L))
        (Set.Ioc (((2 : ℝ) ^ (m + 1))⁻¹ * L) (((2 : ℝ) ^ m)⁻¹ * L)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    rintro y ⟨h1, -⟩ ⟨-, h4⟩
    have hpow : ((2 : ℝ) ^ m)⁻¹ ≤ ((2 : ℝ) ^ (n + 1))⁻¹ :=
      (inv_le_inv₀ (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)).mpr
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n + 1 ≤ m))
    have := mul_le_mul_of_nonneg_right hpow hL.le
    linarith
  intro n m hnm
  rcases lt_or_gt_of_ne hnm with hlt | hgt
  · exact key n m hlt
  · exact (key m n hgt).symm

/-- **Change of variables on one dyadic slab**: the substitution
`y = 2^{-n} y₀` maps the top band `(L/2, L]` onto the `n`-th slab and
preserves `dy / y`. -/
private theorem slab_lintegral (h : ℝ → ℝ) (_hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (x L : ℝ) (hL : 0 < L) (n : ℕ) :
    ∫⁻ y in Set.Ioc (((2 : ℝ) ^ (n + 1))⁻¹ * L) (((2 : ℝ) ^ n)⁻¹ * L),
      ENNReal.ofReal ((eps h x y) ^ 2 / y) =
    ∫⁻ y₀ in Set.Ioc (L / 2) L,
      ENNReal.ofReal ((eps h x (((2 : ℝ) ^ n)⁻¹ * y₀)) ^ 2 / y₀) := by
  have hc : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := inv_pos.mpr (pow_pos (by norm_num) _)
  have hlow : ((2 : ℝ) ^ (n + 1))⁻¹ * L = ((2 : ℝ) ^ n)⁻¹ * (L / 2) := by
    rw [pow_succ, mul_inv]
    ring
  have hGm : Measurable fun y => ENNReal.ofReal ((eps h x y) ^ 2 / y) :=
    ENNReal.measurable_ofReal.comp
      ((((eps_measurable h hac).comp (measurable_const.prodMk measurable_id)).pow_const 2).div
        measurable_id)
  have hmap : (volume : Measure ℝ) =
      ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) • Measure.map (((2 : ℝ) ^ n)⁻¹ * ·) volume := by
    have e := Real.map_volume_mul_left (a := ((2 : ℝ) ^ n)⁻¹) hc.ne'
    rw [inv_inv, abs_of_pos (pow_pos (show (0 : ℝ) < 2 by norm_num) n)] at e
    rw [e, smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr (pow_nonneg (by norm_num) _)),
      inv_mul_cancel₀ (pow_pos (show (0 : ℝ) < 2 by norm_num) n).ne', ENNReal.ofReal_one,
      one_smul]
  have hind : ∀ y₀ : ℝ,
      (Set.Ioc (((2 : ℝ) ^ n)⁻¹ * (L / 2)) (((2 : ℝ) ^ n)⁻¹ * L)).indicator
          (fun y => ENNReal.ofReal ((eps h x y) ^ 2 / y)) (((2 : ℝ) ^ n)⁻¹ * y₀) =
        (Set.Ioc (L / 2) L).indicator
          (fun y₁ => ENNReal.ofReal ((eps h x (((2 : ℝ) ^ n)⁻¹ * y₁)) ^ 2 /
            (((2 : ℝ) ^ n)⁻¹ * y₁))) y₀ := by
    intro y₀
    by_cases hy₀ : y₀ ∈ Set.Ioc (L / 2) L
    · have hmem : ((2 : ℝ) ^ n)⁻¹ * y₀ ∈
          Set.Ioc (((2 : ℝ) ^ n)⁻¹ * (L / 2)) (((2 : ℝ) ^ n)⁻¹ * L) :=
        ⟨mul_lt_mul_of_pos_left hy₀.1 hc, mul_le_mul_of_nonneg_left hy₀.2 hc.le⟩
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hy₀]
    · have hnmem : ((2 : ℝ) ^ n)⁻¹ * y₀ ∉
          Set.Ioc (((2 : ℝ) ^ n)⁻¹ * (L / 2)) (((2 : ℝ) ^ n)⁻¹ * L) := by
        intro hmem
        exact hy₀ ⟨(mul_lt_mul_iff_of_pos_left hc).mp hmem.1,
          (mul_le_mul_iff_of_pos_left hc).mp hmem.2⟩
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hy₀]
  rw [hlow]
  calc ∫⁻ y in Set.Ioc (((2 : ℝ) ^ n)⁻¹ * (L / 2)) (((2 : ℝ) ^ n)⁻¹ * L),
          ENNReal.ofReal ((eps h x y) ^ 2 / y)
      = ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) •
          ∫⁻ y in Set.Ioc (((2 : ℝ) ^ n)⁻¹ * (L / 2)) (((2 : ℝ) ^ n)⁻¹ * L),
            ENNReal.ofReal ((eps h x y) ^ 2 / y)
              ∂(Measure.map (((2 : ℝ) ^ n)⁻¹ * ·) volume) := by
        conv_lhs => rw [hmap, Measure.restrict_smul, MeasureTheory.lintegral_smul_measure]
    _ = ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) •
          ∫⁻ y₀, (Set.Ioc (((2 : ℝ) ^ n)⁻¹ * (L / 2)) (((2 : ℝ) ^ n)⁻¹ * L)).indicator
            (fun y => ENNReal.ofReal ((eps h x y) ^ 2 / y)) (((2 : ℝ) ^ n)⁻¹ * y₀) := by
        congr 1
        have hlm := MeasureTheory.lintegral_map
          (f := (Set.Ioc (((2 : ℝ) ^ n)⁻¹ * (L / 2)) (((2 : ℝ) ^ n)⁻¹ * L)).indicator
            (fun y => ENNReal.ofReal ((eps h x y) ^ 2 / y)))
          (g := fun y => ((2 : ℝ) ^ n)⁻¹ * y) (μ := (volume : Measure ℝ))
          (hGm.indicator measurableSet_Ioc) (measurable_const_mul _)
        rw [← MeasureTheory.lintegral_indicator measurableSet_Ioc, hlm]
    _ = ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) •
          ∫⁻ y₀ in Set.Ioc (L / 2) L,
            ENNReal.ofReal ((eps h x (((2 : ℝ) ^ n)⁻¹ * y₀)) ^ 2 / (((2 : ℝ) ^ n)⁻¹ * y₀)) := by
        congr 1
        rw [MeasureTheory.lintegral_congr hind, MeasureTheory.lintegral_indicator
          measurableSet_Ioc]
    _ = ∫⁻ y₀ in Set.Ioc (L / 2) L,
          ENNReal.ofReal ((eps h x (((2 : ℝ) ^ n)⁻¹ * y₀)) ^ 2 / y₀) := by
        have hlm := MeasureTheory.lintegral_const_mul
          (r := ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹))
          (f := fun y₀ => ENNReal.ofReal ((eps h x (((2 : ℝ) ^ n)⁻¹ * y₀)) ^ 2 /
            (((2 : ℝ) ^ n)⁻¹ * y₀)))
          (μ := volume.restrict (Set.Ioc (L / 2) L))
          (hGm.comp (measurable_const_mul _))
        rw [smul_eq_mul, ← hlm]
        apply MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc
        intro y₀ hy₀
        have hy₀p : (0 : ℝ) < y₀ := by have h1 := hy₀.1; linarith [hL]
        show ENNReal.ofReal (((2 : ℝ) ^ n)⁻¹) *
            ENNReal.ofReal ((eps h x (((2 : ℝ) ^ n)⁻¹ * y₀)) ^ 2 / (((2 : ℝ) ^ n)⁻¹ * y₀)) =
          ENNReal.ofReal ((eps h x (((2 : ℝ) ^ n)⁻¹ * y₀)) ^ 2 / y₀)
        rw [← ENNReal.ofReal_mul hc.le]
        congr 1
        field_simp [hc.ne', hy₀p.ne']

/-- The entropy defect is integrable in `x` on compact intervals: it is the
difference of the continuous `U₀` and `V₀`. -/
theorem entropyDefect_integrableOn (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (y₀ : ℝ) (hy₀ : 0 < y₀) (u v : ℝ) :
    IntegrableOn (fun x => entropyDefect (deriv h) (x - y₀) (x + y₀))
      (Set.Icc u v) volume := by
  have hEq : (fun x => entropyDefect (deriv h) (x - y₀) (x + y₀)) =
      fun x => UFn h y₀ 0 x - VFn h y₀ 0 x := by
    funext x
    have hUV := (UFn_sub_VFn h hh hac hy₀ 0 x).symm
    simpa [yRad] using hUV
  rw [hEq]
  exact ((UFn_continuous h hh hac hy₀ 0).sub
    (VFn_continuous h hα hy₀ 0)).continuousOn.integrableOn_Icc

/-- `E_h(J) ≥ 0`: it dominates the (nonnegative) defect average at
`y₀ = |J|`. -/
theorem entropyBound_nonneg (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h)
    (hw : ∀ᵐ t ∂volume, 0 < deriv h t)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (a b : ℝ) (hab : a < b)
    (hE : BddAbove (entropyBoundSet (deriv h) a b)) :
    0 ≤ entropyBound (deriv h) a b := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hmem : (∫ x in (a - (b - a))..(b + (b - a)),
        entropyDefect (deriv h) (x - (b - a)) (x + (b - a))) / (3 * (b - a)) ∈
      entropyBoundSet (deriv h) a b :=
    ⟨b - a, hL, le_refl _, rfl⟩
  have hm := le_csSup hE hmem
  have hnn : (0 : ℝ) ≤ ∫ x in (a - (b - a))..(b + (b - a)),
      entropyDefect (deriv h) (x - (b - a)) (x + (b - a)) := by
    apply intervalIntegral.integral_nonneg (by linarith [hL])
    intro x _
    exact entropyDefect_nonneg h hh hac hw hα (by linarith)
  have h0 : (0 : ℝ) ≤ (∫ x in (a - (b - a))..(b + (b - a)),
      entropyDefect (deriv h) (x - (b - a)) (x + (b - a))) / (3 * (b - a)) :=
    div_nonneg hnn (by positivity)
  exact h0.trans hm

/-- The `lintegral` form of the Carleson corollary: the box integral of
`ε_h² / y` is at most `6 log 2 · E_h(J) · |J|` as an extended nonnegative
real. -/
theorem eps_carleson_lintegral (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (hw : ∀ᵐ t ∂volume, 0 < deriv h t)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (a b : ℝ) (hab : a < b)
    (hE : BddAbove (entropyBoundSet (deriv h) a b)) :
    ∫⁻ p in carlesonBox a b, ENNReal.ofReal ((eps h p.1 p.2) ^ 2 / p.2) ≤
      ENNReal.ofReal (6 * Real.log 2 * entropyBound (deriv h) a b * (b - a)) := by
  set L := b - a with hL_def
  have hL : 0 < L := sub_pos.mpr hab
  set E := entropyBound (deriv h) a b with hE_def
  have hE0 : 0 ≤ E := entropyBound_nonneg h hh hac hw hα a b hab hE
  have hme : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((eps h p.1 p.2) ^ 2 / p.2) :=
    ENNReal.measurable_ofReal.comp (((eps_measurable h hac).pow_const 2).div measurable_snd)
  have hH : ∀ n : ℕ, Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal ((eps h p.1 ((2 ^ n : ℝ)⁻¹ * p.2)) ^ 2 / p.2) := fun n =>
    ENNReal.measurable_ofReal.comp
      ((((eps_measurable h hac).comp
        (measurable_fst.prodMk (measurable_const.mul measurable_snd))).pow_const 2).div
          measurable_snd)
  -- the key per-`y₀` bound: the dyadic sum of `∫_J ε_h(x, 2^{-n} y₀)² dx`
  -- is at most `6 E_h(J) |J|`, by the entropy inequality and the definition
  -- of `E_h`.
  have hkey : ∀ y₀ ∈ Set.Ioc (L / 2) L,
      (∑' n : ℕ, ∫⁻ x in Set.Ioc a b,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2)) ≤
        ENNReal.ofReal (6 * E * L) := by
    intro y₀ hy₀
    have hy₀pos : 0 < y₀ := by have h1 := hy₀.1; linarith [hL]
    have hy₀le : y₀ ≤ L := hy₀.2
    have hint : ∀ n : ℕ, IntegrableOn (fun x => (eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2)
        (Set.Ioc a b) volume := fun n =>
      ((eps_continuous h hh hac
        (mul_ne_zero (inv_ne_zero (pow_ne_zero n two_ne_zero)) hy₀pos.ne')).pow
          2).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    have hrw : ∀ n : ℕ, (∫⁻ x in Set.Ioc a b,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2)) =
        ENNReal.ofReal (∫ x in a..b, (eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2) := by
      intro n
      have h2 : (∫⁻ x in Set.Ioc a b,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2)) < ⊤ := by
        have hf := (hint n).hasFiniteIntegral
        rw [hasFiniteIntegral_iff_enorm] at hf
        have hae : Filter.EventuallyEq (MeasureTheory.ae (volume.restrict (Set.Ioc a b)))
            (fun x => ‖(eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2‖ₑ)
            (fun x => ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2)) :=
          Filter.Eventually.of_forall fun x => by
            show ‖(eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2‖ₑ =
              ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2)
            rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        rwa [lintegral_congr_ae hae] at hf
      have h1 : (∫ x in Set.Ioc a b, (eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2) =
          (∫⁻ x in Set.Ioc a b,
            ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2)).toReal :=
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun _ => sq_nonneg _) (hint n).aestronglyMeasurable
      rw [intervalIntegral.integral_of_le hab.le, h1, ENNReal.ofReal_toReal h2.ne]
    rw [tsum_congr hrw]
    apply ENNReal.tsum_le_of_sum_range_le
    intro N
    rw [← ENNReal.ofReal_sum_of_nonneg fun n _ =>
      intervalIntegral.integral_nonneg hab.le fun x _ => sq_nonneg _]
    apply ENNReal.ofReal_le_ofReal
    have hD_le : (∫ x in (a - L)..(b + L),
        entropyDefect (deriv h) (x - y₀) (x + y₀)) ≤ E * (3 * L) := by
      have hmem : (∫ x in (a - L)..(b + L),
            entropyDefect (deriv h) (x - y₀) (x + y₀)) / (3 * L) ∈
          entropyBoundSet (deriv h) a b :=
        ⟨y₀, hy₀pos, hy₀le, rfl⟩
      have hm : (∫ x in (a - L)..(b + L),
            entropyDefect (deriv h) (x - y₀) (x + y₀)) / (3 * L) ≤ E :=
        le_csSup hE hmem
      have h3L : (0 : ℝ) < 3 * L := by positivity
      rwa [div_le_iff₀ h3L] at hm
    have hEI := entropy_inequality h hh hac hw hα a b y₀ hab hy₀pos hy₀le N
    have hring : (6 : ℝ) * E * L = 2 * (E * (3 * L)) := by ring
    linarith [hEI, hD_le]
  -- the master identity: the box `lintegral` as a `y₀`-integral of dyadic sums
  have hmaster : ∫⁻ p in carlesonBox a b, ENNReal.ofReal ((eps h p.1 p.2) ^ 2 / p.2) =
      ∫⁻ y₀ in Set.Ioc (L / 2) L, ENNReal.ofReal (y₀⁻¹) *
        (∑' n : ℕ, ∫⁻ x in Set.Ioc a b,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2)) := by
    have hprod : (∫⁻ p in carlesonBox a b, ENNReal.ofReal ((eps h p.1 p.2) ^ 2 / p.2)) =
        ∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc 0 L,
          ENNReal.ofReal ((eps h x y) ^ 2 / y) := by
      rw [carlesonBox, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
      exact MeasureTheory.lintegral_prod _ hme.aemeasurable
    rw [hprod]
    have hinner : ∀ x : ℝ, (∫⁻ y in Set.Ioc 0 L, ENNReal.ofReal ((eps h x y) ^ 2 / y)) =
        ∑' n : ℕ, ∫⁻ y₀ in Set.Ioc (L / 2) L,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀) := by
      intro x
      rw [← slab_iUnion hL,
        MeasureTheory.lintegral_iUnion (fun _ => measurableSet_Ioc) (slab_pairwise_disjoint hL)]
      exact tsum_congr fun n => slab_lintegral h hh hac x L hL n
    rw [MeasureTheory.lintegral_congr fun x => hinner x]
    have hFmeas : ∀ n : ℕ, Measurable fun x =>
        ∫⁻ y₀ in Set.Ioc (L / 2) L,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀) :=
      fun n => Measurable.lintegral_prod_right (f := fun x y₀ =>
        ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀)) (hH n)
    have hH₂ : ∀ n : ℕ, Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal ((eps h p.2 ((2 ^ n : ℝ)⁻¹ * p.1)) ^ 2 / p.1) := fun n =>
      ENNReal.measurable_ofReal.comp
        ((((eps_measurable h hac).comp
          (measurable_snd.prodMk (measurable_const.mul measurable_fst))).pow_const 2).div
            measurable_fst)
    have hGmeas : ∀ n : ℕ, Measurable fun y₀ =>
        ∫⁻ x in Set.Ioc a b,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀) :=
      fun n => Measurable.lintegral_prod_right (f := fun y₀ x =>
        ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀)) (hH₂ n)
    rw [MeasureTheory.lintegral_tsum (fun n => (hFmeas n).aemeasurable)]
    have hswap : ∀ n : ℕ, (∫⁻ x in Set.Ioc a b, ∫⁻ y₀ in Set.Ioc (L / 2) L,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀)) =
        ∫⁻ y₀ in Set.Ioc (L / 2) L, ∫⁻ x in Set.Ioc a b,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀) := by
      intro n
      have h1 : (∫⁻ z, (fun p : ℝ × ℝ =>
              ENNReal.ofReal ((eps h p.1 ((2 ^ n : ℝ)⁻¹ * p.2)) ^ 2 / p.2)) z
            ∂((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc (L / 2) L)))) =
          ∫⁻ x in Set.Ioc a b, ∫⁻ y₀ in Set.Ioc (L / 2) L,
            ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀) :=
        MeasureTheory.lintegral_prod _ (hH n).aemeasurable
      have h2 : (∫⁻ z, (fun p : ℝ × ℝ =>
              ENNReal.ofReal ((eps h p.1 ((2 ^ n : ℝ)⁻¹ * p.2)) ^ 2 / p.2)) z
            ∂((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc (L / 2) L)))) =
          ∫⁻ y₀ in Set.Ioc (L / 2) L, ∫⁻ x in Set.Ioc a b,
            ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀) :=
        MeasureTheory.lintegral_prod_symm' _ (hH n)
      rw [← h1, h2]
    rw [tsum_congr hswap, ← MeasureTheory.lintegral_tsum (fun n => (hGmeas n).aemeasurable)]
    apply MeasureTheory.lintegral_congr
    intro y₀
    have hfactor : ∀ n : ℕ, (∫⁻ x in Set.Ioc a b,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2 / y₀)) =
        ENNReal.ofReal (y₀⁻¹) * ∫⁻ x in Set.Ioc a b,
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2) := by
      intro n
      have hm' : Measurable fun x =>
          ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2) :=
        ENNReal.measurable_ofReal.comp
          (((eps_measurable h hac).comp (measurable_id.prodMk measurable_const)).pow_const 2)
      rw [← MeasureTheory.lintegral_const_mul _ hm']
      apply MeasureTheory.lintegral_congr
      intro x
      by_cases hy : 0 < y₀
      · rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hy.le)]
        congr 1
        rw [div_eq_mul_inv]
        exact mul_comm _ _
      · push Not at hy
        rw [ENNReal.ofReal_of_nonpos (inv_nonpos.mpr hy), zero_mul,
          ENNReal.ofReal_of_nonpos (div_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hy)]
    rw [tsum_congr hfactor, ENNReal.tsum_mul_left]
  rw [hmaster]
  have hE6L : (0 : ℝ) ≤ 6 * E * L := mul_nonneg (mul_nonneg (by norm_num) hE0) hL.le
  calc ∫⁻ y₀ in Set.Ioc (L / 2) L, ENNReal.ofReal (y₀⁻¹) *
          (∑' n : ℕ, ∫⁻ x in Set.Ioc a b,
            ENNReal.ofReal ((eps h x ((2 ^ n : ℝ)⁻¹ * y₀)) ^ 2))
      ≤ ∫⁻ y₀ in Set.Ioc (L / 2) L,
          ENNReal.ofReal (y₀⁻¹) * ENNReal.ofReal (6 * E * L) := by
        apply MeasureTheory.lintegral_mono_ae
        rw [ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall fun y₀ hy₀ =>
          mul_le_mul_of_nonneg_left (hkey y₀ hy₀) zero_le
    _ = ENNReal.ofReal (6 * E * L) * ∫⁻ y₀ in Set.Ioc (L / 2) L,
          ENNReal.ofReal (y₀⁻¹) := by
        rw [MeasureTheory.lintegral_congr fun y₀ => mul_comm _ _]
        exact MeasureTheory.lintegral_const_mul _
          (ENNReal.measurable_ofReal.comp measurable_id.inv)
    _ = ENNReal.ofReal (6 * E * L) * ENNReal.ofReal (Real.log 2) := by
        congr 1
        have hsub : Set.Icc (L / 2) L ⊆ {(0 : ℝ)}ᶜ := by
          intro x hx
          have h2 : (0 : ℝ) < x := lt_of_lt_of_le (by linarith [hL]) hx.1
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact ne_of_gt h2
        have hii : IntegrableOn (fun y₀ : ℝ => y₀⁻¹) (Set.Ioc (L / 2) L) volume :=
          (ContinuousOn.integrableOn_Icc (continuousOn_inv₀.mono hsub)).mono_set
            Set.Ioc_subset_Icc_self
        have h1 : (∫ y₀ in Set.Ioc (L / 2) L, y₀⁻¹) =
            (∫⁻ y₀ in Set.Ioc (L / 2) L, ENNReal.ofReal (y₀⁻¹)).toReal :=
          MeasureTheory.integral_eq_lintegral_of_nonneg_ae
            ((ae_restrict_iff' measurableSet_Ioc).mpr
              (Filter.Eventually.of_forall fun _ hy₀ =>
                inv_nonneg.mpr (by have h1 := hy₀.1; linarith [hL])))
            hii.aestronglyMeasurable
        have hfin : (∫⁻ y₀ in Set.Ioc (L / 2) L, ENNReal.ofReal (y₀⁻¹)) < ⊤ := by
          have hf := hii.hasFiniteIntegral
          rw [hasFiniteIntegral_iff_enorm] at hf
          have hae : Filter.EventuallyEq
              (MeasureTheory.ae (volume.restrict (Set.Ioc (L / 2) L)))
              (fun y₀ : ℝ => ‖y₀⁻¹‖ₑ) (fun y₀ => ENNReal.ofReal (y₀⁻¹)) := by
            show ∀ᵐ y₀ ∂(volume.restrict (Set.Ioc (L / 2) L)), _ = _
            rw [ae_restrict_iff' measurableSet_Ioc]
            exact Filter.Eventually.of_forall fun y₀ hy₀ => by
              show ‖y₀⁻¹‖ₑ = ENNReal.ofReal (y₀⁻¹)
              rw [← ofReal_norm, Real.norm_eq_abs,
                abs_of_nonneg (inv_nonneg.mpr (by have h1 := hy₀.1; linarith [hL]))]
          rwa [lintegral_congr_ae hae] at hf
        rw [← ENNReal.ofReal_toReal hfin.ne, ← h1,
          ← intervalIntegral.integral_of_le (by linarith [hL] : L / 2 ≤ L),
          integral_inv_of_pos (by linarith [hL] : (0 : ℝ) < L / 2) hL]
        have hLL : L / (L / 2) = 2 := by field_simp [hL.ne']
        rw [hLL]
    _ = ENNReal.ofReal (6 * Real.log 2 * E * L) := by
        rw [← ENNReal.ofReal_mul hE6L]
        congr 1
        ring

/-- **Corollary (Carleson bound for `ε_h`)**: for every bounded interval `J`,
`∬_{Q_J} ε_h(x, y)² dxdy/y ≤ 6 log 2 · E_h(J) · |J|`. (The `BddAbove`
hypothesis rules out the junk value `E_h(J) = 0` arising from an unbounded
defect set. As in `entropy_inequality`, `h' > 0` a.e. and `log h' ∈ L¹_loc`
keep the entropy defect meaningful.) -/
theorem eps_carleson_bound (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (hw : ∀ᵐ t ∂volume, 0 < deriv h t)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (a b : ℝ) (hab : a < b)
    (hE : BddAbove (entropyBoundSet (deriv h) a b)) :
    carlesonBoxIntegral (eps h) a b ≤
      6 * Real.log 2 * entropyBound (deriv h) a b * (b - a) := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hE0 := entropyBound_nonneg h hh hac hw hα a b hab hE
  have hlint := eps_carleson_lintegral h hh hac hw hα a b hab hE
  have hmeas : Measurable fun p : ℝ × ℝ => (eps h p.1 p.2) ^ 2 / p.2 :=
    ((eps_measurable h hac).pow_const 2).div measurable_snd
  have hbox : MeasurableSet (carlesonBox a b) := measurableSet_Ioc.prod measurableSet_Ioc
  have hf0 : ∀ p ∈ carlesonBox a b, (0 : ℝ) ≤ (eps h p.1 p.2) ^ 2 / p.2 := by
    intro p hp
    exact div_nonneg (sq_nonneg _) (Set.mem_prod.mp hp).2.1.le
  -- integrability of the box integrand from the finite `lintegral`
  have hfi : HasFiniteIntegral (fun p : ℝ × ℝ => (eps h p.1 p.2) ^ 2 / p.2)
      (volume.restrict (carlesonBox a b)) := by
    rw [hasFiniteIntegral_iff_enorm]
    have hae : Filter.EventuallyEq (MeasureTheory.ae (volume.restrict (carlesonBox a b)))
        (fun p : ℝ × ℝ => ‖(eps h p.1 p.2) ^ 2 / p.2‖ₑ)
        (fun p => ENNReal.ofReal ((eps h p.1 p.2) ^ 2 / p.2)) := by
      show ∀ᵐ p ∂(volume.restrict (carlesonBox a b)), _ = _
      rw [ae_restrict_iff' hbox]
      exact Filter.Eventually.of_forall fun p hp => by
        show ‖(eps h p.1 p.2) ^ 2 / p.2‖ₑ = ENNReal.ofReal ((eps h p.1 p.2) ^ 2 / p.2)
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hf0 p hp)]
    rw [lintegral_congr_ae hae]
    exact hlint.trans_lt ENNReal.ofReal_lt_top
  have hint : Integrable (fun p : ℝ × ℝ => (eps h p.1 p.2) ^ 2 / p.2)
      (volume.restrict (carlesonBox a b)) := ⟨hmeas.aestronglyMeasurable, hfi⟩
  have hint' : Integrable (fun p : ℝ × ℝ => (eps h p.1 p.2) ^ 2 / p.2)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 (b - a)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ, ← carlesonBox]
    exact hint
  have hiter : (∫ x in Set.Ioc a b, ∫ y in Set.Ioc 0 (b - a), (eps h x y) ^ 2 / y) =
      ∫ p in carlesonBox a b, (eps h p.1 p.2) ^ 2 / p.2 := by
    rw [carlesonBox, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
    exact (MeasureTheory.integral_prod _ hint').symm
  have hconv : carlesonBoxIntegral (eps h) a b =
      (∫⁻ p in carlesonBox a b, ENNReal.ofReal ((eps h p.1 p.2) ^ 2 / p.2)).toReal := by
    unfold carlesonBoxIntegral
    rw [intervalIntegral.integral_of_le hab.le,
      setIntegral_congr_fun measurableSet_Ioc (fun x _ => intervalIntegral.integral_of_le hL.le),
      hiter,
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        ((ae_restrict_iff' hbox).mpr (Filter.Eventually.of_forall hf0))
        hint.aestronglyMeasurable]
  rw [hconv]
  have hfin : (∫⁻ p in carlesonBox a b, ENNReal.ofReal ((eps h p.1 p.2) ^ 2 / p.2)) ≠ ⊤ :=
    (hlint.trans_lt ENNReal.ofReal_lt_top).ne
  have hRHS : (0 : ℝ) ≤ 6 * Real.log 2 * entropyBound (deriv h) a b * (b - a) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) hE0) hL.le
  calc (∫⁻ p in carlesonBox a b, ENNReal.ofReal ((eps h p.1 p.2) ^ 2 / p.2)).toReal
      ≤ (ENNReal.ofReal
          (6 * Real.log 2 * entropyBound (deriv h) a b * (b - a))).toReal :=
        (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hlint
    _ = 6 * Real.log 2 * entropyBound (deriv h) a b * (b - a) :=
        ENNReal.toReal_ofReal hRHS

/-- **Lemma (Two bounds for `E_h`), part (a)**: if `w = h'` satisfies (A2)
with constant `A₀`, i.e. `(w)_K ≤ A₀ m_K` for every interval `K`, then
`E_h(J) ≤ log A₀` for every bounded interval `J`. (`hh`, `hac`, `hα` are the
standing hypotheses of this section: `h` strictly increasing and locally
absolutely continuous with `log h'` locally integrable; without them
`weightMean (deriv h)` need not be positive and the bound can fail.) -/
theorem entropy_bound_ainfty (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (A₀ : ℝ) (hA₀ : 1 ≤ A₀)
    (hA2 : WeightA2 (deriv h) A₀) (a b : ℝ) (hab : a < b) :
    entropyBound (deriv h) a b ≤ Real.log A₀ := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hA₀pos : (0 : ℝ) < A₀ := lt_of_lt_of_le zero_lt_one hA₀
  -- Pointwise: `D_w(K) ≤ log A₀` for every interval `K = [u, v]`.
  have hpt : ∀ u v : ℝ, u < v → entropyDefect (deriv h) u v ≤ Real.log A₀ := by
    intro u v huv
    have hgm : 0 < weightGeomMean (deriv h) u v := by
      unfold weightGeomMean; exact Real.exp_pos _
    have hmean : weightMean (deriv h) u v = (h v - h u) / (v - u) :=
      weightMean_deriv h hac (ne_of_lt huv)
    have hmeanpos : 0 < weightMean (deriv h) u v := by
      rw [hmean]
      exact div_pos (sub_pos.mpr (hh huv)) (sub_pos.mpr huv)
    have hratio_le : weightMean (deriv h) u v / weightGeomMean (deriv h) u v ≤ A₀ := by
      rw [div_le_iff₀ hgm]
      exact hA2 u v huv
    have hratio_pos : 0 < weightMean (deriv h) u v / weightGeomMean (deriv h) u v :=
      div_pos hmeanpos hgm
    unfold entropyDefect
    exact (Real.log_le_log_iff hratio_pos hA₀pos).mpr hratio_le
  unfold entropyBound
  refine csSup_le ⟨_, ⟨b - a, hL, le_refl _, rfl⟩⟩ ?_
  rintro r ⟨y₀, hy₀, hy₀le, rfl⟩
  have hAB : a - (b - a) ≤ b + (b - a) := by linarith
  have hint : IntegrableOn (fun x => entropyDefect (deriv h) (x - y₀) (x + y₀))
      (Set.Icc (a - (b - a)) (b + (b - a))) volume :=
    entropyDefect_integrableOn h hh hac hα y₀ hy₀ (a - (b - a)) (b + (b - a))
  have hintIntv : IntervalIntegrable
      (fun x => entropyDefect (deriv h) (x - y₀) (x + y₀)) volume
      (a - (b - a)) (b + (b - a)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr hint
  have hmono : (∫ x in (a - (b - a))..(b + (b - a)),
      entropyDefect (deriv h) (x - y₀) (x + y₀)) ≤
      ∫ _x in (a - (b - a))..(b + (b - a)), Real.log A₀ := by
    apply intervalIntegral.integral_mono_on hAB hintIntv intervalIntegrable_const
    intro x _
    exact hpt (x - y₀) (x + y₀) (by linarith)
  rw [intervalIntegral.integral_const, smul_eq_mul,
    show b + (b - a) - (a - (b - a)) = 3 * (b - a) by ring] at hmono
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (b - a)),
    mul_comm (Real.log A₀) (3 * (b - a))]
  exact hmono

/-! ## A Calderón–Zygmund argument for John–Nirenberg -/

/-- The level-`m` dyadic ancestor index (`m ≤ n`) of the level-`n` cell `j`. -/
private def ancIdx (n m j : ℕ) : ℕ := j / 2 ^ (n - m)

private lemma ancIdx_mul_le (n m j : ℕ) : ancIdx n m j * 2 ^ (n - m) ≤ j :=
  Nat.div_mul_le_self j (2 ^ (n - m))

private lemma lt_ancIdx_succ_mul (n m j : ℕ) : j < (ancIdx n m j + 1) * 2 ^ (n - m) := by
  have hpos : 0 < 2 ^ (n - m) := pow_pos (by norm_num) _
  have hdm : 2 ^ (n - m) * ancIdx n m j + j % 2 ^ (n - m) = j := Nat.div_add_mod j (2 ^ (n - m))
  have hmod : j % 2 ^ (n - m) < 2 ^ (n - m) := Nat.mod_lt j hpos
  have hdist : (ancIdx n m j + 1) * 2 ^ (n - m) =
      2 ^ (n - m) * ancIdx n m j + 2 ^ (n - m) := by ring
  omega

/-- The level-`n` dyadic cell `j` is contained in its level-`m` ancestor cell
(`m ≤ n`). -/
private lemma dyad_nested (a b : ℝ) (hab : a ≤ b) (n m j : ℕ) (hmn : m ≤ n) :
    dPt a b m (ancIdx n m j) ≤ dPt a b n j ∧
      dPt a b n (j + 1) ≤ dPt a b m (ancIdx n m j + 1) := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  have h2m : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hpow : (2 : ℝ) ^ n = 2 ^ m * 2 ^ (n - m) := by
    rw [← pow_add]; congr 1; omega
  have h1 : (ancIdx n m j : ℝ) * 2 ^ (n - m) ≤ (j : ℝ) := by exact_mod_cast ancIdx_mul_le n m j
  have h2 : (j : ℝ) + 1 ≤ ((ancIdx n m j : ℝ) + 1) * 2 ^ (n - m) := by
    have h := Nat.succ_le_of_lt (lt_ancIdx_succ_mul n m j)
    have hc : ((j + 1 : ℕ) : ℝ) ≤ (((ancIdx n m j + 1) * 2 ^ (n - m) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at hc
    linarith
  constructor
  · have goal1 : (ancIdx n m j : ℝ) * (2 : ℝ) ^ n ≤ (j : ℝ) * (2 : ℝ) ^ m := by
      rw [hpow]
      calc (ancIdx n m j : ℝ) * ((2 : ℝ) ^ m * 2 ^ (n - m))
          = (ancIdx n m j * 2 ^ (n - m) : ℝ) * (2 : ℝ) ^ m := by ring
        _ ≤ (j : ℝ) * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_right h1 h2m.le
    have key : (ancIdx n m j : ℝ) / (2 : ℝ) ^ m ≤ (j : ℝ) / (2 : ℝ) ^ n :=
      (div_le_div_iff₀ h2m h2n).mpr goal1
    unfold dPt
    have hthis := mul_le_mul_of_nonneg_left key hba
    rw [div_eq_mul_inv, div_eq_mul_inv] at hthis
    nlinarith [hthis]
  · have goal2 : ((j : ℝ) + 1) * (2 : ℝ) ^ m ≤ ((ancIdx n m j : ℝ) + 1) * (2 : ℝ) ^ n := by
      rw [hpow]
      calc ((j : ℝ) + 1) * (2 : ℝ) ^ m
          ≤ (((ancIdx n m j : ℝ) + 1) * 2 ^ (n - m)) * (2 : ℝ) ^ m :=
            mul_le_mul_of_nonneg_right h2 h2m.le
        _ = ((ancIdx n m j : ℝ) + 1) * ((2 : ℝ) ^ m * 2 ^ (n - m)) := by ring
    have key : ((j : ℝ) + 1) / (2 : ℝ) ^ n ≤ ((ancIdx n m j : ℝ) + 1) / (2 : ℝ) ^ m :=
      (div_le_div_iff₀ h2n h2m).mpr goal2
    unfold dPt
    have hthis := mul_le_mul_of_nonneg_left key hba
    rw [div_eq_mul_inv, div_eq_mul_inv] at hthis
    push_cast
    nlinarith [hthis]

/-- The half-open dyadic cell `[dPt a b n j, dPt a b n (j+1))`. -/
private def cellSet (a b : ℝ) (n j : ℕ) : Set ℝ :=
  Set.Ico (dPt a b n j) (dPt a b n (j + 1))

/-- The average of `α` over the level-`n`, index-`j` dyadic cell. -/
private noncomputable def cellAvg (α : ℝ → ℝ) (a b : ℝ) (n j : ℕ) : ℝ :=
  intervalAvg α (dPt a b n j) (dPt a b n (j + 1))

private lemma cellSet_disjoint_same_level (a b : ℝ) (hab : a < b) (n j1 j2 : ℕ)
    (hne : j1 ≠ j2) : Disjoint (cellSet a b n j1) (cellSet a b n j2) := by
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · apply Set.disjoint_left.mpr
    intro x hx1 hx2
    have hle : dPt a b n (j1 + 1) ≤ dPt a b n j2 := dPt_mono hab.le n (by omega)
    exact absurd (hle.trans hx2.1) (not_le.mpr hx1.2)
  · apply Set.disjoint_left.mpr
    intro x hx1 hx2
    have hle : dPt a b n (j2 + 1) ≤ dPt a b n j1 := dPt_mono hab.le n (by omega)
    exact absurd (hle.trans hx1.1) (not_le.mpr hx2.2)

private lemma cellSet_subset_ancestor (a b : ℝ) (hab : a ≤ b) (n m j : ℕ) (hmn : m ≤ n) :
    cellSet a b n j ⊆ cellSet a b m (ancIdx n m j) := by
  obtain ⟨h1, h2⟩ := dyad_nested a b hab n m j hmn
  intro x hx
  exact ⟨h1.trans hx.1, hx.2.trans_le h2⟩

/-- `(n, j)` is a Calderón–Zygmund cell for `α` on `[a, b]` relative to
reference value `ref` and threshold `τ`: the level-`n` average deviates from
`ref` by more than `τ`, and this is the *first* such deviation along the
cell's dyadic ancestry. -/
private def IsCZCell (α : ℝ → ℝ) (a b ref τ : ℝ) (n j : ℕ) : Prop :=
  j < 2 ^ n ∧ τ < |cellAvg α a b n j - ref| ∧
    ∀ m, m < n → |cellAvg α a b m (ancIdx n m j) - ref| ≤ τ

private lemma czCell_disjoint_le (α : ℝ → ℝ) (a b ref τ : ℝ) (hab : a < b)
    {n1 j1 n2 j2 : ℕ} (h1 : IsCZCell α a b ref τ n1 j1) (h2 : IsCZCell α a b ref τ n2 j2)
    (hle : n1 ≤ n2) (hne : (n1, j1) ≠ (n2, j2)) :
    Disjoint (cellSet a b n1 j1) (cellSet a b n2 j2) := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · subst heq
    exact cellSet_disjoint_same_level a b hab n1 j1 j2 (fun h => hne (by rw [h]))
  · have hsub : cellSet a b n2 j2 ⊆ cellSet a b n1 (ancIdx n2 n1 j2) :=
      cellSet_subset_ancestor a b hab.le n2 n1 j2 hlt.le
    have hne_idx : j1 ≠ ancIdx n2 n1 j2 := by
      intro heq
      have hb2 := h2.2.2 n1 hlt
      rw [← heq] at hb2
      exact absurd hb2 (not_le.mpr h1.2.1)
    exact Set.disjoint_left.mpr (fun x hx1 hx2 =>
      Set.disjoint_left.mp
        (cellSet_disjoint_same_level a b hab n1 j1 (ancIdx n2 n1 j2) hne_idx) hx1 (hsub hx2))

/-- Distinct Calderón–Zygmund cells are disjoint. -/
private lemma czCell_disjoint (α : ℝ → ℝ) (a b ref τ : ℝ) (hab : a < b)
    {n1 j1 n2 j2 : ℕ} (h1 : IsCZCell α a b ref τ n1 j1) (h2 : IsCZCell α a b ref τ n2 j2)
    (hne : (n1, j1) ≠ (n2, j2)) :
    Disjoint (cellSet a b n1 j1) (cellSet a b n2 j2) := by
  rcases le_total n1 n2 with hle | hle
  · exact czCell_disjoint_le α a b ref τ hab h1 h2 hle hne
  · exact (czCell_disjoint_le α a b ref τ hab h2 h1 hle (fun h => hne h.symm)).symm

/-- `α` is locally integrable on `ℝ` if it is interval integrable on every
bounded interval. -/
private lemma locallyIntegrable_of_forall_intervalIntegrable (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) :
    LocallyIntegrable α volume := by
  intro x
  refine ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : x - 1 ≤ x + 1)).mp
    (hα (x - 1) (x + 1) (by linarith))

/-- If `F(t) = ∫ x in c..t, α x` has derivative `α x` at `x`, then the average
of `α` over any shrinking pair of intervals `[l n, x]`, `[x, r n]` sandwiching
`x` converges to `α x`. -/
private lemma cellAvg_tendsto_of_hasDerivAt (α : ℝ → ℝ) (x : ℝ)
    (hint : ∀ u v : ℝ, IntervalIntegrable α volume u v)
    (hx : HasDerivAt (fun t => ∫ s in x..t, α s) (α x) x)
    {l r : ℕ → ℝ} (hlx : ∀ n, l n ≤ x) (hxr : ∀ n, x < r n)
    (hltend : Filter.Tendsto l Filter.atTop (nhds x))
    (hrtend : Filter.Tendsto r Filter.atTop (nhds x)) :
    Filter.Tendsto (fun n => intervalAvg α (l n) (r n)) Filter.atTop (nhds (α x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set F : ℝ → ℝ := fun t => ∫ s in x..t, α s with hF_def
  have hFx : F x = 0 := intervalIntegral.integral_same
  have hlo := hx.isLittleO.def (show (0:ℝ) < ε / 4 by linarith)
  rw [Metric.eventually_nhds_iff] at hlo
  obtain ⟨δ, hδ, hδ'⟩ := hlo
  have hbound : ∀ y : ℝ, dist y x < δ → |F y - (y - x) * α x| ≤ (ε / 4) * |y - x| := by
    intro y hy
    have := hδ' hy
    simp only [Real.norm_eq_abs, hFx, sub_zero] at this
    convert this using 2
  have hδl : ∀ᶠ n in Filter.atTop, dist (l n) x < δ := hltend.eventually (Metric.ball_mem_nhds x hδ)
  have hδr : ∀ᶠ n in Filter.atTop, dist (r n) x < δ := hrtend.eventually (Metric.ball_mem_nhds x hδ)
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [hδl, hδr] with n hln hrn
  have hbl := hbound (l n) hln
  have hbr := hbound (r n) hrn
  have hrl : l n < r n := (hlx n).trans_lt (hxr n)
  have hint1 : ∫ s in (l n)..(r n), α s = F (r n) - F (l n) :=
    (intervalIntegral.integral_interval_sub_left (hint x (r n)) (hint x (l n))).symm
  have hrlpos : (0:ℝ) < r n - l n := sub_pos.mpr hrl
  have key : intervalAvg α (l n) (r n) - α x =
      ((F (r n) - (r n - x) * α x) - (F (l n) - (l n - x) * α x)) / (r n - l n) := by
    unfold intervalAvg
    rw [hint1]
    field_simp
    ring
  rw [Real.dist_eq, key]
  have habs : |(F (r n) - (r n - x) * α x) - (F (l n) - (l n - x) * α x)| ≤
      (ε / 4) * |r n - x| + (ε / 4) * |l n - x| := by
    have e : (F (r n) - (r n - x) * α x) - (F (l n) - (l n - x) * α x) =
        (F (r n) - (r n - x) * α x) + (-(F (l n) - (l n - x) * α x)) := by ring
    rw [e]
    calc |(F (r n) - (r n - x) * α x) + (-(F (l n) - (l n - x) * α x))|
        ≤ |F (r n) - (r n - x) * α x| + |-(F (l n) - (l n - x) * α x)| := abs_add_le _ _
      _ = |F (r n) - (r n - x) * α x| + |F (l n) - (l n - x) * α x| := by rw [abs_neg]
      _ ≤ (ε / 4) * |r n - x| + (ε / 4) * |l n - x| := add_le_add hbr hbl
  have hrx : |r n - x| ≤ r n - l n := by rw [abs_of_pos (by linarith [hxr n])]; linarith [hlx n]
  have hlx' : |l n - x| ≤ r n - l n := by
    rw [abs_of_nonpos (by linarith [hlx n])]; linarith [hxr n]
  rw [abs_div, abs_of_pos hrlpos]
  rw [div_lt_iff₀ hrlpos]
  calc |(F (r n) - (r n - x) * α x) - (F (l n) - (l n - x) * α x)|
      ≤ (ε / 4) * |r n - x| + (ε / 4) * |l n - x| := habs
    _ ≤ (ε / 4) * (r n - l n) + (ε / 4) * (r n - l n) :=
        add_le_add (mul_le_mul_of_nonneg_left hrx (by linarith))
          (mul_le_mul_of_nonneg_left hlx' (by linarith))
    _ < ε * (r n - l n) := by nlinarith [hrlpos]

/-- The index of the level-`n` dyadic cell of `[a, b]` containing `x`. -/
private noncomputable def cellIdx (a b : ℝ) (n : ℕ) (x : ℝ) : ℕ :=
  ⌊(x - a) / ((b - a) * (2 ^ n : ℝ)⁻¹)⌋₊

private lemma mem_cellSet_cellIdx (a b : ℝ) (hab : a < b) (n : ℕ) (x : ℝ)
    (hx : a ≤ x) (hxb : x < b) :
    x ∈ cellSet a b n (cellIdx a b n x) ∧ cellIdx a b n x < 2 ^ n := by
  set u := (b - a) * (2 ^ n : ℝ)⁻¹ with hu_def
  have hu : (0 : ℝ) < u := by
    rw [hu_def]; have hba : (0 : ℝ) < b - a := sub_pos.mpr hab; positivity
  set q := (x - a) / u with hq_def
  have hq0 : (0 : ℝ) ≤ q := div_nonneg (sub_nonneg.mpr hx) hu.le
  have h2u : (2 : ℝ) ^ n * u = b - a := by
    rw [hu_def]; field_simp [pow_ne_zero n two_ne_zero]
  have hq_lt : q < (2 : ℝ) ^ n := by
    rw [hq_def, div_lt_iff₀ hu, h2u]; exact sub_lt_sub_right hxb a
  have hjlt : cellIdx a b n x < 2 ^ n := by
    rw [cellIdx, Nat.floor_lt hq0]
    exact_mod_cast hq_lt
  refine ⟨⟨?_, ?_⟩, hjlt⟩
  · have h1 : (⌊q⌋₊ : ℝ) ≤ q := Nat.floor_le hq0
    have h2 := mul_le_mul_of_nonneg_right h1 hu.le
    rw [hq_def, div_mul_cancel₀ _ hu.ne'] at h2
    unfold dPt cellIdx
    rw [← hu_def]
    linarith
  · have h1 : q < ⌊q⌋₊ + 1 := Nat.lt_floor_add_one q
    have h2 := mul_lt_mul_of_pos_right h1 hu
    rw [hq_def, div_mul_cancel₀ _ hu.ne'] at h2
    unfold dPt cellIdx
    rw [← hu_def]
    push_cast
    linarith

private lemma dyadicLen_tendsto_zero (a b : ℝ) :
    Filter.Tendsto (fun n : ℕ => (b - a) * (2 ^ n : ℝ)⁻¹) Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun n : ℕ => (2⁻¹ : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h2 := h1.const_mul (b - a)
  rw [mul_zero] at h2
  have e : (fun n : ℕ => (b - a) * (2 ^ n : ℝ)⁻¹) = fun n => (b - a) * (2⁻¹ : ℝ) ^ n := by
    funext n; rw [inv_pow]
  rwa [e]

private lemma dPt_cellIdx_tendsto_left (a b : ℝ) (hab : a < b) (x : ℝ) (hx : a ≤ x) (hxb : x < b) :
    Filter.Tendsto (fun n => dPt a b n (cellIdx a b n x)) Filter.atTop (nhds x) := by
  have hlen := dyadicLen_tendsto_zero a b
  rw [Metric.tendsto_atTop] at hlen ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hlen ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hmem := mem_cellSet_cellIdx a b hab n x hx hxb
  have h1 := hmem.1.1
  have hspec := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_pos (by
    have hba : (0 : ℝ) < b - a := sub_pos.mpr hab; positivity)] at hspec
  have hlen_eq : dPt a b n (cellIdx a b n x + 1) - dPt a b n (cellIdx a b n x) =
      (b - a) * (2 ^ n : ℝ)⁻¹ := dPt_sub_succ a b n (cellIdx a b n x)
  have h2 := hmem.1.2
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]
  linarith

private lemma dPt_cellIdx_tendsto_right (a b : ℝ) (hab : a < b) (x : ℝ) (hx : a ≤ x)
    (hxb : x < b) :
    Filter.Tendsto (fun n => dPt a b n (cellIdx a b n x + 1)) Filter.atTop (nhds x) := by
  have hlen := dyadicLen_tendsto_zero a b
  rw [Metric.tendsto_atTop] at hlen ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hlen ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hmem := mem_cellSet_cellIdx a b hab n x hx hxb
  have h1 := hmem.1.1
  have hspec := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_pos (by
    have hba : (0 : ℝ) < b - a := sub_pos.mpr hab; positivity)] at hspec
  have hlen_eq : dPt a b n (cellIdx a b n x + 1) - dPt a b n (cellIdx a b n x) =
      (b - a) * (2 ^ n : ℝ)⁻¹ := dPt_sub_succ a b n (cellIdx a b n x)
  have h2 := hmem.1.2
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]
  linarith

/-- For a.e. `x ∈ [a, b)`, the level-`n` dyadic cell average of `α` at `x`
converges to `α x` as `n → ∞`. -/
private lemma cellAvg_tendsto_ae (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) (a b : ℝ) (hab : a < b) :
    ∀ᵐ x ∂(volume.restrict (Set.Ico a b)),
      Filter.Tendsto (fun n => cellAvg α a b n (cellIdx a b n x)) Filter.atTop (nhds (α x)) := by
  have hloc : LocallyIntegrable α volume := locallyIntegrable_of_forall_intervalIntegrable α hα
  have hDT := LocallyIntegrable.ae_hasDerivAt_integral hloc
  have hintOn : ∀ u v : ℝ, IntervalIntegrable α volume u v := fun u v => by
    rcases lt_trichotomy u v with h | h | h
    · exact hα u v h
    · subst h; simp [IntervalIntegrable]
    · exact (hα v u h).symm
  filter_upwards [ae_restrict_of_ae hDT, ae_restrict_mem measurableSet_Ico] with x hx hxmem
  obtain ⟨hxa, hxb⟩ := hxmem
  exact cellAvg_tendsto_of_hasDerivAt α x hintOn (hx x)
    (fun n => (mem_cellSet_cellIdx a b hab n x hxa hxb).1.1)
    (fun n => (mem_cellSet_cellIdx a b hab n x hxa hxb).1.2)
    (dPt_cellIdx_tendsto_left a b hab x hxa hxb)
    (dPt_cellIdx_tendsto_right a b hab x hxa hxb)

/-- Chebyshev bound on a single Calderón–Zygmund cell. -/
private lemma cellSet_measure_le (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v)
    (a b ref τ : ℝ) (hab : a < b) (n j : ℕ) (hcz : IsCZCell α a b ref τ n j) :
    τ * (volume (cellSet a b n j)).toReal ≤ ∫ x in cellSet a b n j, |α x - ref| := by
  have hlt : dPt a b n j < dPt a b n (j + 1) := dPt_lt_succ hab n j
  have hInt : IntervalIntegrable α volume (dPt a b n j) (dPt a b n (j + 1)) := hα _ _ hlt
  have hlen : (volume (cellSet a b n j)).toReal = dPt a b n (j + 1) - dPt a b n j := by
    show (volume (Set.Ico (dPt a b n j) (dPt a b n (j + 1)))).toReal = _
    rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
  have hlen' : (0 : ℝ) < dPt a b n (j + 1) - dPt a b n j := sub_pos.mpr hlt
  have hcellavg : cellAvg α a b n j - ref =
      (∫ x in (dPt a b n j)..(dPt a b n (j + 1)), (α x - ref)) /
        (dPt a b n (j + 1) - dPt a b n j) := by
    unfold cellAvg intervalAvg
    rw [intervalIntegral.integral_sub hInt intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    field_simp
  have hcheby : τ < |cellAvg α a b n j - ref| := hcz.2.1
  rw [hcellavg, abs_div, abs_of_pos hlen', lt_div_iff₀ hlen'] at hcheby
  have hbound : |∫ x in (dPt a b n j)..(dPt a b n (j + 1)), (α x - ref)| ≤
      ∫ x in (dPt a b n j)..(dPt a b n (j + 1)), |α x - ref| :=
    intervalIntegral.abs_integral_le_integral_abs hlt.le
  have hconv : (∫ x in (dPt a b n j)..(dPt a b n (j + 1)), |α x - ref|) =
      ∫ x in cellSet a b n j, |α x - ref| := by
    rw [intervalIntegral.integral_of_le hlt.le]
    show (∫ x in Set.Ioc (dPt a b n j) (dPt a b n (j + 1)), |α x - ref|) =
      ∫ x in Set.Ico (dPt a b n j) (dPt a b n (j + 1)), |α x - ref|
    exact integral_Ico_eq_integral_Ioc.symm
  rw [hlen]
  calc τ * (dPt a b n (j + 1) - dPt a b n j)
      ≤ |∫ x in (dPt a b n j)..(dPt a b n (j + 1)), (α x - ref)| := hcheby.le
    _ ≤ ∫ x in (dPt a b n j)..(dPt a b n (j + 1)), |α x - ref| := hbound
    _ = ∫ x in cellSet a b n j, |α x - ref| := hconv

/-- The union of all Calderón–Zygmund cells for `α` on `[a, b)` relative to
`ref, τ`. -/
private def czUnion (α : ℝ → ℝ) (a b ref τ : ℝ) : Set ℝ :=
  ⋃ p : {p : ℕ × ℕ // IsCZCell α a b ref τ p.1 p.2}, cellSet a b p.1.1 p.1.2

private lemma czUnion_subset (α : ℝ → ℝ) (a b ref τ : ℝ) (hab : a < b) :
    czUnion α a b ref τ ⊆ Set.Ico a b := by
  intro x hx
  simp only [czUnion, Set.mem_iUnion] at hx
  obtain ⟨p, hxp⟩ := hx
  have hj := p.2.1
  exact ⟨by calc a = dPt a b p.1.1 0 := (dPt_zero a b p.1.1).symm
      _ ≤ dPt a b p.1.1 p.1.2 := dPt_mono hab.le p.1.1 (Nat.zero_le _)
      _ ≤ x := hxp.1,
    by calc x < dPt a b p.1.1 (p.1.2 + 1) := hxp.2
      _ ≤ dPt a b p.1.1 (2 ^ p.1.1) := dPt_mono hab.le p.1.1 hj
      _ = b := dPt_last a b p.1.1⟩

private lemma czUnion_pairwise_disjoint (α : ℝ → ℝ) (a b ref τ : ℝ) (hab : a < b) :
    Pairwise (fun i j : {p : ℕ × ℕ // IsCZCell α a b ref τ p.1 p.2} =>
      Disjoint (cellSet a b i.1.1 i.1.2) (cellSet a b j.1.1 j.1.2)) :=
  fun i j hij => czCell_disjoint α a b ref τ hab i.2 j.2 (fun h => hij (Subtype.ext h))

/-- **Maximal weak-type bound**: the union of all Calderón–Zygmund cells for
`α` on `[a, b)` relative to `ref, τ` has measure at most `(1/τ) ∫_{[a,b)}
|α - ref|`. -/
private lemma czUnion_measure_le (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v)
    (a b ref τ : ℝ) (hab : a < b) (hτ : 0 < τ) :
    τ * (volume (czUnion α a b ref τ)).toReal ≤ ∫ x in Set.Ico a b, |α x - ref| := by
  set S := czUnion α a b ref τ with hS_def
  set ι := {p : ℕ × ℕ // IsCZCell α a b ref τ p.1 p.2}
  have hsub := czUnion_subset α a b ref τ hab
  have hdisj := czUnion_pairwise_disjoint α a b ref τ hab
  have hInt_ab : IntegrableOn (fun x => |α x - ref|) (Set.Ico a b) volume := by
    have h1 : IntervalIntegrable α volume a b := hα a b hab
    have h2 : IntervalIntegrable (fun x => |α x - ref|) volume a b :=
      (h1.sub intervalIntegrable_const).abs
    exact (intervalIntegrable_iff_integrableOn_Ico_of_le hab.le).mp h2
  have hInt_S : IntegrableOn (fun x => |α x - ref|) S volume := hInt_ab.mono_set hsub
  have heq : ∫ x in S, |α x - ref| =
      ∑' p : ι, ∫ x in cellSet a b p.1.1 p.1.2, |α x - ref| :=
    MeasureTheory.integral_iUnion (fun _ => measurableSet_Ico) hdisj hInt_S
  have hSummable : Summable (fun p : ι => ∫ x in cellSet a b p.1.1 p.1.2, |α x - ref|) :=
    (MeasureTheory.hasSum_integral_iUnion (fun _ => measurableSet_Ico) hdisj hInt_S).summable
  have hterm : ∀ p : ι, τ * (volume (cellSet a b p.1.1 p.1.2)).toReal ≤
      ∫ x in cellSet a b p.1.1 p.1.2, |α x - ref| :=
    fun p => cellSet_measure_le α hα a b ref τ hab p.1.1 p.1.2 p.2
  have hSummable2 : Summable (fun p : ι => τ * (volume (cellSet a b p.1.1 p.1.2)).toReal) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg hτ.le ENNReal.toReal_nonneg) hterm hSummable
  have hle : ∑' p : ι, τ * (volume (cellSet a b p.1.1 p.1.2)).toReal ≤
      ∑' p : ι, ∫ x in cellSet a b p.1.1 p.1.2, |α x - ref| :=
    hSummable2.tsum_le_tsum hterm hSummable
  have hvol_eq : volume S = ∑' p : ι, volume (cellSet a b p.1.1 p.1.2) :=
    measure_iUnion hdisj (fun _ => measurableSet_Ico)
  have hcell_fin : ∀ p : ι, volume (cellSet a b p.1.1 p.1.2) ≠ ⊤ := fun p => by
    show volume (Set.Ico _ _) ≠ ⊤
    rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  have hvol_toReal : (volume S).toReal =
      ∑' p : ι, (volume (cellSet a b p.1.1 p.1.2)).toReal := by
    rw [hvol_eq, ENNReal.tsum_toReal_eq hcell_fin]
  calc τ * (volume S).toReal
      = τ * ∑' p : ι, (volume (cellSet a b p.1.1 p.1.2)).toReal := by rw [hvol_toReal]
    _ = ∑' p : ι, τ * (volume (cellSet a b p.1.1 p.1.2)).toReal := tsum_mul_left.symm
    _ ≤ ∑' p : ι, ∫ x in cellSet a b p.1.1 p.1.2, |α x - ref| := hle
    _ = ∫ x in S, |α x - ref| := heq.symm
    _ ≤ ∫ x in Set.Ico a b, |α x - ref| :=
        setIntegral_mono_set hInt_ab (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (Filter.Eventually.of_forall hsub)

private lemma intervalAvg_midpoint_split (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) (L R : ℝ) (hLR : L < R) :
    intervalAvg α L R =
      (intervalAvg α L ((L + R) / 2) + intervalAvg α ((L + R) / 2) R) / 2 := by
  set M := (L + R) / 2 with hM_def
  have hLM : L < M := by rw [hM_def]; linarith
  have hMR : M < R := by rw [hM_def]; linarith
  have hInt1 : IntervalIntegrable α volume L M := hα L M hLM
  have hInt2 : IntervalIntegrable α volume M R := hα M R hMR
  unfold intervalAvg
  rw [← intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2]
  have hLM_len : M - L = (R - L) / 2 := by rw [hM_def]; ring
  have hMR_len : R - M = (R - L) / 2 := by rw [hM_def]; ring
  rw [hLM_len, hMR_len]
  have hRL : R - L ≠ 0 := ne_of_gt (by linarith)
  field_simp

/-- The `m`-th level cell average splits as the average of its two children's
averages. -/
private lemma cellAvg_split (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) (a b : ℝ) (hab : a < b)
    (m j : ℕ) :
    cellAvg α a b m j =
      (cellAvg α a b (m + 1) (2 * j) + cellAvg α a b (m + 1) (2 * j + 1)) / 2 := by
  have hlt : dPt a b m j < dPt a b m (j + 1) := dPt_lt_succ hab m j
  have hsplit := intervalAvg_midpoint_split α hα (dPt a b m j) (dPt a b m (j + 1)) hlt
  rw [← center_eq_mid a b m j] at hsplit
  have h22 : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
  unfold cellAvg
  rw [h22, dPt_two_mul, dPt_two_mul_add_one, dPt_two_mul]
  exact hsplit

/-- If `[L, M] ⊆ [L, R]` with `M - L = θ (R - L)` for `0 < θ ≤ 1`, the average
of `α` over `[L, M]` deviates from the average over `[L, R]` by at most
`θ⁻¹` times the mean oscillation of `α` over `[L, R]`. -/
private lemma avg_left_dev_le (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v)
    (L M R : ℝ) (hLM : L < M) (hMR : M ≤ R) :
    |intervalAvg α L M - intervalAvg α L R| ≤
      (R - L) / (M - L) * intervalOscillation α L R := by
  rcases eq_or_lt_of_le hMR with hMR' | hMR'
  · have hML0 : M - L = R - L := by rw [hMR']
    rw [hMR', div_self (ne_of_gt (sub_pos.mpr (hMR' ▸ hLM))), one_mul, sub_self, abs_zero]
    have hLR : L < R := hMR' ▸ hLM
    unfold intervalOscillation intervalAvg
    apply div_nonneg _ (by linarith)
    exact intervalIntegral.integral_nonneg hLR.le (fun x _ => abs_nonneg _)
  have hLR : L < R := hLM.trans hMR'
  have hML : (0:ℝ) < M - L := sub_pos.mpr hLM
  have hRL : (0:ℝ) < R - L := sub_pos.mpr hLR
  set P := intervalAvg α L R with hP_def
  have hIntLR : IntervalIntegrable α volume L R := hα L R hLR
  have hIntLM : IntervalIntegrable α volume L M := hα L M hLM
  have hIntMR : IntervalIntegrable α volume M R := hα M R hMR'
  have hcompLM : IntervalIntegrable (fun x => |α x - P|) volume L M :=
    (hIntLM.sub intervalIntegrable_const).abs
  have hcompMR : IntervalIntegrable (fun x => |α x - P|) volume M R :=
    (hIntMR.sub intervalIntegrable_const).abs
  have hle : (∫ x in L..M, |α x - P|) ≤ ∫ x in L..R, |α x - P| := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hcompLM hcompMR]
    linarith [intervalIntegral.integral_nonneg (μ := volume) hMR'.le
      (fun x _ => abs_nonneg (α x - P))]
  have hAP : intervalAvg α L M - P = (∫ x in L..M, (α x - P)) / (M - L) := by
    unfold intervalAvg
    rw [intervalIntegral.integral_sub hIntLM intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    field_simp
  have hbound1 : |∫ x in L..M, (α x - P)| ≤ ∫ x in L..M, |α x - P| :=
    intervalIntegral.abs_integral_le_integral_abs hLM.le
  have hosc_eq : intervalOscillation α L R = (∫ x in L..R, |α x - P|) / (R - L) := by
    unfold intervalOscillation
    rw [← hP_def]
    unfold intervalAvg
    rfl
  rw [hAP, abs_div, abs_of_pos hML, hosc_eq]
  have hcancel : (R - L) / (M - L) * ((∫ x in L..R, |α x - P|) / (R - L)) =
      (∫ x in L..R, |α x - P|) / (M - L) := by
    field_simp
  rw [hcancel]
  gcongr
  exact hbound1.trans hle

/-- The mirror of `avg_left_dev_le`: the average over `[M, R] ⊆ [L, R]`
deviates from the average over `[L, R]` by at most `(R-L)/(R-M)` times the
mean oscillation of `α` over `[L, R]`. -/
private lemma avg_right_dev_le (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v)
    (L M R : ℝ) (hLM : L ≤ M) (hMR : M < R) :
    |intervalAvg α M R - intervalAvg α L R| ≤
      (R - L) / (R - M) * intervalOscillation α L R := by
  rcases eq_or_lt_of_le hLM with hLM' | hLM'
  · rw [← hLM', div_self (ne_of_gt (sub_pos.mpr (hLM' ▸ hMR))), one_mul, sub_self, abs_zero]
    have hLR : L < R := hLM' ▸ hMR
    unfold intervalOscillation intervalAvg
    apply div_nonneg _ (by linarith)
    exact intervalIntegral.integral_nonneg hLR.le (fun x _ => abs_nonneg _)
  have hLR : L < R := hLM'.trans hMR
  have hML : (0:ℝ) < M - L := sub_pos.mpr hLM'
  have hRM : (0:ℝ) < R - M := sub_pos.mpr hMR
  have hRL : (0:ℝ) < R - L := sub_pos.mpr hLR
  set P := intervalAvg α L R with hP_def
  have hIntLR : IntervalIntegrable α volume L R := hα L R hLR
  have hIntLM : IntervalIntegrable α volume L M := hα L M hLM'
  have hIntMR : IntervalIntegrable α volume M R := hα M R hMR
  have hcompLM : IntervalIntegrable (fun x => |α x - P|) volume L M :=
    (hIntLM.sub intervalIntegrable_const).abs
  have hcompMR : IntervalIntegrable (fun x => |α x - P|) volume M R :=
    (hIntMR.sub intervalIntegrable_const).abs
  have hle : (∫ x in M..R, |α x - P|) ≤ ∫ x in L..R, |α x - P| := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hcompLM hcompMR]
    linarith [intervalIntegral.integral_nonneg (μ := volume) hLM'.le
      (fun x _ => abs_nonneg (α x - P))]
  have hAP : intervalAvg α M R - P = (∫ x in M..R, (α x - P)) / (R - M) := by
    unfold intervalAvg
    rw [intervalIntegral.integral_sub hIntMR intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    field_simp
  have hbound1 : |∫ x in M..R, (α x - P)| ≤ ∫ x in M..R, |α x - P| :=
    intervalIntegral.abs_integral_le_integral_abs hMR.le
  have hosc_eq : intervalOscillation α L R = (∫ x in L..R, |α x - P|) / (R - L) := by
    unfold intervalOscillation
    rw [← hP_def]
    unfold intervalAvg
    rfl
  rw [hAP, abs_div, abs_of_pos hRM, hosc_eq]
  have hcancel : (R - L) / (R - M) * ((∫ x in L..R, |α x - P|) / (R - L)) =
      (∫ x in L..R, |α x - P|) / (R - M) := by
    field_simp
  rw [hcancel]
  gcongr
  exact hbound1.trans hle

/-- **One-level jump bound**: if the mean oscillation of `α` over the parent
cell is at most `η`, the two children's averages deviate from the parent's
average by at most `2η`. -/
private lemma cellAvg_child_dev_le (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) (a b : ℝ) (hab : a < b)
    (m j : ℕ) (η : ℝ)
    (hosc : intervalOscillation α (dPt a b m j) (dPt a b m (j + 1)) ≤ η) :
    |cellAvg α a b (m + 1) (2 * j) - cellAvg α a b m j| ≤ 2 * η ∧
      |cellAvg α a b (m + 1) (2 * j + 1) - cellAvg α a b m j| ≤ 2 * η := by
  set L := dPt a b m j with hL_def
  set R := dPt a b m (j + 1) with hR_def
  set M := dyadicCenter a b m j with hM_def
  have hLR : L < R := dPt_lt_succ hab m j
  have hLM : L < M := dPt_lt_center hab m j
  have hMR : M < R := center_lt_dPt_succ hab m j
  have hMmid : M = (L + R) / 2 := center_eq_mid a b m j
  have hA : cellAvg α a b (m + 1) (2 * j) = intervalAvg α L M := by
    show cellAvg α a b (m + 1) (2 * j) = _
    unfold cellAvg
    rw [dPt_two_mul, dPt_two_mul_add_one]
  have hB : cellAvg α a b (m + 1) (2 * j + 1) = intervalAvg α M R := by
    have h22 : 2 * j + 1 + 1 = 2 * (j + 1) := by ring
    unfold cellAvg
    rw [h22, dPt_two_mul_add_one, dPt_two_mul]
  have hPeq : cellAvg α a b m j = intervalAvg α L R := rfl
  have h2 : (R - L) / (M - L) = 2 := by
    have hRL2 : R - L = 2 * (M - L) := by rw [hMmid]; ring
    rw [hRL2, mul_div_assoc, div_self (ne_of_gt (sub_pos.mpr hLM)), mul_one]
  have h2' : (R - L) / (R - M) = 2 := by
    have hRL2 : R - L = 2 * (R - M) := by rw [hMmid]; ring
    rw [hRL2, mul_div_assoc, div_self (ne_of_gt (sub_pos.mpr hMR)), mul_one]
  rw [hA, hB, hPeq]
  constructor
  · calc |intervalAvg α L M - intervalAvg α L R| ≤
        (R - L) / (M - L) * intervalOscillation α L R := avg_left_dev_le α hα L M R hLM hMR.le
      _ = 2 * intervalOscillation α L R := by rw [h2]
      _ ≤ 2 * η := by linarith [hosc]
  · calc |intervalAvg α M R - intervalAvg α L R| ≤
        (R - L) / (R - M) * intervalOscillation α L R := avg_right_dev_le α hα L M R hLM.le hMR
      _ = 2 * intervalOscillation α L R := by rw [h2']
      _ ≤ 2 * η := by linarith [hosc]

/-- A Calderón–Zygmund cell of `α` on `[a, b)` relative to its *own* top-level
average `ref = cellAvg α a b 0 0` and threshold `2η` always has `n ≥ 1`. -/
private lemma czCell_level_pos (α : ℝ → ℝ) (a b η : ℝ) (hη : 0 < η) (n j : ℕ)
    (hcz : IsCZCell α a b (cellAvg α a b 0 0) (2 * η) n j) : 1 ≤ n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · exfalso
    subst hn
    have hj0 : j = 0 := by have := hcz.1; simpa using this
    subst hj0
    have hgt := hcz.2.1
    simp at hgt
    linarith
  · exact hn

/-- **Two-level jump bound for Calderón–Zygmund cells**: a cell's average
deviates from the reference by at most `4η`. -/
private lemma czCell_ref_dev_le (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) (a b η : ℝ) (hab : a < b)
    (hη : 0 < η) (n j : ℕ) (hcz : IsCZCell α a b (cellAvg α a b 0 0) (2 * η) n j)
    (hosc : ∀ m j' : ℕ, m < n → j' < 2 ^ m →
      intervalOscillation α (dPt a b m j') (dPt a b m (j' + 1)) ≤ η) :
    |cellAvg α a b n j - cellAvg α a b 0 0| ≤ 4 * η := by
  have hn1 : 1 ≤ n := czCell_level_pos α a b η hη n j hcz
  set m := n - 1 with hm_def
  set k := ancIdx n m j with hk_def
  have hnm : n = m + 1 := by omega
  have h1 : n - m = 1 := by omega
  have hk_eq : k = j / 2 := by rw [hk_def, ancIdx, h1, pow_one]
  have hjk : j = 2 * k ∨ j = 2 * k + 1 := by rw [hk_eq]; omega
  have hkm : k < 2 ^ m := by
    have := hcz.1
    rw [hnm] at this
    rw [hk_eq]
    omega
  have hparent : |cellAvg α a b m k - cellAvg α a b 0 0| ≤ 2 * η := by
    have := hcz.2.2 m (by omega)
    rwa [← hk_def] at this
  have hchild := cellAvg_child_dev_le α hα a b hab m k η
    (hosc m k (by omega) hkm)
  rcases hjk with hjk | hjk
  · rw [hjk, hnm]
    calc |cellAvg α a b (m + 1) (2 * k) - cellAvg α a b 0 0| ≤
        |cellAvg α a b (m + 1) (2 * k) - cellAvg α a b m k| + |cellAvg α a b m k - cellAvg α a b 0 0| :=
          abs_sub_le _ _ _
      _ ≤ 2 * η + 2 * η := add_le_add hchild.1 hparent
      _ = 4 * η := by ring
  · rw [hjk, hnm]
    calc |cellAvg α a b (m + 1) (2 * k + 1) - cellAvg α a b 0 0| ≤
        |cellAvg α a b (m + 1) (2 * k + 1) - cellAvg α a b m k| + |cellAvg α a b m k - cellAvg α a b 0 0| :=
          abs_sub_le _ _ _
      _ ≤ 2 * η + 2 * η := add_le_add hchild.2 hparent
      _ = 4 * η := by ring

/-- Consistency of `cellIdx` across levels: the level-`m` ancestor of `x`'s
level-`n` cell index is `x`'s own level-`m` cell index. -/
private lemma cellIdx_ancestor_eq (a b : ℝ) (hab : a < b) (m n : ℕ) (hmn : m ≤ n) (x : ℝ)
    (hxa : a ≤ x) (hxb : x < b) :
    ancIdx n m (cellIdx a b n x) = cellIdx a b m x := by
  have h1 : x ∈ cellSet a b n (cellIdx a b n x) := (mem_cellSet_cellIdx a b hab n x hxa hxb).1
  have h2 : x ∈ cellSet a b m (ancIdx n m (cellIdx a b n x)) :=
    cellSet_subset_ancestor a b hab.le n m (cellIdx a b n x) hmn h1
  have h3 : x ∈ cellSet a b m (cellIdx a b m x) := (mem_cellSet_cellIdx a b hab m x hxa hxb).1
  by_contra hne
  exact Set.disjoint_left.mp (cellSet_disjoint_same_level a b hab m _ _ hne) h2 h3

/-- **A.e. complement bound**: outside the Calderón–Zygmund union, `α`
deviates from `ref` by at most `τ`. -/
private lemma ae_bound_outside_czUnion (α : ℝ → ℝ)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) (a b ref τ : ℝ) (hab : a < b) :
    ∀ᵐ x ∂(volume.restrict (Set.Ico a b)), x ∉ czUnion α a b ref τ → |α x - ref| ≤ τ := by
  filter_upwards [cellAvg_tendsto_ae α hα a b hab, ae_restrict_mem measurableSet_Ico]
    with x hxtendsto hxmem hxnot
  obtain ⟨hxa, hxb⟩ := hxmem
  have hall : ∀ n, |cellAvg α a b n (cellIdx a b n x) - ref| ≤ τ := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_contra hcon
      push Not at hcon
      apply hxnot
      refine Set.mem_iUnion.mpr ⟨⟨(n, cellIdx a b n x), ?_⟩,
        (mem_cellSet_cellIdx a b hab n x hxa hxb).1⟩
      refine ⟨(mem_cellSet_cellIdx a b hab n x hxa hxb).2, hcon, ?_⟩
      intro m hm
      dsimp only at hm ⊢
      rw [cellIdx_ancestor_eq a b hab m n hm.le x hxa hxb]
      exact ih m hm
  have hcont : Filter.Tendsto (fun n => |cellAvg α a b n (cellIdx a b n x) - ref|)
      Filter.atTop (nhds |α x - ref|) := (hxtendsto.sub tendsto_const_nhds).abs
  exact le_of_tendsto' hcont hall

private lemma dPt_mem_Icc (p q : ℝ) (hpq : p ≤ q) (m j : ℕ) (hj : j ≤ 2 ^ m) :
    p ≤ dPt p q m j ∧ dPt p q m j ≤ q := by
  refine ⟨?_, ?_⟩
  · have := dPt_mono hpq m (Nat.zero_le j); rwa [dPt_zero] at this
  · have := dPt_mono hpq m hj; rwa [dPt_last] at this

/-- The set of ratios `|{x ∈ [p,q) : τ < |α(x) - avg_{[p,q]}(α)|}| / (q-p)`
over subintervals `[p, q] ⊆ [A, B]`. -/
private noncomputable def maxRatioSet (α : ℝ → ℝ) (A B τ : ℝ) : Set ℝ :=
  { r : ℝ | ∃ p q : ℝ, A ≤ p ∧ p < q ∧ q ≤ B ∧
      r = (volume {x ∈ Set.Ico p q | τ < |α x - cellAvg α p q 0 0|}).toReal / (q - p) }

private lemma maxRatioSet_bddAbove (α : ℝ → ℝ) (A B τ : ℝ) : BddAbove (maxRatioSet α A B τ) := by
  refine ⟨1, ?_⟩
  rintro r ⟨p, q, hAp, hpq, hqB, rfl⟩
  rw [div_le_one (by linarith)]
  calc (volume {x ∈ Set.Ico p q | τ < |α x - cellAvg α p q 0 0|}).toReal
      ≤ (volume (Set.Ico p q)).toReal :=
        ENNReal.toReal_mono (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
          (measure_mono fun x hx => hx.1)
    _ = q - p := by rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]

/-- The supremum of `maxRatioSet`. -/
private noncomputable def maxRatio (α : ℝ → ℝ) (A B τ : ℝ) : ℝ := sSup (maxRatioSet α A B τ)

private lemma maxRatio_nonneg (α : ℝ → ℝ) (A B τ : ℝ) (hAB : A < B) : 0 ≤ maxRatio α A B τ := by
  have hmem : (0:ℝ) ≤ (volume {x ∈ Set.Ico A B | τ < |α x - cellAvg α A B 0 0|}).toReal / (B - A) :=
    div_nonneg ENNReal.toReal_nonneg (by linarith)
  refine hmem.trans (le_csSup (maxRatioSet_bddAbove α A B τ) ⟨A, B, le_refl A, hAB, le_refl B, rfl⟩)

/-- **Self-improving inequality**: raising the threshold by `4η` halves the
maximal ratio, given a uniform mean-oscillation bound `η` on `[A, B]`. -/
private lemma maxRatio_selfimprove (α : ℝ → ℝ) (hmeas : Measurable α)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) (A B η : ℝ) (hAB : A < B)
    (hη : 0 < η)
    (hbmo : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B → intervalOscillation α p q ≤ η) (τ : ℝ)
    (hτ : 0 ≤ τ) :
    maxRatio α A B (τ + 4 * η) ≤ (1 / 2) * maxRatio α A B τ := by
  show sSup (maxRatioSet α A B (τ + 4 * η)) ≤ (1 / 2) * maxRatio α A B τ
  refine csSup_le ⟨(volume {x ∈ Set.Ico A B | (τ + 4 * η) < |α x - cellAvg α A B 0 0|}).toReal /
    (B - A), A, B, le_refl A, hAB, le_refl B, rfl⟩ ?_
  rintro r ⟨p, q, hAp, hpq, hqB, rfl⟩
  set ref := cellAvg α p q 0 0 with href_def
  set ι := {pr : ℕ × ℕ // IsCZCell α p q ref (2 * η) pr.1 pr.2}
  have hoscpq : intervalOscillation α p q ≤ η := hbmo p q hAp hpq hqB
  have hae2 : ∀ᵐ x ∂volume, x ∈ Set.Ico p q →
      (x ∉ czUnion α p q ref (2 * η) → |α x - ref| ≤ 2 * η) :=
    (ae_restrict_iff' measurableSet_Ico).mp (ae_bound_outside_czUnion α hα p q ref (2 * η) hpq)
  have hcontainae : ∀ᵐ x ∂volume,
      x ∈ {x ∈ Set.Ico p q | (τ + 4 * η) < |α x - ref|} →
      x ∈ ⋃ Qp : ι, {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
        τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|} := by
    filter_upwards [hae2] with x hx hxmem
    obtain ⟨hxIco, hxgt⟩ := hxmem
    by_contra hxnotin2
    have hxnotcz : x ∉ czUnion α p q ref (2 * η) := by
      intro hxcz
      simp only [czUnion, Set.mem_iUnion] at hxcz
      obtain ⟨Qp, hxQp⟩ := hxcz
      apply hxnotin2
      refine Set.mem_iUnion.mpr ⟨Qp, hxQp, ?_⟩
      have hdev := czCell_ref_dev_le α hα p q η hpq hη Qp.1.1 Qp.1.2
        (href_def ▸ Qp.2)
        (fun m j' hm hj' => by
          have hle1 := dPt_mem_Icc p q hpq.le m j' hj'.le
          have hle2 := dPt_mem_Icc p q hpq.le m (j' + 1) hj'
          exact hbmo (dPt p q m j') (dPt p q m (j' + 1))
            (hAp.trans hle1.1) (dPt_lt_succ hpq m j') (hle2.2.trans hqB))
      have heq : α x - ref = (α x - cellAvg α p q Qp.1.1 Qp.1.2) +
          (cellAvg α p q Qp.1.1 Qp.1.2 - ref) := by ring
      have htri : |α x - ref| ≤ |α x - cellAvg α p q Qp.1.1 Qp.1.2| +
          |cellAvg α p q Qp.1.1 Qp.1.2 - ref| := by rw [heq]; exact abs_add_le _ _
      have hdev' : |cellAvg α p q Qp.1.1 Qp.1.2 - ref| ≤ 4 * η := hdev
      by_contra hcon
      push Not at hcon
      linarith
    linarith [hx hxIco hxnotcz]
  have hmeasle : volume {x ∈ Set.Ico p q | (τ + 4 * η) < |α x - ref|} ≤
      volume (⋃ Qp : ι, {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
        τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}) :=
    measure_mono_ae hcontainae
  have hsum : volume (⋃ Qp : ι, {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
      τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}) ≤
      ∑' Qp : ι, volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
        τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|} :=
    measure_iUnion_le _
  have hpercell : ∀ Qp : ι, (volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
      τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}).toReal ≤
      maxRatio α A B τ * (volume (cellSet p q Qp.1.1 Qp.1.2)).toReal := by
    rintro ⟨⟨n, j⟩, hjn, -, -⟩
    set pc := dPt p q n j with hpc_def
    set qc := dPt p q n (j + 1) with hqc_def
    have hpqc : pc < qc := dPt_lt_succ hpq n j
    have hApc : A ≤ pc := hAp.trans (dPt_mem_Icc p q hpq.le n j hjn.le).1
    have hqcB : qc ≤ B := (dPt_mem_Icc p q hpq.le n (j + 1) hjn).2.trans hqB
    have hcellavg_eq : cellAvg α p q n j = cellAvg α pc qc 0 0 := by
      show intervalAvg α pc qc = intervalAvg α (dPt pc qc 0 0) (dPt pc qc 0 1)
      rw [dPt_zero, show (1 : ℕ) = 2 ^ 0 by norm_num, dPt_last]
    have hset_eq : {x ∈ cellSet p q n j | τ < |α x - cellAvg α p q n j|} =
        {x ∈ Set.Ico pc qc | τ < |α x - cellAvg α pc qc 0 0|} := by
      show {x ∈ Set.Ico pc qc | τ < |α x - cellAvg α p q n j|} = _
      rw [hcellavg_eq]
    have hmem : (volume {x ∈ Set.Ico pc qc | τ < |α x - cellAvg α pc qc 0 0|}).toReal /
        (qc - pc) ∈ maxRatioSet α A B τ := ⟨pc, qc, hApc, hpqc, hqcB, rfl⟩
    have hle := le_csSup (maxRatioSet_bddAbove α A B τ) hmem
    have hlen : (volume (cellSet p q n j)).toReal = qc - pc := by
      show (volume (Set.Ico pc qc)).toReal = _
      rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]
    have hlen' : (0 : ℝ) < qc - pc := sub_pos.mpr hpqc
    rw [div_le_iff₀ hlen'] at hle
    rw [hset_eq, hlen]
    exact hle
  have hcell_fin : ∀ Qp : ι, volume (cellSet p q Qp.1.1 Qp.1.2) ≠ ⊤ := fun Qp => by
    show volume (Set.Ico _ _) ≠ ⊤
    rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top
  have hbad_fin : ∀ Qp : ι, volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
      τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|} ≠ ⊤ :=
    fun Qp => ne_top_of_le_ne_top (hcell_fin Qp) (measure_mono fun x hx => hx.1)
  have hsum_toReal : (∑' Qp : ι, volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
      τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}).toReal =
      ∑' Qp : ι, (volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
        τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}).toReal :=
    ENNReal.tsum_toReal_eq hbad_fin
  have hmaxnn : 0 ≤ maxRatio α A B τ := maxRatio_nonneg α A B τ hAB
  have hSummable_cell : Summable (fun Qp : ι => (volume (cellSet p q Qp.1.1 Qp.1.2)).toReal) := by
    have hvol_eq : volume (czUnion α p q ref (2 * η)) =
        ∑' Qp : ι, volume (cellSet p q Qp.1.1 Qp.1.2) :=
      measure_iUnion (czUnion_pairwise_disjoint α p q ref (2 * η) hpq)
        (fun _ => measurableSet_Ico)
    have hfin : volume (czUnion α p q ref (2 * η)) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Ico (a := p) (b := q)]; exact ENNReal.ofReal_ne_top)
        (measure_mono (czUnion_subset α p q ref (2 * η) hpq))
    rw [hvol_eq] at hfin
    exact ENNReal.summable_toReal hfin
  have hSummable_bad : Summable (fun Qp : ι => (volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
      τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}).toReal) :=
    Summable.of_nonneg_of_le (fun Qp => ENNReal.toReal_nonneg)
      (fun Qp => (hpercell Qp)) (hSummable_cell.mul_left (maxRatio α A B τ))
  have hle_sum : ∑' Qp : ι, (volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
      τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}).toReal ≤
      ∑' Qp : ι, maxRatio α A B τ * (volume (cellSet p q Qp.1.1 Qp.1.2)).toReal :=
    hSummable_bad.tsum_le_tsum hpercell (hSummable_cell.mul_left _)
  have hczvol_eq : (volume (czUnion α p q ref (2 * η))).toReal =
      ∑' Qp : ι, (volume (cellSet p q Qp.1.1 Qp.1.2)).toReal := by
    have hvol_eq : volume (czUnion α p q ref (2 * η)) =
        ∑' Qp : ι, volume (cellSet p q Qp.1.1 Qp.1.2) :=
      measure_iUnion (czUnion_pairwise_disjoint α p q ref (2 * η) hpq)
        (fun _ => measurableSet_Ico)
    rw [hvol_eq, ENNReal.tsum_toReal_eq hcell_fin]
  have hczmeasure : 2 * η * (volume (czUnion α p q ref (2 * η))).toReal ≤
      ∫ x in Set.Ico p q, |α x - ref| :=
    czUnion_measure_le α hα p q ref (2 * η) hpq (by linarith)
  have hcellavg00 : cellAvg α p q 0 0 = intervalAvg α p q := by
    show intervalAvg α (dPt p q 0 0) (dPt p q 0 1) = intervalAvg α p q
    rw [dPt_zero, show (1 : ℕ) = 2 ^ 0 by norm_num, dPt_last]
  have href_eq : ref = intervalAvg α p q := by rw [href_def, hcellavg00]
  have hoscint : (∫ x in Set.Ico p q, |α x - ref|) = (q - p) * intervalOscillation α p q := by
    have hthis : (∫ x in p..q, |α x - ref|) = ∫ x in Set.Ioc p q, |α x - ref| :=
      intervalIntegral.integral_of_le (μ := volume) hpq.le
    rw [integral_Ico_eq_integral_Ioc, ← hthis]
    unfold intervalOscillation
    rw [href_eq]
    unfold intervalAvg
    have hqp0 : (q - p) ≠ 0 := ne_of_gt (by linarith)
    field_simp
    apply intervalIntegral.integral_congr
    intro x _
    simp only [mul_comm (α x) (q - p)]
  have hczbound : (volume (czUnion α p q ref (2 * η))).toReal ≤ (q - p) / 2 := by
    rw [hoscint] at hczmeasure
    have : 2 * η * (volume (czUnion α p q ref (2 * η))).toReal ≤ (q - p) * η := by
      calc 2 * η * (volume (czUnion α p q ref (2 * η))).toReal ≤ (q - p) * intervalOscillation α p q :=
            hczmeasure
        _ ≤ (q - p) * η := by
            apply mul_le_mul_of_nonneg_left hoscpq (by linarith)
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [this]
  have hfinal : (volume {x ∈ Set.Ico p q | (τ + 4 * η) < |α x - ref|}).toReal ≤
      maxRatio α A B τ * ((q - p) / 2) := by
    have hbadmeas : ∀ Qp : ι, MeasurableSet {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
        τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|} :=
      fun Qp => measurableSet_Ico.inter
        (measurableSet_lt measurable_const (hmeas.sub measurable_const).abs)
    have hdisj_bad : Pairwise (fun i j : ι => Disjoint
        {x ∈ cellSet p q i.1.1 i.1.2 | τ < |α x - cellAvg α p q i.1.1 i.1.2|}
        {x ∈ cellSet p q j.1.1 j.1.2 | τ < |α x - cellAvg α p q j.1.1 j.1.2|}) :=
      fun i j hij => Disjoint.mono (Set.sep_subset _ _) (Set.sep_subset _ _)
        (czUnion_pairwise_disjoint α p q ref (2 * η) hpq hij)
    have hsum_lt_top : (∑' Qp : ι, volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
        τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}) < ⊤ := by
      rw [← measure_iUnion hdisj_bad hbadmeas]
      have hcell_sub : ∀ Qp : ι, cellSet p q Qp.1.1 Qp.1.2 ⊆ Set.Ico p q := by
        intro Qp x hx
        have hjn : Qp.1.2 < 2 ^ Qp.1.1 := Qp.2.1
        have h1 := dPt_mem_Icc p q hpq.le Qp.1.1 Qp.1.2 hjn.le
        have h2 := dPt_mem_Icc p q hpq.le Qp.1.1 (Qp.1.2 + 1) hjn
        exact ⟨h1.1.trans hx.1, hx.2.trans_le h2.2⟩
      calc volume (⋃ Qp : ι, {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
            τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}) ≤ volume (Set.Ico p q) :=
              measure_mono (Set.iUnion_subset fun Qp x hx => hcell_sub Qp hx.1)
        _ < ⊤ := by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top
    have hstep : (volume {x ∈ Set.Ico p q | (τ + 4 * η) < |α x - ref|}).toReal ≤
        (∑' Qp : ι, volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
          τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}).toReal :=
      ENNReal.toReal_mono hsum_lt_top.ne (hmeasle.trans hsum)
    rw [hsum_toReal] at hstep
    calc (volume {x ∈ Set.Ico p q | (τ + 4 * η) < |α x - ref|}).toReal ≤
          ∑' Qp : ι, (volume {x ∈ cellSet p q Qp.1.1 Qp.1.2 |
            τ < |α x - cellAvg α p q Qp.1.1 Qp.1.2|}).toReal := hstep
      _ ≤ ∑' Qp : ι, maxRatio α A B τ * (volume (cellSet p q Qp.1.1 Qp.1.2)).toReal := hle_sum
      _ = maxRatio α A B τ * ∑' Qp : ι, (volume (cellSet p q Qp.1.1 Qp.1.2)).toReal :=
          tsum_mul_left
      _ = maxRatio α A B τ * (volume (czUnion α p q ref (2 * η))).toReal := by rw [hczvol_eq]
      _ ≤ maxRatio α A B τ * ((q - p) / 2) := mul_le_mul_of_nonneg_left hczbound hmaxnn
  rw [div_le_iff₀ (by linarith)]
  calc (volume {x ∈ Set.Ico p q | (τ + 4 * η) < |α x - ref|}).toReal ≤
      maxRatio α A B τ * ((q - p) / 2) := hfinal
    _ = 1 / 2 * maxRatio α A B τ * (q - p) := by ring

private lemma maxRatio_le_one (α : ℝ → ℝ) (A B τ : ℝ) (hAB : A < B) :
    maxRatio α A B τ ≤ 1 := by
  show sSup (maxRatioSet α A B τ) ≤ 1
  refine csSup_le ⟨(volume {x ∈ Set.Ico A B | τ < |α x - cellAvg α A B 0 0|}).toReal / (B - A),
    A, B, le_refl A, hAB, le_refl B, rfl⟩ ?_
  rintro r ⟨p, q, hAp, hpq, hqB, rfl⟩
  rw [div_le_one (by linarith)]
  calc (volume {x ∈ Set.Ico p q | τ < |α x - cellAvg α p q 0 0|}).toReal
      ≤ (volume (Set.Ico p q)).toReal :=
        ENNReal.toReal_mono (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
          (measure_mono fun x hx => hx.1)
    _ = q - p := by rw [Real.volume_Ico, ENNReal.toReal_ofReal (by linarith)]

/-- **Geometric decay of the maximal ratio**: iterating the self-improving
inequality `k` times. -/
private lemma maxRatio_geometric (α : ℝ → ℝ) (hmeas : Measurable α)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) (A B η : ℝ) (hAB : A < B)
    (hη : 0 < η)
    (hbmo : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B → intervalOscillation α p q ≤ η) :
    ∀ k : ℕ, maxRatio α A B (4 * η * k) ≤ (2 : ℝ)⁻¹ ^ k := by
  intro k
  induction k with
  | zero => simpa using maxRatio_le_one α A B 0 hAB
  | succ k ih =>
    have hstep := maxRatio_selfimprove α hmeas hα A B η hAB hη hbmo (4 * η * k)
      (by positivity)
    have heq : 4 * η * (k : ℝ) + 4 * η = 4 * η * ((k : ℝ) + 1) := by ring
    rw [heq] at hstep
    have hcast : ((k : ℕ) + 1 : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at hstep
    calc maxRatio α A B (4 * η * ((k + 1 : ℕ) : ℝ)) ≤
        (1 / 2) * maxRatio α A B (4 * η * (k : ℝ)) := hstep
      _ ≤ (1 / 2) * (2 : ℝ)⁻¹ ^ k := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 : ℝ)⁻¹ ^ (k + 1) := by ring

/-- The elementary Taylor-type bound `e^s - 1 - s ≤ s² e^{|s|}`, valid for all
real `s`. -/
private lemma exp_sub_one_sub_id_le (s : ℝ) :
    Real.exp s - 1 - s ≤ s ^ 2 * Real.exp |s| := by
  have hexp_ge_one : (1 : ℝ) ≤ Real.exp |s| := Real.one_le_exp (abs_nonneg s)
  rcases le_or_gt |s| 1 with hs | hs
  · have hb := Real.abs_exp_sub_one_sub_id_le hs
    have h1 : Real.exp s - 1 - s ≤ s ^ 2 := (le_abs_self _).trans hb
    nlinarith [sq_nonneg s]
  · rcases le_or_gt 0 s with hs0 | hs0
    · have habs : |s| = s := abs_of_nonneg hs0
      have hs1 : 1 < s := by rw [habs] at hs; exact hs
      have hsq : (1 : ℝ) ≤ s ^ 2 := by nlinarith
      have hpos : 0 < Real.exp s := Real.exp_pos s
      calc Real.exp s - 1 - s ≤ Real.exp s := by linarith
        _ = 1 * Real.exp s := (one_mul _).symm
        _ ≤ s ^ 2 * Real.exp s := mul_le_mul_of_nonneg_right hsq hpos.le
        _ = s ^ 2 * Real.exp |s| := by rw [habs]
    · have habs : |s| = -s := abs_of_neg hs0
      have hs1 : 1 < -s := by rw [habs] at hs; exact hs
      have hexp_lt : Real.exp s < 1 := Real.exp_lt_one_iff.mpr hs0
      have hsq : -s ≤ s ^ 2 := by nlinarith
      calc Real.exp s - 1 - s ≤ -s := by linarith
        _ ≤ s ^ 2 := hsq
        _ = s ^ 2 * 1 := (mul_one _).symm
        _ ≤ s ^ 2 * Real.exp |s| := mul_le_mul_of_nonneg_left hexp_ge_one (sq_nonneg s)

/-- The convergent series `∑ (k+1)² (√2/2)^k` entering the John–Nirenberg
moment constant. -/
private noncomputable def jnSum : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) ^ 2 * (Real.sqrt 2 / 2) ^ k

private lemma sqrt2_half_lt_one : ‖(Real.sqrt 2 / 2 : ℝ)‖ < 1 := by
  have h2 : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2,
      Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) < 4)]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  linarith

private lemma jnSum_summable :
    Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 2 * (Real.sqrt 2 / 2) ^ k) := by
  have h2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 sqrt2_half_lt_one
  have h1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 sqrt2_half_lt_one
  have h0 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 sqrt2_half_lt_one
  have := ((h2.add (h1.mul_left 2)).add h0)
  refine this.congr fun k => ?_
  ring

private lemma jnSum_nonneg : 0 ≤ jnSum :=
  tsum_nonneg fun k => by positivity

/-- **John–Nirenberg moment bound**: with geometric decay of the tail measures,
`∫ s² e^{|s|} ≤ 16 √2 · jnSum · η² · (q - p)` on `[p, q)`. -/
private lemma exp_moment_bound (α : ℝ → ℝ) (hmeas : Measurable α)
    (hα : ∀ u v : ℝ, u < v → IntervalIntegrable α volume u v) (A B η : ℝ) (hAB : A < B)
    (hη : 0 < η) (hηsmall : η ≤ Real.log 2 / 8)
    (hbmo : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B → intervalOscillation α p q ≤ η)
    (p q : ℝ) (hAp : A ≤ p) (hpq : p < q) (hqB : q ≤ B) :
    ∫⁻ x in Set.Ico p q, ENNReal.ofReal
        ((α x - cellAvg α p q 0 0) ^ 2 * Real.exp |α x - cellAvg α p q 0 0|) ≤
      ENNReal.ofReal (16 * Real.sqrt 2 * jnSum * η ^ 2 * (q - p)) := by
  set c := cellAvg α p q 0 0 with hc_def
  set S : ℕ → Set ℝ := fun k => {x ∈ Set.Ico p q | 4 * η * (k : ℝ) < |α x - c|} with hS_def
  have hSmeas : ∀ k, MeasurableSet (S k) := fun k =>
    measurableSet_Ico.inter (measurableSet_lt measurable_const (hmeas.sub measurable_const).abs)
  -- tail bound from the geometric decay of the maximal ratio
  have htail : ∀ k : ℕ, (volume (S k)).toReal ≤ (2 : ℝ)⁻¹ ^ k * (q - p) := by
    intro k
    have hmem : (volume {x ∈ Set.Ico p q | (4 * η * (k : ℝ)) < |α x - cellAvg α p q 0 0|}).toReal /
        (q - p) ∈ maxRatioSet α A B (4 * η * (k : ℝ)) := ⟨p, q, hAp, hpq, hqB, rfl⟩
    have hle := le_csSup (maxRatioSet_bddAbove α A B (4 * η * (k : ℝ))) hmem
    have hgeo := maxRatio_geometric α hmeas hα A B η hAB hη hbmo k
    have hqp : (0 : ℝ) < q - p := by linarith
    rw [div_le_iff₀ hqp] at hle
    calc (volume (S k)).toReal ≤ maxRatio α A B (4 * η * (k : ℝ)) * (q - p) := hle
      _ ≤ (2 : ℝ)⁻¹ ^ k * (q - p) := mul_le_mul_of_nonneg_right hgeo hqp.le
  -- the staircase majorant
  set Φ : ℕ → ℝ := fun k => (4 * η * ((k : ℝ) + 1)) ^ 2 * Real.exp (4 * η * ((k : ℝ) + 1))
    with hΦ_def
  have hΦnn : ∀ k, 0 ≤ Φ k := fun k => by rw [hΦ_def]; positivity
  set g : ℕ → ℝ → ENNReal := fun k x => (S k).indicator (fun _ => ENNReal.ofReal (Φ k)) x
    with hg_def
  have hgmeas : ∀ k, Measurable (g k) := fun k =>
    (measurable_const.indicator (hSmeas k))
  -- pointwise domination
  have hpoint : ∀ x ∈ Set.Ico p q,
      ENNReal.ofReal ((α x - c) ^ 2 * Real.exp |α x - c|) ≤ ∑' k : ℕ, g k x := by
    intro x hx
    rcases eq_or_lt_of_le (abs_nonneg (α x - c)) with h0 | h0
    · have hzero : (α x - c) ^ 2 = 0 := by
        have : α x - c = 0 := abs_eq_zero.mp h0.symm
        rw [this]; ring
      rw [hzero, zero_mul, ENNReal.ofReal_zero]
      exact zero_le
    · set t := |α x - c| with ht_def
      set u := t / (4 * η) with hu_def
      have hupos : 0 < u := by rw [hu_def]; positivity
      set m := ⌈u⌉₊ with hm_def
      have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by
        intro hm0
        rw [hm_def] at hm0
        exact absurd (Nat.ceil_eq_zero.mp hm0) (not_le.mpr hupos))
      set k₀ := m - 1 with hk0_def
      have hk0cast : ((k₀ : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [hk0_def]
        push_cast [Nat.cast_sub hm1]
        ring
      have hlt : 4 * η * (k₀ : ℝ) < t := by
        have hceil : (m : ℝ) < u + 1 := by
          rw [hm_def]; exact Nat.ceil_lt_add_one hupos.le
        have : (k₀ : ℝ) < u := by rw [hk0cast]; linarith
        rw [hu_def] at this
        have h4η : (0 : ℝ) < 4 * η := by linarith
        calc 4 * η * (k₀ : ℝ) < 4 * η * (t / (4 * η)) :=
              mul_lt_mul_of_pos_left this h4η
          _ = t := by field_simp
      have hge : t ≤ 4 * η * ((k₀ : ℝ) + 1) := by
        have hceil : u ≤ (m : ℝ) := Nat.le_ceil u
        have h4η : (0 : ℝ) < 4 * η := by linarith
        rw [hk0cast]
        rw [hu_def] at hceil
        calc t = 4 * η * (t / (4 * η)) := by field_simp
          _ ≤ 4 * η * (m : ℝ) := mul_le_mul_of_nonneg_left hceil h4η.le
          _ = 4 * η * ((m : ℝ) - 1 + 1) := by ring
      have hxS : x ∈ S k₀ := ⟨hx, hlt⟩
      have hterm : ENNReal.ofReal ((α x - c) ^ 2 * Real.exp |α x - c|) ≤ g k₀ x := by
        rw [hg_def]
        simp only [Set.indicator_of_mem hxS]
        apply ENNReal.ofReal_le_ofReal
        have hsq : (α x - c) ^ 2 = t ^ 2 := by rw [ht_def, sq_abs]
        rw [hsq, ← ht_def]
        have h1 : t ^ 2 ≤ (4 * η * ((k₀ : ℝ) + 1)) ^ 2 := by
          have ht0 : (0:ℝ) ≤ t := abs_nonneg _
          nlinarith [hge, ht0]
        have h2 : Real.exp t ≤ Real.exp (4 * η * ((k₀ : ℝ) + 1)) := Real.exp_le_exp.mpr hge
        exact mul_le_mul h1 h2 (Real.exp_pos t).le (by positivity)
      exact hterm.trans (ENNReal.le_tsum (f := fun k => g k x) k₀)
  -- integrate
  have hstep1 : ∫⁻ x in Set.Ico p q,
      ENNReal.ofReal ((α x - c) ^ 2 * Real.exp |α x - c|) ≤
      ∫⁻ x in Set.Ico p q, ∑' k : ℕ, g k x := by
    apply lintegral_mono_ae
    rw [ae_restrict_iff' measurableSet_Ico]
    exact Filter.Eventually.of_forall hpoint
  have hstep2 : (∫⁻ x in Set.Ico p q, ∑' k : ℕ, g k x) =
      ∑' k : ℕ, ∫⁻ x in Set.Ico p q, g k x :=
    lintegral_tsum (fun k => (hgmeas k).aemeasurable)
  have hstep3 : ∀ k : ℕ, (∫⁻ x in Set.Ico p q, g k x) =
      ENNReal.ofReal (Φ k) * volume (S k) := by
    intro k
    rw [hg_def]
    rw [lintegral_indicator_const (hSmeas k)]
    congr 1
    rw [Measure.restrict_apply (hSmeas k)]
    congr 1
    exact Set.inter_eq_left.mpr fun y hy => hy.1
  -- termwise bound and summation
  have hterm_bd : ∀ k : ℕ, ENNReal.ofReal (Φ k) * volume (S k) ≤
      ENNReal.ofReal (Φ k * ((2 : ℝ)⁻¹ ^ k * (q - p))) := by
    intro k
    have hSfin : volume (S k) ≠ ⊤ :=
      ne_top_of_le_ne_top (by rw [Real.volume_Ico (a := p) (b := q)]; exact ENNReal.ofReal_ne_top)
        (measure_mono fun y hy => hy.1)
    have hvol : volume (S k) ≤ ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k * (q - p)) := by
      rw [← ENNReal.ofReal_toReal hSfin]
      exact ENNReal.ofReal_le_ofReal (htail k)
    calc ENNReal.ofReal (Φ k) * volume (S k)
        ≤ ENNReal.ofReal (Φ k) * ENNReal.ofReal ((2 : ℝ)⁻¹ ^ k * (q - p)) :=
          mul_le_mul' (le_refl _) hvol
      _ = ENNReal.ofReal (Φ k * ((2 : ℝ)⁻¹ ^ k * (q - p))) :=
          (ENNReal.ofReal_mul (hΦnn k)).symm
  -- the real series bound
  have hexp4η : Real.exp (4 * η) ≤ Real.sqrt 2 := by
    have h1 : 4 * η ≤ Real.log 2 / 2 := by linarith
    calc Real.exp (4 * η) ≤ Real.exp (Real.log 2 / 2) := Real.exp_le_exp.mpr h1
      _ = Real.sqrt 2 := by
          rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
          congr 1
          ring
  have hseries_term : ∀ k : ℕ, Φ k * ((2 : ℝ)⁻¹ ^ k * (q - p)) ≤
      (16 * Real.sqrt 2 * η ^ 2 * (q - p)) * (((k : ℝ) + 1) ^ 2 * (Real.sqrt 2 / 2) ^ k) := by
    intro k
    have hqp : (0 : ℝ) ≤ q - p := by linarith
    have hΦeq : Φ k = 16 * η ^ 2 * ((k : ℝ) + 1) ^ 2 * Real.exp (4 * η * ((k : ℝ) + 1)) := by
      rw [hΦ_def]; ring
    have hexpsplit : Real.exp (4 * η * ((k : ℝ) + 1)) =
        Real.exp (4 * η) * Real.exp (4 * η) ^ k := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    have hratio : Real.exp (4 * η) ^ k * (2 : ℝ)⁻¹ ^ k ≤ (Real.sqrt 2 / 2) ^ k := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      calc Real.exp (4 * η) * (2 : ℝ)⁻¹ ≤ Real.sqrt 2 * (2 : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hexp4η (by norm_num)
        _ = Real.sqrt 2 / 2 := by ring
    rw [hΦeq, hexpsplit]
    have hsq2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    calc 16 * η ^ 2 * ((k : ℝ) + 1) ^ 2 * (Real.exp (4 * η) * Real.exp (4 * η) ^ k) *
          ((2 : ℝ)⁻¹ ^ k * (q - p))
        = (16 * η ^ 2 * ((k : ℝ) + 1) ^ 2 * (q - p)) *
            (Real.exp (4 * η) * (Real.exp (4 * η) ^ k * (2 : ℝ)⁻¹ ^ k)) := by ring
      _ ≤ (16 * η ^ 2 * ((k : ℝ) + 1) ^ 2 * (q - p)) *
            (Real.sqrt 2 * (Real.sqrt 2 / 2) ^ k) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul hexp4η hratio (by positivity) hsq2
      _ = (16 * Real.sqrt 2 * η ^ 2 * (q - p)) * (((k : ℝ) + 1) ^ 2 * (Real.sqrt 2 / 2) ^ k) := by
          ring
  calc ∫⁻ x in Set.Ico p q, ENNReal.ofReal ((α x - c) ^ 2 * Real.exp |α x - c|)
      ≤ ∑' k : ℕ, ENNReal.ofReal (Φ k * ((2 : ℝ)⁻¹ ^ k * (q - p))) := by
        refine (hstep1.trans (le_of_eq hstep2)).trans ?_
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [hstep3 k]
        exact hterm_bd k
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ((16 * Real.sqrt 2 * η ^ 2 * (q - p)) *
          (((k : ℝ) + 1) ^ 2 * (Real.sqrt 2 / 2) ^ k)) :=
        ENNReal.tsum_le_tsum fun k => ENNReal.ofReal_le_ofReal (hseries_term k)
    _ = ENNReal.ofReal (∑' k : ℕ, (16 * Real.sqrt 2 * η ^ 2 * (q - p)) *
          (((k : ℝ) + 1) ^ 2 * (Real.sqrt 2 / 2) ^ k)) := by
        have hqp0 : (0 : ℝ) ≤ q - p := by linarith
        refine (ENNReal.ofReal_tsum_of_nonneg (fun k => ?_) (jnSum_summable.mul_left _)).symm
        exact mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 16 * Real.sqrt 2 * η ^ 2) hqp0)
          (by positivity)
    _ = ENNReal.ofReal (16 * Real.sqrt 2 * jnSum * η ^ 2 * (q - p)) := by
        rw [tsum_mul_left]
        congr 1
        rw [jnSum]
        ring

/-- From a second-moment bound to a bound on the entropy defect. -/
private lemma entropyDefect_le_of_moment (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (hw : ∀ᵐ t ∂volume, 0 < deriv h t)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (hmeas : Measurable (fun t => Real.log (deriv h t)))
    (p q : ℝ) (hpq : p < q) (M : ℝ) (hM : 0 ≤ M)
    (hmom : ∫⁻ x in Set.Ico p q, ENNReal.ofReal
        ((Real.log (deriv h x) - cellAvg (fun t => Real.log (deriv h t)) p q 0 0) ^ 2 *
          Real.exp |Real.log (deriv h x) -
            cellAvg (fun t => Real.log (deriv h t)) p q 0 0|) ≤
      ENNReal.ofReal (M * (q - p))) :
    entropyDefect (deriv h) p q ≤ M := by
  set α : ℝ → ℝ := fun t => Real.log (deriv h t) with hα_def
  have hqp : (0 : ℝ) < q - p := sub_pos.mpr hpq
  have hcellavg00 : cellAvg α p q 0 0 = intervalAvg α p q := by
    show intervalAvg α (dPt p q 0 0) (dPt p q 0 1) = intervalAvg α p q
    rw [dPt_zero, show (1 : ℕ) = 2 ^ 0 by norm_num, dPt_last]
  set c := cellAvg α p q 0 0 with hc_def
  have hc_eq : c = intervalAvg α p q := hcellavg00
  set s : ℝ → ℝ := fun x => α x - c with hs_def
  have hsmeas : Measurable s := hmeas.sub measurable_const
  have hαint : IntervalIntegrable α volume p q := hα p q hpq
  have hsint : IntervalIntegrable s volume p q := hαint.sub intervalIntegrable_const
  -- the mean of `s` over `[p, q]` vanishes
  have hs_mean : (∫ x in p..q, s x) = 0 := by
    rw [hs_def]
    simp only
    rw [intervalIntegral.integral_sub hαint intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, hc_eq]
    unfold intervalAvg
    field_simp
    ring
  -- the second-moment bound in Bochner form
  set F : ℝ → ℝ := fun x => (s x) ^ 2 * Real.exp |s x| with hF_def
  have hFnn : ∀ x, 0 ≤ F x := fun x => by rw [hF_def]; positivity
  have hFmeas : Measurable F :=
    (hsmeas.pow_const 2).mul (Real.measurable_exp.comp hsmeas.abs)
  have hmom' : ∫⁻ x in Set.Ico p q, ENNReal.ofReal (F x) ≤
      ENNReal.ofReal (M * (q - p)) := hmom
  have hFint : IntegrableOn F (Set.Ico p q) volume := by
    refine ⟨hFmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have hae : ∀ x, ‖F x‖ₑ = ENNReal.ofReal (F x) := by
      intro x
      rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hFnn x)]
    calc ∫⁻ x in Set.Ico p q, ‖F x‖ₑ
        = ∫⁻ x in Set.Ico p q, ENNReal.ofReal (F x) := by simp_rw [hae]
      _ ≤ ENNReal.ofReal (M * (q - p)) := hmom'
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hFbound : (∫ x in Set.Ico p q, F x) ≤ M * (q - p) := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun x => hFnn x) hFmeas.aestronglyMeasurable]
    have hfin : (∫⁻ x in Set.Ico p q, ENNReal.ofReal (F x)) ≠ ⊤ :=
      (hmom'.trans_lt ENNReal.ofReal_lt_top).ne
    calc (∫⁻ x in Set.Ico p q, ENNReal.ofReal (F x)).toReal
        ≤ (ENNReal.ofReal (M * (q - p))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hmom'
      _ = M * (q - p) := ENNReal.toReal_ofReal (by positivity)
  have hFbound' : (∫ x in p..q, F x) ≤ M * (q - p) := by
    rw [intervalIntegral.integral_of_le hpq.le, ← integral_Ico_eq_integral_Ioc]
    exact hFbound
  have hFintv : IntervalIntegrable F volume p q := by
    rw [intervalIntegrable_iff_integrableOn_Ico_of_le hpq.le]
    exact hFint
  -- pointwise Taylor bound and integration
  have hexpint : IntervalIntegrable (fun x => Real.exp (s x)) volume p q := by
    have hdom : IntervalIntegrable (fun x => 1 + s x + F x) volume p q :=
      (IntervalIntegrable.add intervalIntegrable_const hsint).add hFintv
    refine IntervalIntegrable.mono_fun hdom
      ((Real.measurable_exp.comp hsmeas).aestronglyMeasurable) ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall fun x _ => ?_
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.exp_pos (s x)).le]
    have h1 := exp_sub_one_sub_id_le (s x)
    have h2 : Real.exp (s x) ≤ 1 + s x + F x := by rw [hF_def]; linarith
    have h3 : (0:ℝ) ≤ 1 + s x + F x := le_trans (Real.exp_pos (s x)).le h2
    rw [abs_of_nonneg h3]
    exact h2
  have hexp_le : (∫ x in p..q, Real.exp (s x)) ≤ (1 + M) * (q - p) := by
    have hptwise : ∀ x, Real.exp (s x) ≤ 1 + s x + F x := by
      intro x
      have := exp_sub_one_sub_id_le (s x)
      rw [hF_def]
      linarith
    have hmono := intervalIntegral.integral_mono_on hpq.le hexpint
      ((IntervalIntegrable.add intervalIntegrable_const hsint).add hFintv) (fun x _ => hptwise x)
    rw [intervalIntegral.integral_add (IntervalIntegrable.add intervalIntegrable_const hsint) hFintv,
      intervalIntegral.integral_add intervalIntegrable_const hsint,
      intervalIntegral.integral_const, smul_eq_mul, hs_mean, mul_one] at hmono
    calc (∫ x in p..q, Real.exp (s x)) ≤ (q - p) + 0 + ∫ x in p..q, F x := hmono
      _ ≤ (q - p) + 0 + M * (q - p) := by linarith [hFbound']
      _ = (1 + M) * (q - p) := by ring
  -- relate to the entropy defect
  have hderiv_exp : (∫ x in p..q, deriv h x) = ∫ x in p..q, Real.exp (α x) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hw] with x hx _
    rw [hα_def]
    simp only
    rw [Real.exp_log hx]
  have hexp_split : (∫ x in p..q, Real.exp (α x)) =
      Real.exp c * ∫ x in p..q, Real.exp (s x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    show Real.exp (α x) = Real.exp c * Real.exp (s x)
    rw [← Real.exp_add, hs_def]
    congr 1
    ring
  have hgeom : weightGeomMean (deriv h) p q = Real.exp c := by
    unfold weightGeomMean
    rw [hc_eq]
  have hmean : weightMean (deriv h) p q =
      Real.exp c * ((∫ x in p..q, Real.exp (s x)) / (q - p)) := by
    unfold weightMean intervalAvg
    rw [hderiv_exp, hexp_split]
    field_simp
  have hratio : weightMean (deriv h) p q / weightGeomMean (deriv h) p q =
      (∫ x in p..q, Real.exp (s x)) / (q - p) := by
    rw [hmean, hgeom]
    field_simp
  have hratio_le : weightMean (deriv h) p q / weightGeomMean (deriv h) p q ≤ 1 + M := by
    rw [hratio, div_le_iff₀ hqp]
    exact hexp_le
  have hmeanpos : 0 < weightMean (deriv h) p q := by
    rw [weightMean_deriv h hac (ne_of_lt hpq)]
    exact div_pos (sub_pos.mpr (hh hpq)) hqp
  have hgeompos : 0 < weightGeomMean (deriv h) p q := by
    unfold weightGeomMean; exact Real.exp_pos _
  have hratio_pos : 0 < weightMean (deriv h) p q / weightGeomMean (deriv h) p q :=
    div_pos hmeanpos hgeompos
  unfold entropyDefect
  calc Real.log (weightMean (deriv h) p q / weightGeomMean (deriv h) p q)
      ≤ (weightMean (deriv h) p q / weightGeomMean (deriv h) p q) - 1 :=
        Real.log_le_sub_one_of_pos hratio_pos
    _ ≤ (1 + M) - 1 := by linarith [hratio_le]
    _ = M := by ring

/-- **Lemma (Two bounds for `E_h`), part (b)**: there are *universal*
constants `η₀ ∈ (0, 1/2]` and `C* ≥ 1` such that for every `h` with
`α = log h' ∈ BMO(ℝ)`, writing `η := ‖α‖_{BMO(5J)}`, if `η ≤ η₀` then
`E_h(J) ≤ C* η²`. (The `BMO` hypothesis makes `η` the true supremum, not the
junk value `0`.) -/
theorem entropy_bound_bmo :
    ∃ η₀ C : ℝ, 0 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 1 ≤ C ∧
      ∀ h : ℝ → ℝ, StrictMono h → LocallyAbsolutelyContinuous h →
        (∀ᵐ t ∂volume, 0 < deriv h t) →
        (∀ u v : ℝ, u < v →
          IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v) →
        BMO (fun t => Real.log (deriv h t)) →
        ∀ a b : ℝ, a < b →
          bmoSeminorm (fun t => Real.log (deriv h t))
              (a - 2 * (b - a)) (b + 2 * (b - a)) ≤ η₀ →
            entropyBound (deriv h) a b ≤
              C * (bmoSeminorm (fun t => Real.log (deriv h t))
                (a - 2 * (b - a)) (b + 2 * (b - a))) ^ 2 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / 16, 16 * Real.sqrt 2 * jnSum + 1, by positivity, ?_, ?_, ?_⟩
  · have h2 : Real.log 2 ≤ 1 := by
      calc Real.log 2 ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        _ = 1 := by norm_num
    linarith
  · have : (0 : ℝ) ≤ 16 * Real.sqrt 2 * jnSum := by
      have := jnSum_nonneg
      positivity
    linarith
  intro h hh hac hw hα hBMO a b hab hbmo_le
  set α : ℝ → ℝ := fun t => Real.log (deriv h t) with hα_def
  set A := a - 2 * (b - a) with hA_def
  set B := b + 2 * (b - a) with hB_def
  set η := bmoSeminorm α A B with hη_def
  have hab' : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hAB : A < B := by rw [hA_def, hB_def]; linarith
  have hmeasα : Measurable α := (measurable_deriv h).log
  -- the BMO seminorm dominates every mean oscillation on `[A, B]`
  have hbddAbove : BddAbove
      {r : ℝ | ∃ c d, A ≤ c ∧ c < d ∧ d ≤ B ∧ r = intervalOscillation α c d} := by
    obtain ⟨C₀, hC₀⟩ := hBMO
    exact ⟨C₀, by rintro r ⟨c, d, -, hcd, -, rfl⟩; exact hC₀ c d hcd⟩
  have hosc_le : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B → intervalOscillation α p q ≤ η := by
    intro p q hAp hpq hqB
    exact le_csSup hbddAbove ⟨p, q, hAp, hpq, hqB, rfl⟩
  have hηnn : 0 ≤ η := by
    have h0 : 0 ≤ intervalOscillation α A B := by
      unfold intervalOscillation intervalAvg
      apply div_nonneg _ (by linarith)
      exact intervalIntegral.integral_nonneg hAB.le (fun x _ => abs_nonneg _)
    exact h0.trans (hosc_le A B (le_refl A) hAB (le_refl B))
  -- the main bound, with a positive perturbation of `η`
  have hmain : ∀ ε : ℝ, 0 < ε → ε ≤ Real.log 2 / 16 →
      entropyBound (deriv h) a b ≤ 16 * Real.sqrt 2 * jnSum * (η + ε) ^ 2 := by
    intro ε hε hεle
    set η' := η + ε with hη'_def
    have hη'pos : 0 < η' := by rw [hη'_def]; linarith
    have hη'small : η' ≤ Real.log 2 / 8 := by
      rw [hη'_def]
      have : η ≤ Real.log 2 / 16 := hbmo_le
      linarith
    have hosc_le' : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B → intervalOscillation α p q ≤ η' := by
      intro p q hAp hpq hqB
      exact (hosc_le p q hAp hpq hqB).trans (by rw [hη'_def]; linarith)
    set M := 16 * Real.sqrt 2 * jnSum * η' ^ 2 with hM_def
    have hMnn : 0 ≤ M := by
      rw [hM_def]
      have := jnSum_nonneg
      positivity
    -- the pointwise entropy-defect bound on every subinterval of `[A, B]`
    have hdefect : ∀ p q : ℝ, A ≤ p → p < q → q ≤ B →
        entropyDefect (deriv h) p q ≤ M := by
      intro p q hAp hpq hqB
      refine entropyDefect_le_of_moment h hh hac hw hα hmeasα p q hpq M hMnn ?_
      have := exp_moment_bound α hmeasα hα A B η' hAB hη'pos hη'small hosc_le' p q hAp hpq hqB
      refine this.trans (le_of_eq ?_)
      rw [hM_def]
    -- average over `3J` and pass to the supremum
    show sSup (entropyBoundSet (deriv h) a b) ≤ M
    refine csSup_le ⟨_, b - a, hab', le_refl _, rfl⟩ ?_
    rintro r ⟨y₀, hy₀, hy₀le, rfl⟩
    have hAB3 : a - (b - a) ≤ b + (b - a) := by linarith
    have hint : IntegrableOn (fun x => entropyDefect (deriv h) (x - y₀) (x + y₀))
        (Set.Icc (a - (b - a)) (b + (b - a))) volume :=
      entropyDefect_integrableOn h hh hac hα y₀ hy₀ (a - (b - a)) (b + (b - a))
    have hintIntv : IntervalIntegrable
        (fun x => entropyDefect (deriv h) (x - y₀) (x + y₀)) volume
        (a - (b - a)) (b + (b - a)) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hAB3).mpr hint
    have hmono : (∫ x in (a - (b - a))..(b + (b - a)),
        entropyDefect (deriv h) (x - y₀) (x + y₀)) ≤
        ∫ _x in (a - (b - a))..(b + (b - a)), M := by
      apply intervalIntegral.integral_mono_on hAB3 hintIntv intervalIntegrable_const
      intro x hx
      refine hdefect (x - y₀) (x + y₀) ?_ (by linarith) ?_
      · rw [hA_def]; have := hx.1; linarith
      · rw [hB_def]; have := hx.2; linarith
    rw [intervalIntegral.integral_const, smul_eq_mul,
      show b + (b - a) - (a - (b - a)) = 3 * (b - a) by ring] at hmono
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 3 * (b - a)), mul_comm M (3 * (b - a))]
    exact hmono
  -- let the perturbation tend to zero
  have hlimit : entropyBound (deriv h) a b ≤ 16 * Real.sqrt 2 * jnSum * η ^ 2 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set K := 16 * Real.sqrt 2 * jnSum with hK_def
    have hKnn : 0 ≤ K := by rw [hK_def]; have := jnSum_nonneg; positivity
    obtain ⟨ε, hε0, hεle, hsmall⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ Real.log 2 / 16 ∧
        K * (2 * η * ε + ε ^ 2) ≤ δ := by
      have hden : 0 < K * (2 * η + 1) + 1 := by nlinarith [hηnn, hKnn]
      refine ⟨min (Real.log 2 / 16) (min 1 (δ / (K * (2 * η + 1) + 1))), ?_, ?_, ?_⟩
      · exact lt_min (by positivity) (lt_min one_pos (by positivity))
      · exact min_le_left _ _
      · set ε := min (Real.log 2 / 16) (min 1 (δ / (K * (2 * η + 1) + 1))) with hε_def
        have hε1 : ε ≤ 1 := le_trans (min_le_right _ _) (min_le_left _ _)
        have hεd : ε ≤ δ / (K * (2 * η + 1) + 1) :=
          le_trans (min_le_right _ _) (min_le_right _ _)
        have hεpos : 0 < ε := lt_min (by positivity) (lt_min one_pos (by positivity))
        have hstep : K * (2 * η * ε + ε ^ 2) ≤ (K * (2 * η + 1)) * ε := by
          have hKε : 0 ≤ K * ε := mul_nonneg hKnn hεpos.le
          have h2 : 2 * η + ε ≤ 2 * η + 1 := by linarith
          calc K * (2 * η * ε + ε ^ 2) = (K * ε) * (2 * η + ε) := by ring
            _ ≤ (K * ε) * (2 * η + 1) := mul_le_mul_of_nonneg_left h2 hKε
            _ = (K * (2 * η + 1)) * ε := by ring
        have hstep2 : (K * (2 * η + 1)) * ε ≤ δ := by
          have h1 : (K * (2 * η + 1)) * ε ≤ (K * (2 * η + 1) + 1) * ε := by
            nlinarith [hεpos.le]
          have h2 : (K * (2 * η + 1) + 1) * ε ≤ δ := by
            rw [← le_div_iff₀' hden]
            exact hεd
          linarith
        linarith
    have := hmain ε hε0 hεle
    have hexpand : K * (η + ε) ^ 2 = K * η ^ 2 + K * (2 * η * ε + ε ^ 2) := by ring
    calc entropyBound (deriv h) a b ≤ K * (η + ε) ^ 2 := this
      _ = K * η ^ 2 + K * (2 * η * ε + ε ^ 2) := hexpand
      _ ≤ K * η ^ 2 + δ := by linarith
  calc entropyBound (deriv h) a b ≤ 16 * Real.sqrt 2 * jnSum * η ^ 2 := hlimit
    _ ≤ (16 * Real.sqrt 2 * jnSum + 1) * η ^ 2 := by nlinarith [sq_nonneg η, jnSum_nonneg]

/-- **Remark 5.2 (continuity)**: for `h` strictly increasing and continuous,
`ε_h(x, y)` is continuous in `(x, y)` off the diagonal `y = 0` (where the
denominator `h(x+y) - h(x-y)` is nonzero), hence measurable. -/
theorem continuous_eps (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h) :
    ContinuousOn (fun p : ℝ × ℝ => eps h p.1 p.2) {p | p.2 ≠ 0} := by
  have hnum : Continuous fun p : ℝ × ℝ => h (p.1 + p.2) + h (p.1 - p.2) - 2 * h p.1 :=
    ((hc.comp (continuous_fst.add continuous_snd)).add
      (hc.comp (continuous_fst.sub continuous_snd))).sub
      (continuous_const.mul (hc.comp continuous_fst))
  have hdenom : Continuous fun p : ℝ × ℝ => h (p.1 + p.2) - h (p.1 - p.2) :=
    (hc.comp (continuous_fst.add continuous_snd)).sub
      (hc.comp (continuous_fst.sub continuous_snd))
  have heq : (fun p : ℝ × ℝ => eps h p.1 p.2) =
      fun p : ℝ × ℝ => (h (p.1 + p.2) + h (p.1 - p.2) - 2 * h p.1) /
        (h (p.1 + p.2) - h (p.1 - p.2)) := rfl
  rw [heq]
  apply hnum.continuousOn.div hdenom.continuousOn
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp
  have hne : h (p.1 - p.2) ≠ h (p.1 + p.2) := fun he => hp (by
    have hxy : p.1 - p.2 = p.1 + p.2 := hh.injective he
    linarith)
  exact sub_ne_zero.mpr (Ne.symm hne)

end VanishingCarleson

end
