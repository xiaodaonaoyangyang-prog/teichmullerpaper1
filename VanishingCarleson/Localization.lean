/-
# Localization of the Douady–Earle extension (§3.3) and its quasiconformality

For `z₀ = x₀ + iy₀ ∈ 𝕌` and `I₀ = [x₀ - y₀, x₀ + y₀]`, the normalized map
`H(t) = (h(x₀ + y₀ t) - h(x₀ - y₀)) / L`, `L = |h(I₀)|`, lies in `𝒦_ρ`
(`normalizeLoc_mem_KFamily`), and conformal naturality gives
`e(H)(i) = (e(h)(z₀) - h(x₀ - y₀)) / L` (`douadyEarle_normalizeLoc`).  Compactness
of `𝒦_ρ` then gives

* **Lemma (DE Localization)** `v₀ ≍_ρ L` (`de_localization`);
* **Corollary (Real-part localization)** `dist(u₀, h(I₀)) ≤ C₀(ρ) L`
  (`real_part_localization`);
* the uniform bound `‖μ_{e(h)}‖_∞ ≤ k(ρ) < 1` (`de_quasiconformal`): the same
  normalization gives `|μ_{e(h)}(z₀)| = |μ_{e(H)}(i)| = |μ_{E(g_H)}(0)|`, which
  is `< 1` at every member of the compact family and continuous on it.
-/
import Mathlib
import VanishingCarleson.Compactness

open MeasureTheory Real Set

noncomputable section

namespace VanishingCarleson

/-- The normalization `H(t) = (h(x + y t) - h(x - y)) / (h(x + y) - h(x - y))`
of the localization proofs. -/
def normalizeLoc (h : ℝ → ℝ) (x y : ℝ) : ℝ → ℝ :=
  fun t => (h (x + y * t) - h (x - y)) / (h (x + y) - h (x - y))

/-- `normalizeLoc h x y = A ∘ h ∘ B` with `A(w) = w / L - h(x - y) / L`, `B(t) = y t + x`. -/
private theorem locAux_normalizeLoc_eq (h : ℝ → ℝ) (x y : ℝ) :
    normalizeLoc h x y = fun t => 1 / (h (x + y) - h (x - y)) * h (y * t + x) +
      -h (x - y) / (h (x + y) - h (x - y)) := by
  funext t
  simp only [normalizeLoc]
  rw [show y * t + x = x + y * t by ring]
  ring

/-- Affine rescaling of the distance to an interval: if the normalized point
`(u - A)/(B - A)` is within `C` of `[0, 1]`, then `u` is within `C (B - A)` of `[A, B]`. -/
private theorem locAux_infDist_Icc_le {u A B C : ℝ} (hAB : A < B)
    (h1 : Metric.infDist ((u - A) / (B - A)) (Set.Icc 0 1) ≤ C) :
    Metric.infDist u (Set.Icc A B) ≤ C * (B - A) := by
  have hL : 0 < B - A := sub_pos.mpr hAB
  obtain ⟨p, hp, hpd⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_infDist_eq_dist
    (Set.nonempty_Icc.mpr zero_le_one) ((u - A) / (B - A))
  rw [hpd, Real.dist_eq] at h1
  have hq : A + (B - A) * p ∈ Set.Icc A B :=
    ⟨by nlinarith [mul_nonneg hL.le hp.1], by nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hp.2)]⟩
  refine (Metric.infDist_le_dist_of_mem hq).trans ?_
  have e : u - (A + (B - A) * p) = (B - A) * ((u - A) / (B - A) - p) := by
    rw [mul_sub, mul_div_cancel₀ _ hL.ne']
    ring
  rw [Real.dist_eq, e, abs_mul, abs_of_pos hL]
  calc (B - A) * |(u - A) / (B - A) - p| ≤ (B - A) * C := mul_le_mul_of_nonneg_left h1 hL.le
    _ = C * (B - A) := mul_comm _ _

/-- The normalized map lies in `𝒦_ρ`. -/
theorem normalizeLoc_mem_KFamily {ρ : ℝ} (_hρ : 1 ≤ ρ) {h : ℝ → ℝ}
    (hqs : Quasisymmetric h ρ) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    normalizeLoc h x y ∈ KFamily ρ := by
  obtain ⟨hmono, hcont, hsurj, hq⟩ := hqs
  have hL : 0 < h (x + y) - h (x - y) := sub_pos.mpr (hmono (by linarith))
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro s t hst
    have h1 : h (x + y * s) < h (x + y * t) := hmono (by nlinarith)
    simp only [normalizeLoc]
    exact div_lt_div_of_pos_right (by linarith) hL
  · unfold normalizeLoc
    fun_prop
  · intro v
    obtain ⟨s, hs⟩ := hsurj (h (x - y) + v * (h (x + y) - h (x - y)))
    refine ⟨(s - x) / y, ?_⟩
    simp only [normalizeLoc]
    rw [mul_div_cancel₀ _ hy.ne', show x + (s - x) = s by ring, hs, div_eq_iff hL.ne']
    ring
  · intro s t ht
    obtain ⟨h1, h2⟩ := hq (x + y * s) (y * t) (mul_pos hy ht)
    have d1 : normalizeLoc h x y (s + t) - normalizeLoc h x y s =
        (h (x + y * s + y * t) - h (x + y * s)) / (h (x + y) - h (x - y)) := by
      simp only [normalizeLoc]
      rw [show x + y * (s + t) = x + y * s + y * t by ring]
      ring
    have d2 : normalizeLoc h x y s - normalizeLoc h x y (s - t) =
        (h (x + y * s) - h (x + y * s - y * t)) / (h (x + y) - h (x - y)) := by
      simp only [normalizeLoc]
      rw [show x + y * (s - t) = x + y * s - y * t by ring]
      ring
    rw [d1, d2, ← mul_div_assoc, ← mul_div_assoc]
    exact ⟨div_le_div_of_nonneg_right h1 hL.le, div_le_div_of_nonneg_right h2 hL.le⟩
  · simp only [normalizeLoc]
    rw [show x + y * -1 = x - y by ring, sub_self, zero_div]
  · simp only [normalizeLoc]
    rw [mul_one, div_self hL.ne']

/-- **The normalization identity**: `e(H)(i) = (e(h)(z₀) - h(x₀ - y₀)) / L`. -/
theorem douadyEarle_normalizeLoc {ρ : ℝ} {h : ℝ → ℝ} (hqs : Quasisymmetric h ρ)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    douadyEarle (normalizeLoc h x y) Complex.I =
      (douadyEarle h ((x : ℂ) + (y : ℂ) * Complex.I) - ((h (x - y) : ℝ) : ℂ)) /
        ((h (x + y) - h (x - y) : ℝ) : ℂ) := by
  obtain ⟨hmono, hcont, hsurj, -⟩ := hqs
  have hL : 0 < h (x + y) - h (x - y) := sub_pos.mpr (hmono (by linarith))
  rw [locAux_normalizeLoc_eq h x y, conformal_naturality h hmono hcont hsurj
    (1 / (h (x + y) - h (x - y))) (-h (x - y) / (h (x + y) - h (x - y))) y x
    (one_div_pos.mpr hL) hy Complex.I (by simp)]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_neg]
  rw [show (y : ℂ) * Complex.I + (x : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I by ring]
  ring

/-- The normalization preserves the modulus of the dilatation:
`|μ_{e(h)}(z₀)| = |μ_{e(H)}(i)|`. -/
theorem norm_complexDilatation_normalizeLoc {ρ : ℝ} {h : ℝ → ℝ} (hqs : Quasisymmetric h ρ)
    (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ‖complexDilatation (douadyEarle (normalizeLoc h x y)) Complex.I‖ =
      ‖complexDilatation (douadyEarle h) ((x : ℂ) + (y : ℂ) * Complex.I)‖ := by
  obtain ⟨hmono, hcont, hsurj, -⟩ := hqs
  have hL : 0 < h (x + y) - h (x - y) := sub_pos.mpr (hmono (by linarith))
  rw [locAux_normalizeLoc_eq h x y, norm_complexDilatation_conformal_naturality h hmono hcont
    hsurj (1 / (h (x + y) - h (x - y))) (-h (x - y) / (h (x + y) - h (x - y))) y x
    (one_div_pos.mpr hL) hy Complex.I (by simp)]
  rw [show (y : ℂ) * Complex.I + (x : ℂ) = (x : ℂ) + (y : ℂ) * Complex.I by ring]

/-- **Lemma (DE Localization)**: for `z₀ = x₀ + iy₀`, `w₀ = e(h)(z₀)` and
`I₀ = [x₀ - y₀, x₀ + y₀]`, `L = |h(I₀)|`, one has `v₀ ≍_ρ L` — the constants
depend only on `ρ`. -/
theorem de_localization (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ h : ℝ → ℝ, Quasisymmetric h ρ → ∀ z₀ : ℂ, 0 < z₀.im →
        c * (h (z₀.re + z₀.im) - h (z₀.re - z₀.im)) ≤ (douadyEarle h z₀).im ∧
        (douadyEarle h z₀).im ≤ C * (h (z₀.re + z₀.im) - h (z₀.re - z₀.im)) := by
  obtain ⟨H₁, hH₁, H₂, hH₂, hext⟩ := compact_functionals ρ hρ Complex.im Complex.continuous_im
  have hc : 0 < (douadyEarle H₂ Complex.I).im :=
    douadyEarle_im_pos H₂ hH₂.1.1 hH₂.1.2.1 hH₂.1.2.2.1 Complex.I (by simp)
  refine ⟨(douadyEarle H₂ Complex.I).im, (douadyEarle H₁ Complex.I).im, hc, (hext H₂ hH₂).1,
    fun h hqs z₀ hz₀ => ?_⟩
  have hL : 0 < h (z₀.re + z₀.im) - h (z₀.re - z₀.im) := sub_pos.mpr (hqs.1 (by linarith))
  have hmem := normalizeLoc_mem_KFamily hρ hqs z₀.re hz₀
  have key : (douadyEarle (normalizeLoc h z₀.re z₀.im) Complex.I).im =
      (douadyEarle h z₀).im / (h (z₀.re + z₀.im) - h (z₀.re - z₀.im)) := by
    rw [douadyEarle_normalizeLoc hqs z₀.re hz₀, Complex.re_add_im, Complex.div_ofReal_im,
      Complex.sub_im, Complex.ofReal_im, sub_zero]
  obtain ⟨h1, h2⟩ := hext _ hmem
  rw [key] at h1 h2
  exact ⟨(le_div_iff₀ hL).mp h2, (div_le_iff₀ hL).mp h1⟩

/-- **Corollary (Real-part localization)**: `dist(u₀, h(I₀)) ≤ C₀(ρ) · L`. -/
theorem real_part_localization (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧
      ∀ h : ℝ → ℝ, Quasisymmetric h ρ → ∀ z₀ : ℂ, 0 < z₀.im →
        Metric.infDist (douadyEarle h z₀).re
            (Set.Icc (h (z₀.re - z₀.im)) (h (z₀.re + z₀.im))) ≤
          C₀ * (h (z₀.re + z₀.im) - h (z₀.re - z₀.im)) := by
  obtain ⟨H₁, _, _, _, hext⟩ := compact_functionals ρ hρ
    (fun w => Metric.infDist w.re (Set.Icc (0 : ℝ) 1))
    ((Metric.continuous_infDist_pt (Set.Icc (0 : ℝ) 1)).comp Complex.continuous_re)
  refine ⟨Metric.infDist (douadyEarle H₁ Complex.I).re (Set.Icc 0 1), Metric.infDist_nonneg,
    fun h hqs z₀ hz₀ => ?_⟩
  have hmem := normalizeLoc_mem_KFamily hρ hqs z₀.re hz₀
  have key : (douadyEarle (normalizeLoc h z₀.re z₀.im) Complex.I).re =
      ((douadyEarle h z₀).re - h (z₀.re - z₀.im)) /
        (h (z₀.re + z₀.im) - h (z₀.re - z₀.im)) := by
    rw [douadyEarle_normalizeLoc hqs z₀.re hz₀, Complex.re_add_im, Complex.div_ofReal_re,
      Complex.sub_re, Complex.ofReal_re]
  have h1 : Metric.infDist (douadyEarle (normalizeLoc h z₀.re z₀.im) Complex.I).re
      (Set.Icc 0 1) ≤ Metric.infDist (douadyEarle H₁ Complex.I).re (Set.Icc 0 1) :=
    (hext _ hmem).1
  rw [key] at h1
  exact locAux_infDist_Icc_le (hqs.1 (by linarith)) h1

/-- A dilatation bound `k₀ < 1` is `(K - 1)/(K + 1)` for `K = (1 + k₀)/(1 - k₀) ≥ 1`. -/
private theorem locAux_exists_K {k₀ : ℝ} (hk0 : 0 ≤ k₀) (hk1 : k₀ < 1) :
    ∃ K : ℝ, 1 ≤ K ∧ (K - 1) / (K + 1) = k₀ := by
  have hpos : 0 < 1 - k₀ := by linarith
  have hK0 : 0 ≤ (1 + k₀) / (1 - k₀) := div_nonneg (by linarith) hpos.le
  refine ⟨(1 + k₀) / (1 - k₀), ?_, ?_⟩
  · rw [le_div_iff₀ hpos]
    linarith
  · have hKm : (1 + k₀) / (1 - k₀) * (1 - k₀) = 1 + k₀ := div_mul_cancel₀ _ hpos.ne'
    rw [div_eq_iff (by linarith : (0 : ℝ) < (1 + k₀) / (1 - k₀) + 1).ne']
    linear_combination hKm

/-- **Quasiconformality of the extension**: for a `ρ`-quasisymmetric `h`,
`e(h)` is `K`-quasiconformal with `K = K(ρ)`; equivalently its complex
dilatation is *uniformly* bounded by `(K - 1)/(K + 1) < 1`. -/
theorem de_quasiconformal (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ∃ K : ℝ, 1 ≤ K ∧
      ∀ h : ℝ → ℝ, Quasisymmetric h ρ → ∀ z : ℂ, 0 < z.im →
        ‖complexDilatation (douadyEarle h) z‖ ≤ (K - 1) / (K + 1) := by
  have h0 : ‖(0 : ℂ)‖ < 1 := by simp
  have hcont : ContinuousOn (fun g : C(Circle, Circle) => ‖complexDilatation (extension g) 0‖)
      (KImage ρ) := fun g hg =>
    (continuousWithinAt_complexDilatation_extension h0 (KImage ρ)
      (fun ψ hψ => (KImage_spec hψ).1) g hg (KImage_spec hg).2).norm
  have hne : (KImage ρ).Nonempty := ⟨_, kConj_mem_KImage _ (affine_mem_KFamily ρ hρ)⟩
  obtain ⟨g₀, hg₀, hmax⟩ := (compact_KFamily ρ hρ).exists_isMaxOn hne hcont
  have hbound : ∀ H (hH : H ∈ KFamily ρ), ‖complexDilatation (extension (cayleyConj H)) 0‖ ≤
      ‖complexDilatation (extension g₀) 0‖ := by
    intro H hH
    have e : cayleyConj H = ⇑(kConj H hH) := by simp only [kConj, ContinuousMap.coe_mk]
    rw [e]
    exact isMaxOn_iff.mp hmax _ (kConj_mem_KImage H hH)
  have hk1 : ‖complexDilatation (extension g₀) 0‖ < 1 := by
    obtain ⟨hb, hor⟩ := KImage_spec hg₀
    have hlt := norm_wirtZbar_lt_norm_wirtZ_extension g₀ hb g₀.continuous hor 0 h0
    have hpos : 0 < ‖wirtZ (extension g₀) 0‖ := lt_of_le_of_lt (norm_nonneg _) hlt
    rw [complexDilatation, norm_div]
    exact (div_lt_one hpos).mpr hlt
  obtain ⟨K, hK1, hKk⟩ := locAux_exists_K (norm_nonneg _) hk1
  refine ⟨K, hK1, fun h hqs z hz => ?_⟩
  have hH := normalizeLoc_mem_KFamily hρ hqs z.re hz
  rw [hKk, ← Complex.re_add_im z, ← norm_complexDilatation_normalizeLoc hqs z.re hz,
    norm_complexDilatation_douadyEarle _ hH.1.1 hH.1.2.1 hH.1.2.2.1 Complex.I (by simp), cayley_I]
  exact hbound _ hH

end VanishingCarleson

end
