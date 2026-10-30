/-
# The forward inequality on the disk (§4, Steps 1c–1e and 3a–3d)

Everything in the proof of Theorem (Forward Inequality) that happens on the
unit disk, for a circle homeomorphism `g` normalized by `E(g)(0) = 0`.  Write
`a = ⨍ g ζ̄` (`momA`), `b = ⨍ g ζ` (`momB`) and `q = ⨍ g²` (`momQ`); in the
paper's notation `a = ⟨gσ̄⟩`, `b = ⟨gσ⟩`, `q = ⟨g²⟩`.

* `disc_wirt_formula` — implicit differentiation of the barycentric equation
  at the origin gives `(1 - |q|²) Φ_z(0) = a + q b̄ = D` and
  `(1 - |q|²) Φ_z̄(0) = b + q ā = N`, so `μ_{E(g)}(0) = N / D`
  (eq. `mu-formula`; the sign `-N/D` of the paper is the value on `𝕌`).
* `circleMean_eq_zero_of_extension_zero` — `E(g)(0) = 0` is the barycentre
  condition `⨍ g = 0` (eq. `bary-disk`).
* `disc_numerator_le` — Steps 3a–3d: for the boundary values `m` of any
  orientation-preserving automorphism of the disk, `|N| ≤ 5 ⨍ |g - m|`.
-/
import Mathlib
import VanishingCarleson.Localization

open MeasureTheory Real Set

noncomputable section

namespace VanishingCarleson

/-- Solving the two implicit-differentiation equations `A = a + q B̄`,
`B = b + q Ā` for `A` and `B`. -/
private theorem fd_implicit_solve {a b q A B : ℂ} (h1 : A = a + q * star B)
    (h2 : B = b + q * star A) :
    ((1 - ‖q‖ ^ 2 : ℝ) : ℂ) * A = a + q * star b ∧
      ((1 - ‖q‖ ^ 2 : ℝ) : ℂ) * B = b + q * star a := by
  have hqq : q * star q = ((‖q‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.star_def, Complex.conj_mul']
  have hsB : star B = star b + A * star q := by rw [h2, star_add, star_mul, star_star]
  have hsA : star A = star a + B * star q := by rw [h1, star_add, star_mul, star_star]
  push_cast
  exact ⟨by linear_combination h1 + q * hsB + A * hqq,
    by linear_combination h2 + q * hsA + B * hqq⟩

/-- **Steps 1c–1e (disk form)**: for an orientation-preserving homeomorphism
`g` of `S¹` with `E(g)(0) = 0`,
`(1 - |q|²) Φ_z(0) = a + q b̄` and `(1 - |q|²) Φ_z̄(0) = b + q ā`. -/
theorem disc_wirt_formula (g : Circle → Circle) (hg : Function.Bijective g)
    (hgc : Continuous g) (_hor : HasIncreasingLift g) (h0 : extension g 0 = 0) :
    ((1 - ‖momQ (toCM g hgc)‖ ^ 2 : ℝ) : ℂ) * wirtZ (extension g) 0 =
        momA (toCM g hgc) + momQ (toCM g hgc) * star (momB (toCM g hgc)) ∧
      ((1 - ‖momQ (toCM g hgc)‖ ^ 2 : ℝ) : ℂ) * wirtZbar (extension g) 0 =
        momB (toCM g hgc) + momQ (toCM g hgc) * star (momA (toCM g hgc)) := by
  obtain ⟨h1, h2⟩ := hasImplicitDerivAtZero g hg hgc h0
  exact fd_implicit_solve h1 h2

/-- **Eq. `bary-disk`**: `E(g)(0) = 0` means `⨍ g = 0`. -/
theorem circleMean_eq_zero_of_extension_zero (g : Circle → Circle) (hg : Function.Bijective g)
    (hgc : Continuous g) (h0 : extension g 0 = 0) :
    circleMean (toCM g hgc) = 0 := by
  have h : harmonicMeasureAvg 0
      (fun ζ => (((g ζ : Circle) : ℂ) - 0) / (1 - star (0 : ℂ) * ((g ζ : Circle) : ℂ))) = 0 := by
    have hb := extension_baryEq g hg hgc 0 (by simp)
    rw [h0] at hb
    exact hb
  simp only [sub_zero, star_zero, zero_mul, div_one] at h
  rw [harmonicMeasureAvg_zero_eq] at h
  rw [circleMean_apply]
  simp only [toCM_apply]
  exact_mod_cast h

/-- The normalized mean `(2π)⁻¹ ∫₀^{2π}` of a complex function is bounded by the
mean of its modulus. -/
private theorem fd_norm_avg_le (F : ℝ → ℂ) :
    ‖(((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi), F θ‖ ≤
      (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), ‖F θ‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm (by positivity)) (by positivity)

/-- Monotonicity of the normalized mean over `[0, 2π]`. -/
private theorem fd_avg_mono {f h : ℝ → ℝ} (hf : Continuous f) (hh : Continuous h)
    (hle : ∀ θ, f θ ≤ h θ) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), f θ ≤
      (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), h θ :=
  mul_le_mul_of_nonneg_left (intervalIntegral.integral_mono (by positivity)
    (hf.intervalIntegrable _ _) (hh.intervalIntegrable _ _) hle) (by positivity)

/-- The normalized mean of a constant. -/
private theorem fd_avg_const (C : ℝ) :
    (2 * Real.pi)⁻¹ * ∫ _θ in (0:ℝ)..(2 * Real.pi), C = C := by
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, ← mul_assoc,
    inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_mul]

/-- The mean value property on the unit circle, for `f` holomorphic on the
disk and continuous on its closure. -/
private theorem fd_mean_value (f : ℂ → ℂ) (hf : DiffContOnCl ℂ f (Metric.ball (0:ℂ) 1)) :
    (((2 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ θ in (0:ℝ)..(2 * Real.pi), f (Circle.exp θ) = f 0 := by
  have h := harmonicMeasureAvg_eq_of_diffContOnCl f 0 (by simp) hf
  rw [harmonicMeasureAvg_zero_eq] at h
  exact_mod_cast h

/-- **Steps 3a–3d**: if `⨍ g = 0` and `m` is the boundary map of an
orientation-preserving automorphism `M` of the disk, then
`|b + q ā| ≤ 5 ⨍ |g - m|`.  (`⨍ m ζ = 0` because `m` has no negative
frequencies, `⨍ m = M(0)` and `⨍ m² = M(0)²` by the mean value property.) -/
theorem disc_numerator_le (g : Circle → Circle) (hgc : Continuous g)
    (hmean : circleMean (toCM g hgc) = 0)
    (M : ℂ → ℂ) (hM : IsDiskAutPlus M) (m : Circle → Circle)
    (hm : ∀ ζ : Circle, ((m ζ : Circle) : ℂ) = M ζ) :
    ‖momB (toCM g hgc) + momQ (toCM g hgc) * star (momA (toCM g hgc))‖ ≤
      5 * ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖((g (Circle.exp θ) : Circle) : ℂ) - ((m (Circle.exp θ) : Circle) : ℂ)‖) := by
  have hpi : (0:ℝ) < 2 * Real.pi := by positivity
  have hMd : DiffContOnCl ℂ M (Metric.ball (0:ℂ) 1) := isDiskAutPlus_diffContOnCl M hM
  set c : ℂ := (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
  set G : ℝ → ℂ := fun θ => ((g (Circle.exp θ) : Circle) : ℂ)
  set W : ℝ → ℂ := fun θ => ((m (Circle.exp θ) : Circle) : ℂ)
  set E : ℝ → ℂ := fun θ => ((Circle.exp θ : Circle) : ℂ)
  have hGn : ∀ θ, ‖G θ‖ = 1 := fun θ => Circle.norm_coe _
  have hWn : ∀ θ, ‖W θ‖ = 1 := fun θ => Circle.norm_coe _
  have hEn : ∀ θ, ‖E θ‖ = 1 := fun θ => Circle.norm_coe _
  have hEc : Continuous E := continuous_subtype_val.comp Circle.exp.continuous
  have hGc : Continuous G := continuous_subtype_val.comp (hgc.comp Circle.exp.continuous)
  have hWM : ∀ θ, W θ = M (E θ) := fun θ => hm _
  have hWc : Continuous W := by
    rw [show W = fun θ => M (E θ) from funext hWM]
    exact hMd.continuousOn_ball.comp_continuous hEc (fun θ => by
      rw [Metric.mem_closedBall, dist_zero_right, hEn])
  have hii : ∀ F : ℝ → ℂ, Continuous F →
      IntervalIntegrable F MeasureTheory.volume 0 (2 * Real.pi) :=
    fun F hF => hF.intervalIntegrable _ _
  -- the mean value property for `M`, `M(z) z` and `M(z)²`
  have hW0 : c * ∫ θ in (0:ℝ)..(2 * Real.pi), W θ = M 0 := by
    simp only [hWM]
    exact fd_mean_value M hMd
  have hWE : c * ∫ θ in (0:ℝ)..(2 * Real.pi), W θ * E θ = 0 := by
    simp only [hWM]
    have h := fd_mean_value (fun z => M z * z)
      ⟨hMd.differentiableOn.mul differentiableOn_id, hMd.continuousOn.mul continuousOn_id⟩
    rw [mul_zero] at h
    exact h
  have hW2 : c * ∫ θ in (0:ℝ)..(2 * Real.pi), W θ * W θ = M 0 * M 0 := by
    simp only [hWM]
    exact fd_mean_value (fun z => M z * M z)
      ⟨hMd.differentiableOn.mul hMd.differentiableOn, hMd.continuousOn.mul hMd.continuousOn⟩
  -- the moments as means
  have ha_def : momA (toCM g hgc) = c * ∫ θ in (0:ℝ)..(2 * Real.pi), G θ * star (E θ) := by
    rw [momA, circleMean_apply]; rfl
  have hb_def : momB (toCM g hgc) = c * ∫ θ in (0:ℝ)..(2 * Real.pi), G θ * E θ := by
    rw [momB, circleMean_apply]; rfl
  have hq_def : momQ (toCM g hgc) = c * ∫ θ in (0:ℝ)..(2 * Real.pi), G θ * G θ := by
    rw [momQ, circleMean_apply]; rfl
  have hG0 : c * ∫ θ in (0:ℝ)..(2 * Real.pi), G θ = 0 := by
    rw [circleMean_apply] at hmean
    exact hmean
  -- `δ = ⨍ |g - m|`
  set δ : ℝ := (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), ‖G θ - W θ‖ with hδ
  have hδc : Continuous fun θ => ‖G θ - W θ‖ := (hGc.sub hWc).norm
  have hδ0 : 0 ≤ δ :=
    mul_nonneg (by positivity)
      (intervalIntegral.integral_nonneg hpi.le (fun θ _ => norm_nonneg _))
  have hδ2 : δ ≤ 2 := by
    calc δ ≤ (2 * Real.pi)⁻¹ * ∫ _θ in (0:ℝ)..(2 * Real.pi), (2:ℝ) :=
          fd_avg_mono hδc continuous_const (fun θ =>
            (norm_sub_le _ _).trans (by rw [hGn, hWn]; norm_num))
      _ = 2 := fd_avg_const 2
  -- Step 3a: `|a| ≤ 1`
  have ha : ‖momA (toCM g hgc)‖ ≤ 1 := by
    calc ‖momA (toCM g hgc)‖
        ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), ‖G θ * star (E θ)‖ := by
          rw [ha_def]; exact fd_norm_avg_le _
      _ = (2 * Real.pi)⁻¹ * ∫ _θ in (0:ℝ)..(2 * Real.pi), (1:ℝ) := by
          simp only [norm_mul, norm_star, hGn, hEn, mul_one]
      _ = 1 := fd_avg_const 1
  -- Step 3b: `|b| ≤ δ`, since `⨍ m ζ = 0`
  have hb : ‖momB (toCM g hgc)‖ ≤ δ := by
    have hsplit : momB (toCM g hgc)
        = c * ∫ θ in (0:ℝ)..(2 * Real.pi), (G θ - W θ) * E θ := by
      simp only [sub_mul]
      rw [intervalIntegral.integral_sub (hii (fun θ => G θ * E θ) (hGc.mul hEc))
        (hii (fun θ => W θ * E θ) (hWc.mul hEc)), mul_sub, hWE, sub_zero, hb_def]
    calc ‖momB (toCM g hgc)‖
        ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), ‖(G θ - W θ) * E θ‖ := by
          rw [hsplit]; exact fd_norm_avg_le _
      _ = δ := by rw [hδ]; simp only [norm_mul, hEn, mul_one]
  -- Step 3c: `|M(0)| ≤ δ`, since `M(0) = ⨍ m` and `⨍ g = 0`
  have hM0 : ‖M 0‖ ≤ δ := by
    have hsplit : M 0 = c * ∫ θ in (0:ℝ)..(2 * Real.pi), (W θ - G θ) := by
      rw [intervalIntegral.integral_sub (hii _ hWc) (hii _ hGc), mul_sub, hW0, hG0, sub_zero]
    calc ‖M 0‖ ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi), ‖W θ - G θ‖ := by
          rw [hsplit]; exact fd_norm_avg_le _
      _ = δ := by
          rw [hδ]
          congr 1
          exact intervalIntegral.integral_congr (fun θ _ => norm_sub_rev _ _)
  -- Step 3d: `|q| ≤ 2δ + |M(0)|²`, since `⨍ m² = M(0)²`
  have hq : ‖momQ (toCM g hgc)‖ ≤ 2 * δ + ‖M 0‖ ^ 2 := by
    have hsplit : momQ (toCM g hgc)
        = c * (∫ θ in (0:ℝ)..(2 * Real.pi), (G θ * G θ - W θ * W θ)) + M 0 * M 0 := by
      rw [intervalIntegral.integral_sub (hii (fun θ => G θ * G θ) (hGc.mul hGc))
        (hii (fun θ => W θ * W θ) (hWc.mul hWc)), mul_sub, hW2, hq_def]
      ring
    have hpt : ∀ θ, ‖G θ * G θ - W θ * W θ‖ ≤ 2 * ‖G θ - W θ‖ := by
      intro θ
      have h2 : ‖G θ + W θ‖ ≤ 2 := (norm_add_le _ _).trans (by rw [hGn, hWn]; norm_num)
      rw [show G θ * G θ - W θ * W θ = (G θ - W θ) * (G θ + W θ) by ring, norm_mul]
      nlinarith [norm_nonneg (G θ - W θ)]
    calc ‖momQ (toCM g hgc)‖
        ≤ ‖c * (∫ θ in (0:ℝ)..(2 * Real.pi), (G θ * G θ - W θ * W θ))‖ + ‖M 0 * M 0‖ := by
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..(2 * Real.pi), ‖G θ * G θ - W θ * W θ‖)
            + ‖M 0‖ ^ 2 := by
          rw [norm_mul (M 0) (M 0), ← sq (‖M 0‖)]
          exact add_le_add (fd_norm_avg_le _) le_rfl
      _ ≤ (2 * Real.pi)⁻¹ * (∫ θ in (0:ℝ)..(2 * Real.pi), 2 * ‖G θ - W θ‖)
            + ‖M 0‖ ^ 2 :=
          add_le_add (fd_avg_mono ((hGc.mul hGc).sub (hWc.mul hWc)).norm
            (continuous_const.mul hδc) hpt) le_rfl
      _ = 2 * δ + ‖M 0‖ ^ 2 := by
          rw [intervalIntegral.integral_const_mul, hδ]; ring
  -- assembling: `|q| ≤ 2δ + δ² ≤ 4δ` and `|b + q ā| ≤ δ + 4δ`
  have hM0sq : ‖M 0‖ ^ 2 ≤ 2 * δ := by
    nlinarith [mul_le_mul hM0 hM0 (norm_nonneg _) hδ0, mul_le_mul_of_nonneg_left hδ2 hδ0]
  have hqa : ‖momQ (toCM g hgc)‖ * ‖momA (toCM g hgc)‖ ≤ ‖momQ (toCM g hgc)‖ :=
    mul_le_of_le_one_right (norm_nonneg _) ha
  show _ ≤ 5 * δ
  calc ‖momB (toCM g hgc) + momQ (toCM g hgc) * star (momA (toCM g hgc))‖
      ≤ ‖momB (toCM g hgc)‖ + ‖momQ (toCM g hgc) * star (momA (toCM g hgc))‖ :=
        norm_add_le _ _
    _ = ‖momB (toCM g hgc)‖ + ‖momQ (toCM g hgc)‖ * ‖momA (toCM g hgc)‖ := by
        rw [norm_mul, norm_star]
    _ ≤ 5 * δ := by linarith

end VanishingCarleson

end
