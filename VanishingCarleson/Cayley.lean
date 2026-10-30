/-
# The Cayley transform

The Cayley transform `γ(z) = (z - i)/(z + i)` carries the upper half-plane `𝕌`
onto the unit disk `Δ` and `ℝ` onto `S¹ ∖ {1}`.  This file collects

* `γ`, `γ⁻¹` and the parametrisation `cayleyCircle : ℝ → S¹` of `S¹ ∖ {1}`;
* the transfer identity (2.1) for the normalized automorphisms, `λ(w)`;
* the Cayley-difference identity of Step 3e of the forward inequality;
* the **Cayley conjugate** `cayleyConj h = γ ∘ h ∘ γ⁻¹` of a homeomorphism `h`
  of `ℝ`, a homeomorphism of `S¹` fixing `1 = γ(∞)`;
* the **transfer of harmonic measure**: `P_z(t) dt` on `ℝ` is the pull-back
  under `γ` of the harmonic measure of `Δ` at `γ(z)`.

These are the bridge between the paper, which works on `𝕌`, and the
Douady–Earle development `DouadyEarleExt`, which works on `Δ`.
-/
import Mathlib
import VanishingCarleson.Basic
import DouadyEarleExt.ImplicitZero

open MeasureTheory Real Set

noncomputable section

namespace VanishingCarleson

/-! ## The transform and its inverse -/

/-- The Cayley transform `γ(z) = (z - i)/(z + i)`, mapping `𝕌 → Δ` and
`ℝ → S¹`, with `γ(i) = 0`. -/
def cayley (z : ℂ) : ℂ := (z - Complex.I) / (z + Complex.I)

/-- The inverse Cayley transform `γ⁻¹(ζ) = i(1 + ζ)/(1 - ζ)`. -/
def cayleyInv (ζ : ℂ) : ℂ := Complex.I * (1 + ζ) / (1 - ζ)

/-- The Cayley transform as a map `ℝ → S¹`, in the form
`γ(t) = e^{i(2 arctan t - π)}`. -/
def cayleyCircle (t : ℝ) : Circle := Circle.exp (2 * Real.arctan t - Real.pi)

/-- `cayleyCircle` really is the Cayley transform. -/
theorem cayleyCircle_coe (t : ℝ) : ((cayleyCircle t : Circle) : ℂ) = cayley (t : ℂ) := by
  have h1 : (0:ℝ) ≤ 1 + t ^ 2 := by positivity
  have hc : Real.cos (2 * Real.arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
    rw [Real.cos_two_mul, Real.cos_arctan, div_pow, one_pow, Real.sq_sqrt h1]
    field_simp
    ring
  have hs : Real.sin (2 * Real.arctan t) = 2 * t / (1 + t ^ 2) := by
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan, mul_assoc, div_mul_div_comm, mul_one,
      Real.mul_self_sqrt h1, mul_div_assoc]
  have hc' : (Real.cos (2 * Real.arctan t) : ℂ) = (1 - (t:ℂ) ^ 2) / (1 + (t:ℂ) ^ 2) := by
    rw [hc]; push_cast; ring
  have hs' : (Real.sin (2 * Real.arctan t) : ℂ) = 2 * (t:ℂ) / (1 + (t:ℂ) ^ 2) := by
    rw [hs]; push_cast; ring
  show (Circle.exp (2 * Real.arctan t - Real.pi) : ℂ) = ((t:ℂ) - Complex.I) / ((t:ℂ) + Complex.I)
  rw [Circle.coe_exp]
  have hexp : Complex.exp (((2 * Real.arctan t - Real.pi : ℝ) : ℂ) * Complex.I) =
      -Complex.exp (((2 * Real.arctan t : ℝ) : ℂ) * Complex.I) := by
    push_cast
    rw [sub_mul, Complex.exp_sub, Complex.exp_pi_mul_I]
    ring
  rw [hexp, Complex.exp_ofReal_mul_I, hc', hs']
  have h1c : (1:ℂ) + (t:ℂ) ^ 2 ≠ 0 := by
    have h1pos : (0:ℝ) < 1 + t ^ 2 := by positivity
    exact_mod_cast h1pos.ne'
  have htI : (t:ℂ) + Complex.I ≠ 0 := by
    intro heq
    have him := congrArg Complex.im heq
    simp at him
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- `γ⁻¹` inverts `γ` on the circle minus the point `1`. -/
theorem cayleyInv_cayleyCircle (t : ℝ) : (cayleyInv ((cayleyCircle t : Circle) : ℂ)).re = t := by
  rw [cayleyCircle_coe]
  have htI : (t:ℂ) + Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have heq : cayleyInv (cayley (t:ℂ)) = (t:ℂ) := by
    unfold cayleyInv cayley
    field_simp
    ring_nf
  rw [heq]
  simp

/-- The Möbius involution `σ_W(Z) = (Z - W)/(1 - W̄ Z)` of the unit disk,
exchanging `0` and `W`. -/
def diskInvolution (W Z : ℂ) : ℂ := (Z - W) / (1 - star W * Z)

/-- The unimodular factor `λ(w) = -|w + i|² / (w + i)²` of the transfer
identity (2.1). -/
def lambdaFactor (w : ℂ) : ℂ := -((‖w + Complex.I‖ ^ 2 : ℝ) : ℂ) / (w + Complex.I) ^ 2

/-- **Transfer identity (2.1)**: `σ_{γ(w)}(γ(u)) = λ(w) (u - w)/(u - w̄)`,
the two normalized conformal maps `𝕌 → Δ` carrying `w` to `0` differing by
the unimodular constant `λ(w)`. -/
theorem cayley_involution_transfer (w u : ℂ) (hw : 0 < w.im) (hu : u ≠ star w)
    (hu2 : u ≠ -Complex.I) :
    diskInvolution (cayley w) (cayley u) = lambdaFactor w * ((u - w) / (u - star w)) := by
  have hp : w + Complex.I ≠ 0 := by
    intro h
    have him : (w + Complex.I).im = 0 := by rw [h]; simp
    simp only [Complex.add_im, Complex.I_im] at him
    linarith
  have hq : u + Complex.I ≠ 0 := by
    intro h
    exact hu2 (by linear_combination h)
  have hsw : u - star w ≠ 0 := sub_ne_zero.mpr hu
  have hstarI : star Complex.I = -Complex.I := Complex.conj_I
  have hstarp_eq : star (w + Complex.I) = star w - Complex.I := by
    rw [star_add, hstarI]; ring
  have hp' : star w - Complex.I ≠ 0 := hstarp_eq ▸ star_ne_zero.mpr hp
  have hnormsq : ((‖w + Complex.I‖ ^ 2 : ℝ) : ℂ) = (w + Complex.I) * (star w - Complex.I) := by
    rw [Complex.sq_norm, ← hstarp_eq]
    exact (Complex.mul_conj (w + Complex.I)).symm
  have hstarcayleyw : star (cayley w) = (star w + Complex.I) / (star w - Complex.I) := by
    unfold cayley
    rw [star_div₀, star_sub, star_add, hstarI]
    ring
  have hden : (1 : ℂ) - star (cayley w) * cayley u ≠ 0 := by
    rw [hstarcayleyw]
    unfold cayley
    intro heq
    rw [div_mul_div_comm, sub_eq_zero, eq_comm, div_eq_one_iff_eq (mul_ne_zero hp' hq)] at heq
    have heq3 : (2 : ℂ) * Complex.I * (u - star w) = 0 := by linear_combination heq
    rcases mul_eq_zero.mp heq3 with h2I | huw
    · exact (mul_ne_zero (two_ne_zero) Complex.I_ne_zero) h2I
    · exact hsw huw
  unfold diskInvolution
  rw [div_eq_iff hden, hstarcayleyw]
  unfold cayley lambdaFactor
  rw [hnormsq]
  field_simp
  ring_nf

/-- `|λ(w)| = 1`. -/
theorem lambdaFactor_norm (w : ℂ) (hw : 0 < w.im) : ‖lambdaFactor w‖ = 1 := by
  have hne : w + Complex.I ≠ 0 := by
    intro h
    have him : (w + Complex.I).im = 0 := by rw [h]; simp
    simp only [Complex.add_im, Complex.I_im] at him
    linarith
  have hnorm_ne : ‖w + Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  unfold lambdaFactor
  rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    norm_pow]
  exact div_self (pow_ne_zero 2 hnorm_ne)

/-- **Step 3e (the Cayley-difference identity)**: for real `u, v` and
`w₀ ∈ 𝕌`,
`|（u - w₀)/(u - w̄₀) - (v - w₀)/(v - w̄₀)| = 2 v₀ |u - v| / (|u - w̄₀| |v - w̄₀|)`. -/
theorem cayley_difference_identity (u v : ℝ) (w₀ : ℂ) (hw₀ : 0 < w₀.im) :
    ‖((u : ℂ) - w₀) / ((u : ℂ) - star w₀) - ((v : ℂ) - w₀) / ((v : ℂ) - star w₀)‖ =
      2 * w₀.im * |u - v| / (‖(u : ℂ) - star w₀‖ * ‖(v : ℂ) - star w₀‖) := by
  have hstarim : (star w₀).im = -w₀.im := Complex.conj_im w₀
  have hu : (u : ℂ) - star w₀ ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, hstarim, Complex.zero_im] at him
    linarith
  have hv : (v : ℂ) - star w₀ ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.ofReal_im, hstarim, Complex.zero_im] at him
    linarith
  have hstar : w₀ - star w₀ = 2 * Complex.I * (w₀.im : ℂ) := by
    apply Complex.ext
    · simp
    · simp; ring
  have hkey : ((u : ℂ) - w₀) / ((u : ℂ) - star w₀) - ((v : ℂ) - w₀) / ((v : ℂ) - star w₀) =
      (2 * Complex.I * (w₀.im : ℂ) * ((u : ℂ) - (v : ℂ))) /
        (((u : ℂ) - star w₀) * ((v : ℂ) - star w₀)) := by
    rw [div_sub_div _ _ hu hv]
    congr 1
    linear_combination ((u : ℂ) - (v : ℂ)) * hstar
  have hcast_norm : ∀ r : ℝ, ‖(r : ℂ)‖ = |r| := by
    intro r
    rcases le_total 0 r with h | h
    · rw [Complex.norm_of_nonneg h, abs_of_nonneg h]
    · rw [show (r : ℂ) = -((-r : ℝ) : ℂ) by push_cast; ring, norm_neg,
        Complex.norm_of_nonneg (by linarith), abs_of_nonpos h]
  have hnum : ‖(2 : ℂ) * Complex.I * (w₀.im : ℂ) * ((u : ℂ) - (v : ℂ))‖ = 2 * w₀.im * |u - v| := by
    have huv : (u : ℂ) - (v : ℂ) = ((u - v : ℝ) : ℂ) := by push_cast; ring
    rw [huv, norm_mul, norm_mul, norm_mul, Complex.norm_I, hcast_norm, hcast_norm]
    rw [abs_of_pos hw₀]
    have h2 : ‖(2 : ℂ)‖ = 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, hcast_norm]; norm_num
    rw [h2]
    ring
  rw [hkey, norm_div, hnum, norm_mul]


/-! ## Mapping properties -/

theorem cayley_I : cayley Complex.I = 0 := by
  simp [cayley]

theorem cayleyInv_zero : cayleyInv 0 = Complex.I := by
  simp [cayleyInv]

private lemma cay_add_I_ne_zero {z : ℂ} (hz : z ≠ -Complex.I) : z + Complex.I ≠ 0 :=
  fun h => hz (eq_neg_of_add_eq_zero_left h)

private lemma cay_ofReal_add_I_ne_zero (t : ℝ) : (t : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

private lemma cay_add_I_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) : z + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at this
  linarith

/-- `Im γ⁻¹(ζ) = (1 - |ζ|²)/|1 - ζ|²` (both sides vanish at `ζ = 1`). -/
private lemma cay_cayleyInv_im (ζ : ℂ) :
    (cayleyInv ζ).im = (1 - Complex.normSq ζ) / Complex.normSq (1 - ζ) := by
  simp only [cayleyInv, Complex.div_im, Complex.mul_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, Complex.normSq_apply ζ]
  ring

/-- `γ` maps `𝕌` into `Δ`. -/
theorem norm_cayley_lt_one {z : ℂ} (hz : 0 < z.im) : ‖cayley z‖ < 1 := by
  have hpos : 0 < ‖z + Complex.I‖ := norm_pos_iff.mpr (cay_add_I_ne_zero_of_im_pos hz)
  rw [cayley, norm_div, div_lt_one hpos]
  have h1 : ‖z - Complex.I‖ ^ 2 < ‖z + Complex.I‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

/-- `γ⁻¹` maps `Δ` into `𝕌`. -/
theorem im_cayleyInv_pos {ζ : ℂ} (hζ : ‖ζ‖ < 1) : 0 < (cayleyInv ζ).im := by
  have hne : 1 - ζ ≠ 0 :=
    sub_ne_zero.mpr (fun h => by rw [← h, norm_one] at hζ; exact lt_irrefl _ hζ)
  rw [cay_cayleyInv_im]
  apply div_pos
  · rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ζ]
  · exact Complex.normSq_pos.mpr hne

theorem cayleyInv_cayley {z : ℂ} (hz : z ≠ -Complex.I) : cayleyInv (cayley z) = z := by
  have hzI := cay_add_I_ne_zero hz
  have h1 : 1 + cayley z = 2 * z / (z + Complex.I) := by
    unfold cayley; field_simp; ring
  have h2 : 1 - cayley z = 2 * Complex.I / (z + Complex.I) := by
    unfold cayley; field_simp; ring
  unfold cayleyInv
  rw [h1, h2, mul_div_assoc', div_div_div_cancel_right₀ hzI]
  field_simp

theorem cayley_cayleyInv {ζ : ℂ} (hζ : ζ ≠ 1) : cayley (cayleyInv ζ) = ζ := by
  have h1 : 1 - ζ ≠ 0 := sub_ne_zero.mpr (Ne.symm hζ)
  have ha : cayleyInv ζ - Complex.I = 2 * Complex.I * ζ / (1 - ζ) := by
    unfold cayleyInv; field_simp; ring
  have hb : cayleyInv ζ + Complex.I = 2 * Complex.I / (1 - ζ) := by
    unfold cayleyInv; field_simp; ring
  unfold cayley
  rw [ha, hb, div_div_div_cancel_right₀ h1]
  field_simp

/-- `cayleyCircle` omits the point `1 = γ(∞)`. -/
theorem cayleyCircle_ne_one (t : ℝ) : cayleyCircle t ≠ 1 := by
  intro h
  have h1 : ((cayleyCircle t : Circle) : ℂ) = 1 := Circle.coe_eq_one.mpr h
  rw [cayleyCircle_coe, cayley, div_eq_one_iff_eq (cay_ofReal_add_I_ne_zero t)] at h1
  have := congrArg Complex.im h1
  simp at this
  norm_num at this

theorem continuous_cayleyCircle : Continuous cayleyCircle :=
  Circle.exp.continuous.comp
    ((continuous_const.mul Real.continuous_arctan).sub continuous_const)

theorem cayleyCircle_injective : Function.Injective cayleyCircle := by
  intro a b hab
  calc a = (cayleyInv ((cayleyCircle a : Circle) : ℂ)).re := (cayleyInv_cayleyCircle a).symm
    _ = (cayleyInv ((cayleyCircle b : Circle) : ℂ)).re := by rw [hab]
    _ = b := cayleyInv_cayleyCircle b

/-- Every point of `S¹ ∖ {1}` is `γ(t)` for `t = Re γ⁻¹(ζ)`. -/
theorem cayleyCircle_cayleyInv_re (ζ : Circle) (hζ : ζ ≠ 1) :
    cayleyCircle (cayleyInv (ζ : ℂ)).re = ζ := by
  have hζ1 : (ζ : ℂ) ≠ 1 := fun h => hζ (Circle.coe_eq_one.mp h)
  have him : (cayleyInv (ζ : ℂ)).im = 0 := by
    rw [cay_cayleyInv_im, Circle.normSq_coe, sub_self, zero_div]
  have hreal : (((cayleyInv (ζ : ℂ)).re : ℝ) : ℂ) = cayleyInv (ζ : ℂ) := by
    apply Complex.ext <;> simp [him]
  apply Circle.ext
  rw [cayleyCircle_coe, hreal, cayley_cayleyInv hζ1]

/-! ## The Cayley conjugate of a homeomorphism of `ℝ` -/

open Classical in
/-- The Cayley conjugate `g_h = γ ∘ h ∘ γ⁻¹ : S¹ → S¹` of `h : ℝ → ℝ`, extended
by `g_h(1) = 1` at the point `1 = γ(∞)`.  For an increasing homeomorphism `h`
of `ℝ` this is the circle homeomorphism `g = γ ∘ h ∘ γ⁻¹` of the paper. -/
def cayleyConj (h : ℝ → ℝ) (ζ : Circle) : Circle :=
  if ζ = 1 then 1 else cayleyCircle (h (cayleyInv (ζ : ℂ)).re)

theorem cayleyConj_one (h : ℝ → ℝ) : cayleyConj h 1 = 1 := by
  simp [cayleyConj]

private lemma cay_cayleyConj_of_ne (h : ℝ → ℝ) {ζ : Circle} (hζ : ζ ≠ 1) :
    cayleyConj h ζ = cayleyCircle (h (cayleyInv (ζ : ℂ)).re) := by
  simp only [cayleyConj, hζ, ↓reduceIte]

theorem cayleyConj_cayleyCircle (h : ℝ → ℝ) (t : ℝ) :
    cayleyConj h (cayleyCircle t) = cayleyCircle (h t) := by
  rw [cay_cayleyConj_of_ne h (cayleyCircle_ne_one t), cayleyInv_cayleyCircle]

/-- On the circle, `g_h(γ(t)) = γ(h(t))` as complex numbers. -/
theorem cayleyConj_cayleyCircle_coe (h : ℝ → ℝ) (t : ℝ) :
    ((cayleyConj h (cayleyCircle t) : Circle) : ℂ) = cayley ((h t : ℝ) : ℂ) := by
  rw [cayleyConj_cayleyCircle, cayleyCircle_coe]

/-- `|γ(u) - 1| = 2/|u + i|` for real `u`. -/
private lemma cay_dist_cayleyCircle_one (u : ℝ) :
    dist (cayleyCircle u) 1 = 2 / ‖(u : ℂ) + Complex.I‖ := by
  have hu := cay_ofReal_add_I_ne_zero u
  have hd : dist (cayleyCircle u) 1 = ‖((cayleyCircle u : Circle) : ℂ) - 1‖ := by
    rw [← dist_eq_norm]; rfl
  have heq : cayley (u : ℂ) - 1 = -(2 * Complex.I) / ((u : ℂ) + Complex.I) := by
    unfold cayley; field_simp; ring
  rw [hd, cayleyCircle_coe, heq, norm_div, norm_neg, norm_mul, Complex.norm_I, mul_one]
  simp

private lemma cay_abs_le_norm_add_I (u : ℝ) : |u| ≤ ‖(u : ℂ) + Complex.I‖ := by
  have := Complex.abs_re_le_norm ((u : ℂ) + Complex.I)
  simpa using this

private lemma cay_norm_add_I_le (u : ℝ) : ‖(u : ℂ) + Complex.I‖ ≤ |u| + 1 := by
  refine (norm_add_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]

/-- The Cayley conjugate of an increasing homeomorphism of `ℝ` is continuous
(at `1` because `h(t) → ±∞` as `t → ±∞`). -/
theorem continuous_cayleyConj {h : ℝ → ℝ} (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) : Continuous (cayleyConj h) := by
  rw [continuous_iff_continuousAt]
  intro ζ₀
  by_cases h0 : ζ₀ = 1
  · subst h0
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨a, ha⟩ := hsurj (2 / ε)
    obtain ⟨b, hb⟩ := hsurj (-(2 / ε))
    set M : ℝ := max |a| |b| with hM
    have hM0 : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left _ _)
    refine ⟨2 / (M + 1), by positivity, fun ζ hζ => ?_⟩
    rw [cayleyConj_one]
    by_cases hζ1 : ζ = 1
    · rw [hζ1, cayleyConj_one, dist_self]
      exact hε
    set t : ℝ := (cayleyInv (ζ : ℂ)).re with ht
    have hζt : ζ = cayleyCircle t := (cayleyCircle_cayleyInv_re ζ hζ1).symm
    rw [hζt, cay_dist_cayleyCircle_one] at hζ
    rw [hζt, cayleyConj_cayleyCircle, cay_dist_cayleyCircle_one]
    have htI : 0 < ‖(t : ℂ) + Complex.I‖ := norm_pos_iff.mpr (cay_ofReal_add_I_ne_zero t)
    have h1 : M + 1 < ‖(t : ℂ) + Complex.I‖ :=
      (div_lt_div_iff_of_pos_left two_pos htI (by positivity)).mp hζ
    have h2 : M < |t| := by linarith [cay_norm_add_I_le t]
    have h3 : 2 / ε < |h t| := by
      rcases lt_abs.mp h2 with h4 | h4
      · have : a < t := lt_of_le_of_lt ((le_abs_self a).trans (le_max_left _ _)) h4
        have := hh this
        rw [ha] at this
        exact lt_of_lt_of_le this (le_abs_self _)
      · have : t < b := by
          have := (neg_le_neg (le_max_right |a| |b|)).trans (neg_abs_le b)
          linarith
        have := hh this
        rw [hb] at this
        exact lt_of_lt_of_le (by linarith) (neg_le_abs (h t))
    have h5 : 2 / ε < ‖((h t : ℝ) : ℂ) + Complex.I‖ :=
      lt_of_lt_of_le h3 (cay_abs_le_norm_add_I (h t))
    have h6 : 0 < ‖((h t : ℝ) : ℂ) + Complex.I‖ := lt_trans (by positivity) h5
    rw [div_lt_iff₀ h6]
    have := (div_lt_iff₀ hε).mp h5
    linarith
  · have heq : (fun ζ : Circle => cayleyCircle (h (cayleyInv (ζ : ℂ)).re)) =ᶠ[nhds ζ₀]
        cayleyConj h := by
      filter_upwards [eventually_ne_nhds h0] with ζ hζ
      exact (cay_cayleyConj_of_ne h hζ).symm
    refine ContinuousAt.congr ?_ heq
    have hζ1 : (1 : ℂ) - ζ₀ ≠ 0 :=
      sub_ne_zero.mpr (fun h' => h0 (Circle.coe_eq_one.mp h'.symm))
    have hcoe : Continuous (fun ζ : Circle => (ζ : ℂ)) := continuous_subtype_val
    have hinv : ContinuousAt (fun ζ : Circle => cayleyInv (ζ : ℂ)) ζ₀ := by
      unfold cayleyInv
      exact ((continuous_const.mul (continuous_const.add hcoe)).continuousAt).div
        ((continuous_const.sub hcoe).continuousAt) hζ1
    exact continuous_cayleyCircle.continuousAt.comp
      (hc.continuousAt.comp (Complex.continuous_re.continuousAt.comp hinv))

theorem bijective_cayleyConj {h : ℝ → ℝ} (hh : StrictMono h) (_hc : Continuous h)
    (hsurj : Function.Surjective h) : Function.Bijective (cayleyConj h) := by
  constructor
  · intro ζ₁ ζ₂ heq
    by_cases h1 : ζ₁ = 1 <;> by_cases h2 : ζ₂ = 1
    · rw [h1, h2]
    · exfalso
      rw [h1, cayleyConj_one, cay_cayleyConj_of_ne h h2] at heq
      exact cayleyCircle_ne_one _ heq.symm
    · exfalso
      rw [h2, cayleyConj_one, cay_cayleyConj_of_ne h h1] at heq
      exact cayleyCircle_ne_one _ heq
    · rw [cay_cayleyConj_of_ne h h1, cay_cayleyConj_of_ne h h2] at heq
      have := hh.injective (cayleyCircle_injective heq)
      calc ζ₁ = cayleyCircle (cayleyInv (ζ₁ : ℂ)).re := (cayleyCircle_cayleyInv_re ζ₁ h1).symm
        _ = cayleyCircle (cayleyInv (ζ₂ : ℂ)).re := by rw [this]
        _ = ζ₂ := cayleyCircle_cayleyInv_re ζ₂ h2
  · intro η
    by_cases hη : η = 1
    · exact ⟨1, by rw [hη, cayleyConj_one]⟩
    · obtain ⟨t, ht⟩ := hsurj (cayleyInv (η : ℂ)).re
      exact ⟨cayleyCircle t, by rw [cayleyConj_cayleyCircle, ht, cayleyCircle_cayleyInv_re η hη]⟩

/-- The Cayley conjugate of an *increasing* homeomorphism of `ℝ` is orientation
preserving. -/
theorem hasIncreasingLift_cayleyConj {h : ℝ → ℝ} (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) : HasIncreasingLift (cayleyConj h) := by
  obtain ⟨H, hmon, hcoe⟩ := CircleLift.exists_strictMono_lift (cayleyConj h)
    (bijective_cayleyConj hh hc hsurj) (continuous_cayleyConj hh hc hsurj)
  rcases hmon with ⟨hm, hp⟩ | ⟨ha, hp⟩
  · exact ⟨H, hm, hp, hcoe⟩
  exfalso
  have hπ := Real.pi_pos
  -- the lift at `γ(s)` is `2 arctan (h s) - π` up to a multiple of `2π`
  have key : ∀ s : ℝ, ∃ k : ℤ,
      H (2 * arctan s - π) = 2 * arctan (h s) - π + k * (2 * π) := by
    intro s
    have e := hcoe (2 * arctan s - π)
    have e2 : ((cayleyConj h (Circle.exp (2 * arctan s - π)) : Circle) : ℂ) =
        Complex.exp (((2 * arctan (h s) - π : ℝ) : ℂ) * Complex.I) := by
      rw [show Circle.exp (2 * arctan s - π) = cayleyCircle s from rfl,
        cayleyConj_cayleyCircle]
      rfl
    rw [e2] at e
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp e.symm
    refine ⟨k, ?_⟩
    generalize 2 * arctan (h s) - π = A at hk ⊢
    generalize H (2 * arctan s - π) = B at hk ⊢
    have := congrArg Complex.im hk
    simp at this
    linarith
  obtain ⟨k₁, hk₁⟩ := key (-1)
  obtain ⟨k₂, hk₂⟩ := key 0
  obtain ⟨k₃, hk₃⟩ := key 1
  have a12 : arctan (-1) < arctan 0 := arctan_strictMono (by norm_num)
  have a23 : arctan 0 < arctan 1 := arctan_strictMono (by norm_num)
  have b12 : arctan (h (-1)) < arctan (h 0) := arctan_strictMono (hh (by norm_num))
  have b23 : arctan (h 0) < arctan (h 1) := arctan_strictMono (hh (by norm_num))
  have c1 := neg_pi_div_two_lt_arctan (-1)
  have c3 := arctan_lt_pi_div_two 1
  have d1 := neg_pi_div_two_lt_arctan (h (-1))
  have d3 := arctan_lt_pi_div_two (h 1)
  -- `H` decreases along the three points, but by less than `2π`
  have e12 := ha (show 2 * arctan (-1) - π < 2 * arctan 0 - π by linarith)
  have e23 := ha (show 2 * arctan 0 - π < 2 * arctan 1 - π by linarith)
  have e13 := ha (show 2 * arctan 1 - π < 2 * arctan (-1) - π + 2 * π by linarith)
  rw [hp] at e13
  have k12 : (k₂ : ℝ) < k₁ := by
    by_contra hcon
    have := not_lt.mp hcon
    nlinarith
  have k23 : (k₃ : ℝ) < k₂ := by
    by_contra hcon
    have := not_lt.mp hcon
    nlinarith
  have k12' : k₂ + 1 ≤ k₁ := by exact_mod_cast k12
  have k23' : k₃ + 1 ≤ k₂ := by exact_mod_cast k23
  have k13 : (k₃ : ℝ) + 2 ≤ k₁ := by
    have : k₃ + 2 ≤ k₁ := by omega
    exact_mod_cast this
  nlinarith

/-! ## Transfer of harmonic measure -/

private lemma cay_poissonKernelUHP_eq_cauchy (z : ℂ) (hz : 0 < z.im) (t : ℝ) :
    poissonKernelUHP z t = ProbabilityTheory.cauchyPDFReal z.re z.im.toNNReal t := by
  rw [ProbabilityTheory.cauchyPDFReal_def, poissonKernelUHP, Real.coe_toNNReal _ hz.le]
  rw [div_eq_mul_inv, mul_inv]
  ring

theorem integrable_poissonKernelUHP (z : ℂ) (hz : 0 < z.im) :
    Integrable (fun t : ℝ => poissonKernelUHP z t) :=
  (ProbabilityTheory.integrable_cauchyPDFReal z.re (γ := z.im.toNNReal)).congr
    (Filter.Eventually.of_forall fun t => (cay_poissonKernelUHP_eq_cauchy z hz t).symm)

theorem integral_poissonKernelUHP (z : ℂ) (hz : 0 < z.im) :
    ∫ t : ℝ, poissonKernelUHP z t = 1 := by
  have hγ : z.im.toNNReal ≠ 0 := (Real.toNNReal_pos.mpr hz).ne'
  simp_rw [cay_poissonKernelUHP_eq_cauchy z hz]
  exact ProbabilityTheory.integral_cauchyPDFReal_eq_one z.re hγ

/-- The pointwise form of the transfer of harmonic measure:
`P_{γ z}(γ t) · (2/(1 + t²)) / 2π = P_z(t)`. -/
private lemma cay_poisson_transfer (z : ℂ) (hz : 0 < z.im) (t : ℝ) :
    (2 * π)⁻¹ * (2 / (1 + t ^ 2)) * poissonKernelDisk (cayley z) (cayley (t : ℂ)) =
      poissonKernelUHP z t := by
  have hzI := cay_add_I_ne_zero_of_im_pos hz
  have htI := cay_ofReal_add_I_ne_zero t
  have hdiff : cayley z - cayley (t : ℂ) =
      2 * Complex.I * (z - t) / ((z + Complex.I) * ((t : ℂ) + Complex.I)) := by
    unfold cayley; field_simp; ring
  have hab : Complex.normSq (z - Complex.I) = Complex.normSq (z + Complex.I) - 4 * z.im := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im]
    ring
  have hc : Complex.normSq ((t : ℂ) + Complex.I) = 1 + t ^ 2 := by
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hd : Complex.normSq (z - t) = (t - z.re) ^ 2 + z.im ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have h4 : Complex.normSq (2 * Complex.I * (z - t)) = 4 * Complex.normSq (z - t) := by
    rw [map_mul, map_mul, Complex.normSq_I, Complex.normSq_ofNat]
    norm_num
  have ha0 : 0 < Complex.normSq (z + Complex.I) := Complex.normSq_pos.mpr hzI
  have hd0 : 0 < (t - z.re) ^ 2 + z.im ^ 2 := by nlinarith [sq_nonneg (t - z.re)]
  have hc0 : 0 < 1 + t ^ 2 := by positivity
  unfold poissonKernelDisk poissonKernelUHP
  rw [Complex.sq_norm, Complex.sq_norm, hdiff, cayley, map_div₀, map_div₀, h4, map_mul, hd,
    hc, hab]
  field_simp
  ring

/-- **Harmonic measure under the Cayley transform.**  For `z ∈ 𝕌` and a
continuous `F` on `S¹`, the average of `F` against the harmonic measure of `Δ`
at `γ(z)` is the average of `F ∘ γ` against the harmonic measure `P_z(t) dt` of
`𝕌` at `z`.  (At `z = i` this is Step 1b of the forward inequality,
`dt/(π(1 + t²)) = dφ/2π`.) -/
theorem harmonicMeasureAvg_cayley (z : ℂ) (hz : 0 < z.im) (F : Circle → ℂ)
    (_hF : Continuous F) :
    harmonicMeasureAvg (cayley z) F =
      ∫ t : ℝ, F (cayleyCircle t) * (poissonKernelUHP z t : ℂ) := by
  have hπ := Real.pi_pos
  -- the substitution `θ = 2 arctan t + π`, a diffeomorphism `ℝ → (0, 2π)`
  have himage : (fun t : ℝ => 2 * arctan t + π) '' univ = Ioo 0 (2 * π) := by
    ext θ
    simp only [mem_image, mem_univ, true_and, mem_Ioo]
    constructor
    · rintro ⟨t, rfl⟩
      have := arctan_lt_pi_div_two t
      have := neg_pi_div_two_lt_arctan t
      constructor <;> linarith
    · rintro ⟨h1, h2⟩
      refine ⟨tan ((θ - π) / 2), ?_⟩
      rw [arctan_tan (by linarith) (by linarith)]
      ring
  have hderiv : ∀ t ∈ (univ : Set ℝ), HasDerivWithinAt (fun t : ℝ => 2 * arctan t + π)
      (2 * (1 / (1 + t ^ 2))) univ t :=
    fun t _ => (((hasDerivAt_arctan t).const_mul 2).add_const π).hasDerivWithinAt
  have hinj : InjOn (fun t : ℝ => 2 * arctan t + π) univ := by
    intro a _ b _ hab
    have : arctan a = arctan b := by simp only at hab; linarith
    exact arctan_strictMono.injective this
  have hcov := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj
    (fun θ : ℝ => F (Circle.exp θ) * (poissonKernelDisk (cayley z) (Circle.exp θ) : ℂ))
  rw [himage, Measure.restrict_univ] at hcov
  rw [harmonicMeasureAvg, intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo, hcov, ← integral_const_mul]
  congr 1
  funext t
  have hexp : Circle.exp (2 * arctan t + π) = cayleyCircle t := by
    rw [cayleyCircle, show 2 * arctan t + π = (2 * arctan t - π) + 2 * π by ring,
      Circle.exp_add_two_pi]
  have hpos : (0 : ℝ) < 2 * (1 / (1 + t ^ 2)) := by positivity
  rw [hexp, cayleyCircle_coe, abs_of_pos hpos, Complex.real_smul,
    ← cay_poisson_transfer z hz t]
  push_cast
  ring

end VanishingCarleson

end
