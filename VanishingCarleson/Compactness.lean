/-
# Compactness of normalized quasisymmetric families (§3.2)

* `KFamily ρ` — the family `𝒦_ρ` of `ρ`-quasisymmetric increasing
  homeomorphisms `H` of `ℝ` with `H(-1) = 0`, `H(1) = 1` (and `H(∞) = ∞`,
  automatic for a homeomorphism of `ℝ`).
* `KImage ρ` — its Cayley conjugates `γ ∘ H ∘ γ⁻¹`, as a subset of
  `C(S¹, S¹)`.

**Lemma (Compactness)** is stated for uniform convergence on `ℝ̄` with the
spherical metric.  Under the Cayley transform `γ : ℝ̄ → S¹`, a bi-Lipschitz
homeomorphism for the chordal metric, this is uniform convergence of the
Cayley conjugates on `S¹`; so the lemma is `IsCompact (KImage ρ)` in `C(S¹, S¹)`
(`compact_KFamily`).  This is also the form in which it is used: the
functionals of Corollary (Compact functionals), Step 2 of the forward
inequality and the quasiconformality bound are all functions of the Cayley
conjugate, continuous for uniform convergence on `S¹` by the continuity of the
Douady–Earle extension in its boundary values (`DouadyEarleExt`).

The proof of `compact_KFamily` follows the paper: the halving/doubling
estimates (Step 1) give, uniformly on `𝒦_ρ`, bounds on compacta, a positive
lower bound for `H(y) - H(x)`, a modulus of continuity and escape to `±∞`
(Steps 2–4).  These make `KImage ρ` equicontinuous, and make the set of its
members closed for *pointwise* convergence (Step 5); the version
`ArzelaAscoli.isCompact_of_equicontinuous` of the Arzelà–Ascoli theorem then
concludes, the space `S¹ → S¹` being compact for pointwise convergence.
-/
import Mathlib
import VanishingCarleson.DouadyEarle

open MeasureTheory Real Set Filter Topology

noncomputable section

namespace VanishingCarleson

/-- The family `𝒦_ρ` of `ρ`-quasisymmetric increasing homeomorphisms of `ℝ`
normalized by `H(-1) = 0`, `H(1) = 1`. -/
def KFamily (ρ : ℝ) : Set (ℝ → ℝ) :=
  { H | Quasisymmetric H ρ ∧ H (-1) = 0 ∧ H 1 = 1 }

/-- `𝒦_ρ` is not empty: it contains `t ↦ (t + 1)/2`. -/
theorem affine_mem_KFamily (ρ : ℝ) (hρ : 1 ≤ ρ) : (fun t : ℝ => (t + 1) / 2) ∈ KFamily ρ := by
  refine ⟨⟨fun a b hab => by simp only; linarith, by fun_prop,
    fun y => ⟨2 * y - 1, by simp only; ring⟩, fun x t ht => ?_⟩, by norm_num, by norm_num⟩
  have h : t ≤ ρ * t := by nlinarith
  simp only
  constructor <;> linarith

/-- The Cayley conjugates `γ ∘ H ∘ γ⁻¹` of the members of `𝒦_ρ`. -/
def KImage (ρ : ℝ) : Set C(Circle, Circle) :=
  { g | ∃ H ∈ KFamily ρ, ⇑g = cayleyConj H }

/-- The Cayley conjugate of a member of `𝒦_ρ`, as an element of `C(S¹, S¹)`. -/
def kConj {ρ : ℝ} (H : ℝ → ℝ) (hH : H ∈ KFamily ρ) : C(Circle, Circle) :=
  ⟨cayleyConj H, continuous_cayleyConj hH.1.1 hH.1.2.1 hH.1.2.2.1⟩

theorem kConj_mem_KImage {ρ : ℝ} (H : ℝ → ℝ) (hH : H ∈ KFamily ρ) : kConj H hH ∈ KImage ρ :=
  ⟨H, hH, rfl⟩

/-- Members of `KImage ρ` are orientation-preserving homeomorphisms of `S¹`. -/
theorem KImage_spec {ρ : ℝ} {g : C(Circle, Circle)} (hg : g ∈ KImage ρ) :
    Function.Bijective g ∧ HasIncreasingLift g := by
  obtain ⟨H, hH, hgH⟩ := hg
  rw [hgH]
  exact ⟨bijective_cayleyConj hH.1.1 hH.1.2.1 hH.1.2.2.1,
    hasIncreasingLift_cayleyConj hH.1.1 hH.1.2.1 hH.1.2.2.1⟩

/-! ## Step 1: halving and doubling -/

section Doubling

variable {H : ℝ → ℝ} {ρ : ℝ}

private lemma kc_right_upper_step (hH : Quasisymmetric H ρ) (a s : ℝ) (hs : 0 < s) :
    (1 + ρ) * (H (a + s) - H a) ≤ ρ * (H (a + 2 * s) - H a) := by
  have h := (hH.2.2.2 (a + s) s hs).2
  have e : a + s + s = a + 2 * s := by ring
  rw [add_sub_cancel_right, e] at h
  linarith

private lemma kc_right_lower_step (hH : Quasisymmetric H ρ) (a s : ℝ) (hs : 0 < s) :
    H (a + 2 * s) - H a ≤ (1 + ρ) * (H (a + s) - H a) := by
  have h := (hH.2.2.2 (a + s) s hs).1
  have e : a + s + s = a + 2 * s := by ring
  rw [add_sub_cancel_right, e] at h
  linarith

private lemma kc_left_upper_step (hH : Quasisymmetric H ρ) (b s : ℝ) (hs : 0 < s) :
    (1 + ρ) * (H b - H (b - s)) ≤ ρ * (H b - H (b - 2 * s)) := by
  have h := (hH.2.2.2 (b - s) s hs).1
  have e : b - s - s = b - 2 * s := by ring
  rw [sub_add_cancel, e] at h
  linarith

private lemma kc_left_lower_step (hH : Quasisymmetric H ρ) (b s : ℝ) (hs : 0 < s) :
    H b - H (b - 2 * s) ≤ (1 + ρ) * (H b - H (b - s)) := by
  have h := (hH.2.2.2 (b - s) s hs).2
  have e : b - s - s = b - 2 * s := by ring
  rw [sub_add_cancel, e] at h
  linarith

/-- Iterated halving, upper bound: `|H([a, a+s])| ≤ α^n |H([a, a+2^n s])|`. -/
private lemma kc_right_upper (hH : Quasisymmetric H ρ) (hρ : 0 ≤ ρ) (a : ℝ) (n : ℕ) :
    ∀ s : ℝ, 0 < s →
      (1 + ρ) ^ n * (H (a + s) - H a) ≤ ρ ^ n * (H (a + 2 ^ n * s) - H a) := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
    intro s hs
    have h1 := kc_right_upper_step hH a s hs
    have h2 := ih (2 * s) (by positivity)
    have e : (2 : ℝ) ^ n * (2 * s) = 2 ^ (n + 1) * s := by ring
    rw [e] at h2
    have hp : (0 : ℝ) ≤ (1 + ρ) ^ n := pow_nonneg (by linarith) n
    calc (1 + ρ) ^ (n + 1) * (H (a + s) - H a)
        = (1 + ρ) ^ n * ((1 + ρ) * (H (a + s) - H a)) := by ring
      _ ≤ (1 + ρ) ^ n * (ρ * (H (a + 2 * s) - H a)) := mul_le_mul_of_nonneg_left h1 hp
      _ = ρ * ((1 + ρ) ^ n * (H (a + 2 * s) - H a)) := by ring
      _ ≤ ρ * (ρ ^ n * (H (a + 2 ^ (n + 1) * s) - H a)) := mul_le_mul_of_nonneg_left h2 hρ
      _ = ρ ^ (n + 1) * (H (a + 2 ^ (n + 1) * s) - H a) := by ring

/-- Iterated doubling, upper bound: `|H([a, a+2^n s])| ≤ (1+ρ)^n |H([a, a+s])|`. -/
private lemma kc_right_lower (hH : Quasisymmetric H ρ) (hρ : 0 ≤ ρ) (a : ℝ) (n : ℕ) :
    ∀ s : ℝ, 0 < s → H (a + 2 ^ n * s) - H a ≤ (1 + ρ) ^ n * (H (a + s) - H a) := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
    intro s hs
    have h1 := kc_right_lower_step hH a s hs
    have h2 := ih (2 * s) (by positivity)
    have e : (2 : ℝ) ^ n * (2 * s) = 2 ^ (n + 1) * s := by ring
    rw [e] at h2
    have hp : (0 : ℝ) ≤ (1 + ρ) ^ n := pow_nonneg (by linarith) n
    calc H (a + 2 ^ (n + 1) * s) - H a ≤ (1 + ρ) ^ n * (H (a + 2 * s) - H a) := h2
      _ ≤ (1 + ρ) ^ n * ((1 + ρ) * (H (a + s) - H a)) := mul_le_mul_of_nonneg_left h1 hp
      _ = (1 + ρ) ^ (n + 1) * (H (a + s) - H a) := by ring

/-- Iterated halving on the left: `|H([b-s, b])| ≤ α^n |H([b-2^n s, b])|`. -/
private lemma kc_left_upper (hH : Quasisymmetric H ρ) (hρ : 0 ≤ ρ) (b : ℝ) (n : ℕ) :
    ∀ s : ℝ, 0 < s →
      (1 + ρ) ^ n * (H b - H (b - s)) ≤ ρ ^ n * (H b - H (b - 2 ^ n * s)) := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
    intro s hs
    have h1 := kc_left_upper_step hH b s hs
    have h2 := ih (2 * s) (by positivity)
    have e : (2 : ℝ) ^ n * (2 * s) = 2 ^ (n + 1) * s := by ring
    rw [e] at h2
    have hp : (0 : ℝ) ≤ (1 + ρ) ^ n := pow_nonneg (by linarith) n
    calc (1 + ρ) ^ (n + 1) * (H b - H (b - s))
        = (1 + ρ) ^ n * ((1 + ρ) * (H b - H (b - s))) := by ring
      _ ≤ (1 + ρ) ^ n * (ρ * (H b - H (b - 2 * s))) := mul_le_mul_of_nonneg_left h1 hp
      _ = ρ * ((1 + ρ) ^ n * (H b - H (b - 2 * s))) := by ring
      _ ≤ ρ * (ρ ^ n * (H b - H (b - 2 ^ (n + 1) * s))) := mul_le_mul_of_nonneg_left h2 hρ
      _ = ρ ^ (n + 1) * (H b - H (b - 2 ^ (n + 1) * s)) := by ring

/-- Iterated doubling on the left: `|H([b-2^n s, b])| ≤ (1+ρ)^n |H([b-s, b])|`. -/
private lemma kc_left_lower (hH : Quasisymmetric H ρ) (hρ : 0 ≤ ρ) (b : ℝ) (n : ℕ) :
    ∀ s : ℝ, 0 < s → H b - H (b - 2 ^ n * s) ≤ (1 + ρ) ^ n * (H b - H (b - s)) := by
  induction n with
  | zero => intro s _; simp
  | succ n ih =>
    intro s hs
    have h1 := kc_left_lower_step hH b s hs
    have h2 := ih (2 * s) (by positivity)
    have e : (2 : ℝ) ^ n * (2 * s) = 2 ^ (n + 1) * s := by ring
    rw [e] at h2
    have hp : (0 : ℝ) ≤ (1 + ρ) ^ n := pow_nonneg (by linarith) n
    calc H b - H (b - 2 ^ (n + 1) * s) ≤ (1 + ρ) ^ n * (H b - H (b - 2 * s)) := h2
      _ ≤ (1 + ρ) ^ n * ((1 + ρ) * (H b - H (b - s))) := mul_le_mul_of_nonneg_left h1 hp
      _ = (1 + ρ) ^ (n + 1) * (H b - H (b - s)) := by ring

end Doubling

/-! ## Steps 2–4: uniform estimates on `𝒦_ρ` -/

section Estimates

variable {H : ℝ → ℝ} {ρ : ℝ}

/-- Step 2, the base scale: `1 ≤ (1+ρ) H(0) ≤ ρ`. -/
private lemma kc_base (hH : H ∈ KFamily ρ) :
    1 ≤ (1 + ρ) * H 0 ∧ (1 + ρ) * H 0 ≤ ρ := by
  have h := hH.1.2.2.2 0 1 one_pos
  rw [zero_add, zero_sub, hH.2.1, hH.2.2] at h
  constructor <;> linarith [h.1, h.2]

private lemma kc_H0 (hH : H ∈ KFamily ρ) : 0 < H 0 ∧ H 0 < 1 := by
  have h1 := hH.1.1 (show (-1 : ℝ) < 0 by norm_num)
  have h2 := hH.1.1 (show (0 : ℝ) < 1 by norm_num)
  rw [hH.2.1] at h1
  rw [hH.2.2] at h2
  exact ⟨h1, h2⟩

/-- Upper bound at the dyadic points `2^n`. -/
private lemma kc_upper_pow (hρ : 1 ≤ ρ) (hH : H ∈ KFamily ρ) (n : ℕ) :
    H (2 ^ n) ≤ 1 + (1 + ρ) ^ n := by
  have h := kc_right_lower hH.1 (by linarith) 0 n 1 one_pos
  rw [zero_add, mul_one, zero_add, hH.2.2] at h
  obtain ⟨h0, h1⟩ := kc_H0 hH
  have hp : (0 : ℝ) ≤ (1 + ρ) ^ n := pow_nonneg (by linarith) n
  have := mul_le_mul_of_nonneg_left (show 1 - H 0 ≤ 1 by linarith) hp
  linarith

/-- Lower bound at the dyadic points `-2^n`. -/
private lemma kc_lower_pow (hρ : 1 ≤ ρ) (hH : H ∈ KFamily ρ) (n : ℕ) :
    -(1 + ρ) ^ n ≤ H (-2 ^ n) := by
  have h := kc_left_lower hH.1 (by linarith) 0 n 1 one_pos
  rw [zero_sub, mul_one, zero_sub, hH.2.1, sub_zero] at h
  obtain ⟨h0, h1⟩ := kc_H0 hH
  have hp : (0 : ℝ) ≤ (1 + ρ) ^ n := pow_nonneg (by linarith) n
  have := mul_le_mul_of_nonneg_left (show H 0 ≤ 1 by linarith) hp
  linarith

/-- Uniform bounds on compacta. -/
private lemma kc_bound (hρ : 1 ≤ ρ) (R : ℝ) :
    ∃ C : ℝ, ∀ H ∈ KFamily ρ, ∀ t : ℝ, |t| ≤ R → |H t| ≤ C := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt R (one_lt_two : (1 : ℝ) < 2)
  refine ⟨1 + (1 + ρ) ^ n, fun H hH t ht => ?_⟩
  have ht' := abs_le.mp ht
  have hu := hH.1.1.monotone (show t ≤ 2 ^ n by linarith)
  have hl := hH.1.1.monotone (show -2 ^ n ≤ t by linarith)
  have h1 := kc_upper_pow hρ hH n
  have h2 := kc_lower_pow hρ hH n
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Step 4, uniform escape to infinity. -/
private lemma kc_escape (hρ : 1 ≤ ρ) (M : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ H ∈ KFamily ρ, M ≤ H R ∧ H (-R) ≤ -M := by
  have hρp : 0 < ρ := by linarith
  have hq : 1 < (1 + ρ) / ρ := by rw [one_lt_div hρp]; linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 + ρ) * (|M| + 1)) hq
  rw [div_pow, lt_div_iff₀ (pow_pos hρp n)] at hn
  have hP : 0 < (1 + ρ) * ρ ^ n := mul_pos (by linarith) (pow_pos hρp n)
  have hMabs := le_abs_self M
  have hMabs' := neg_abs_le M
  refine ⟨2 ^ n, by positivity, fun H hH => ⟨?_, ?_⟩⟩
  · have h := kc_right_upper hH.1 hρp.le 0 n 1 one_pos
    rw [zero_add, mul_one, zero_add, hH.2.2] at h
    obtain ⟨hb1, hb2⟩ := kc_base hH
    obtain ⟨h0, -⟩ := kc_H0 hH
    -- `(1+ρ)^n ≤ (1+ρ) ρ^n (H(2^n) - H 0)`
    have h3 : (1 + ρ) ^ n ≤ (1 + ρ) * ρ ^ n * (H (2 ^ n) - H 0) := by
      have h4 : (1 + ρ) ^ n * 1 ≤ (1 + ρ) ^ n * ((1 + ρ) * (1 - H 0)) :=
        mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) n)
      have h5 := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 1 + ρ by linarith)
      nlinarith
    have h6 : (1 + ρ) * ρ ^ n * (|M| + 1) < (1 + ρ) * ρ ^ n * H (2 ^ n) := by
      have : (1 + ρ) * ρ ^ n * H 0 > 0 := mul_pos hP h0
      nlinarith
    have := lt_of_mul_lt_mul_left h6 hP.le
    linarith
  · have h := kc_left_upper hH.1 hρp.le 0 n 1 one_pos
    rw [zero_sub, mul_one, zero_sub, hH.2.1, sub_zero] at h
    obtain ⟨hb1, hb2⟩ := kc_base hH
    obtain ⟨-, h1⟩ := kc_H0 hH
    have h3 : (1 + ρ) ^ n ≤ (1 + ρ) * ρ ^ n * (H 0 - H (-2 ^ n)) := by
      have h4 : (1 + ρ) ^ n * 1 ≤ (1 + ρ) ^ n * ((1 + ρ) * H 0) :=
        mul_le_mul_of_nonneg_left hb1 (pow_nonneg (by linarith) n)
      have h5 := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 1 + ρ by linarith)
      nlinarith
    have h6 : (1 + ρ) * ρ ^ n * (|M| + 1) < (1 + ρ) * ρ ^ n * (1 - H (-2 ^ n)) := by
      have : (1 + ρ) * ρ ^ n * (1 - H 0) > 0 := mul_pos hP (by linarith)
      nlinarith
    have := lt_of_mul_lt_mul_left h6 hP.le
    linarith

/-- Step 5, the uniform lower bound: `H(y) - H(x) ≥ δ(x, y) > 0` on `𝒦_ρ`. -/
private lemma kc_gap (hρ : 1 ≤ ρ) {x y : ℝ} (hxy : x < y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H ∈ KFamily ρ, δ ≤ H y - H x := by
  set d := y - x with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((y + 1) / d) (one_lt_two : (1 : ℝ) < 2)
  rw [div_lt_iff₀ hd0] at hn
  set a := y - 2 ^ n * d with ha
  have hs : 0 < (2 : ℝ) ^ n * d := by positivity
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((1 - a) / (2 ^ n * d)) (one_lt_two : (1 : ℝ) < 2)
  rw [div_lt_iff₀ hs] at hm
  have hP : 0 < (1 + ρ) ^ m * (1 + ρ) ^ n := by
    have : 0 < 1 + ρ := by linarith
    positivity
  refine ⟨1 / ((1 + ρ) ^ m * (1 + ρ) ^ n), by positivity, fun H hH => ?_⟩
  have h1 := kc_left_lower hH.1 (by linarith) y n d hd0
  have hyx : y - d = x := by rw [hd]; ring
  rw [hyx] at h1
  have h2 := kc_right_lower hH.1 (by linarith) a m (2 ^ n * d) hs
  have hay : a + 2 ^ n * d = y := by rw [ha]; ring
  rw [hay] at h2
  have htop := hH.1.1.monotone (show (1 : ℝ) ≤ a + 2 ^ m * (2 ^ n * d) by linarith)
  have hbot := hH.1.1.monotone (show a ≤ -1 by rw [ha]; linarith)
  rw [hH.2.2] at htop
  rw [hH.2.1] at hbot
  have h3 := mul_le_mul_of_nonneg_left h1 (pow_nonneg (show (0 : ℝ) ≤ 1 + ρ by linarith) m)
  rw [div_le_iff₀ hP]
  nlinarith

/-- Step 3, a uniform modulus of continuity on compacta. -/
private lemma kc_modulus (hρ : 1 ≤ ρ) (R ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ H ∈ KFamily ρ, ∀ x y : ℝ, |x| ≤ R → |y| ≤ R → |x - y| < δ →
      |H x - H y| < ε := by
  have hρp : 0 < ρ := by linarith
  set R' := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hRR' : R ≤ R' := le_max_left _ _
  obtain ⟨C, hC⟩ := kc_bound hρ (2 * R')
  have hC0 : 0 ≤ C := by
    have := hC _ (affine_mem_KFamily ρ hρ) 0 (by rw [abs_zero]; linarith)
    exact (abs_nonneg _).trans this
  have hq0 : 0 ≤ ρ / (1 + ρ) := by positivity
  have hq1 : ρ / (1 + ρ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (2 * C + 1) by positivity) hq1
  set δ := R' / 2 ^ n with hδ
  have hδ0 : 0 < δ := by positivity
  have h2δ : 2 ^ n * δ = R' := by rw [hδ]; field_simp
  -- the one-sided estimate
  have key : ∀ H ∈ KFamily ρ, ∀ x y : ℝ, |x| ≤ R' → x ≤ y → y - x < δ → H y - H x < ε := by
    intro H hH x y hx hxy hyx
    have h := kc_right_upper hH.1 hρp.le x n δ hδ0
    rw [h2δ] at h
    have hmono := hH.1.1.monotone (show y ≤ x + δ by linarith)
    have hx' := abs_le.mp hx
    have hb1 := abs_le.mp (hC H hH (x + R') (by rw [abs_le]; constructor <;> linarith))
    have hb2 := abs_le.mp (hC H hH x (by linarith))
    have hdiff : H (x + R') - H x ≤ 2 * C := by linarith [hb1.2, hb2.1]
    have hpos : 0 < (1 + ρ) ^ n := pow_pos (by linarith) n
    have h3 : H (x + δ) - H x ≤ (ρ / (1 + ρ)) ^ n * (2 * C) := by
      rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ hpos]
      have := mul_le_mul_of_nonneg_left hdiff (pow_nonneg hρp.le n)
      linarith
    have h4 : (ρ / (1 + ρ)) ^ n * (2 * C) ≤ (ρ / (1 + ρ)) ^ n * (2 * C + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hq0 n)
    have h5 : (ρ / (1 + ρ)) ^ n * (2 * C + 1) < ε := by
      rwa [lt_div_iff₀ (by linarith)] at hn
    linarith
  refine ⟨min δ 1, lt_min hδ0 one_pos, fun H hH x y hx hy hxy => ?_⟩
  have hxy' : |x - y| < δ := lt_of_lt_of_le hxy (min_le_left _ _)
  have hxy'' := abs_lt.mp hxy'
  rcases le_total x y with h | h
  · have := key H hH x y (hx.trans hRR') h (by linarith)
    have hm := hH.1.1.monotone h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · have := key H hH y x (hy.trans hRR') h (by linarith)
    have hm := hH.1.1.monotone h
    rw [abs_of_nonneg (by linarith)]
    exact this

end Estimates

/-! ## The Cayley transform on the real line -/

section CayleyReal

private lemma kc_dist_circle (a b : Circle) : dist a b = ‖(a : ℂ) - b‖ := by
  rw [← dist_eq_norm]; rfl

private lemma kc_ne_zero (u : ℝ) : (u : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this

private lemma kc_one_le_norm (u : ℝ) : 1 ≤ ‖(u : ℂ) + Complex.I‖ := by
  have := Complex.abs_im_le_norm ((u : ℂ) + Complex.I)
  simpa using this

private lemma kc_abs_le_norm (u : ℝ) : |u| ≤ ‖(u : ℂ) + Complex.I‖ := by
  have := Complex.abs_re_le_norm ((u : ℂ) + Complex.I)
  simpa using this

private lemma kc_norm_le (u : ℝ) : ‖(u : ℂ) + Complex.I‖ ≤ |u| + 1 := by
  have := norm_add_le (u : ℂ) Complex.I
  simpa [Complex.norm_real] using this

/-- `|γ(u) - 1| = 2 / |u + i|`. -/
private lemma kc_norm_sub_one (u : ℝ) :
    ‖((cayleyCircle u : Circle) : ℂ) - 1‖ = 2 / ‖(u : ℂ) + Complex.I‖ := by
  rw [cayleyCircle_coe]
  have hne := kc_ne_zero u
  have e : cayley (u : ℂ) - 1 = -2 * Complex.I / ((u : ℂ) + Complex.I) := by
    unfold cayley
    field_simp
    ring
  rw [e, norm_div]
  simp

/-- `γ` is `2`-Lipschitz on `ℝ`. -/
private lemma kc_norm_sub_le (u v : ℝ) :
    ‖((cayleyCircle u : Circle) : ℂ) - cayleyCircle v‖ ≤ 2 * |u - v| := by
  rw [cayleyCircle_coe, cayleyCircle_coe]
  have hu := kc_ne_zero u
  have hv := kc_ne_zero v
  have e : cayley (u : ℂ) - cayley (v : ℂ) =
      2 * Complex.I * ((u - v : ℝ) : ℂ) / (((u : ℂ) + Complex.I) * ((v : ℂ) + Complex.I)) := by
    unfold cayley
    push_cast
    field_simp
    ring
  rw [e, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 := kc_one_le_norm u
  have h2 := kc_one_le_norm v
  have hD : 1 ≤ ‖(u : ℂ) + Complex.I‖ * ‖(v : ℂ) + Complex.I‖ := by nlinarith
  simp only [Complex.norm_I, mul_one]
  rw [show ‖(2 : ℂ)‖ = 2 by simp]
  exact div_le_self (by positivity) hD

private lemma kc_continuousAt_cayleyInv {w : ℂ} (hw : w ≠ 1) : ContinuousAt cayleyInv w := by
  show ContinuousAt (fun ζ : ℂ => Complex.I * (1 + ζ) / (1 - ζ)) w
  exact (continuousAt_const.mul (continuousAt_const.add continuousAt_id)).div
    (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr hw.symm)

private lemma kc_continuous_coe : Continuous (fun ζ : Circle => (ζ : ℂ)) :=
  continuous_subtype_val

end CayleyReal

/-! ## Equicontinuity -/

private lemma kc_equicontinuous (ρ : ℝ) (hρ : 1 ≤ ρ) :
    Equicontinuous (fun g : KImage ρ => ⇑(g : C(Circle, Circle))) := by
  intro ζ₀
  refine Metric.equicontinuousAt_iff_right.mpr fun ε hε => ?_
  by_cases h1 : ζ₀ = 1
  · subst h1
    obtain ⟨R, hR, hesc⟩ := kc_escape hρ (2 / ε + 1)
    have hη : (0 : ℝ) < 2 / (R + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds (1 : Circle) hη] with ζ hζ
    rintro ⟨g, H, hH, hgH⟩
    show dist (g 1) (g ζ) < ε
    rw [hgH, cayleyConj_one]
    by_cases hζ1 : ζ = 1
    · rw [hζ1, cayleyConj_one, dist_self]; exact hε
    set t := (cayleyInv (ζ : ℂ)).re with ht_def
    have hζt : cayleyCircle t = ζ := cayleyCircle_cayleyInv_re ζ hζ1
    have ht : R < |t| := by
      have hd : ‖((cayleyCircle t : Circle) : ℂ) - 1‖ < 2 / (R + 1) := by
        rw [hζt, ← Circle.coe_one, ← kc_dist_circle]; exact hζ
      rw [kc_norm_sub_one] at hd
      have h1 := kc_norm_le t
      have h2 := kc_one_le_norm t
      rw [div_lt_div_iff_of_pos_left (by norm_num) (by linarith) (by linarith)] at hd
      linarith
    have hHt : 2 / ε + 1 ≤ |H t| := by
      rcases le_or_gt 0 t with h0 | h0
      · rw [abs_of_nonneg h0] at ht
        have h3 := (hesc H hH).1
        have h4 := hH.1.1.monotone ht.le
        exact le_trans (by linarith) (le_abs_self _)
      · rw [abs_of_neg h0] at ht
        have h3 := (hesc H hH).2
        have h4 := hH.1.1.monotone (show t ≤ -R by linarith)
        have h5 := neg_abs_le (H t)
        have h6 : 0 < 2 / ε + 1 := by positivity
        rw [abs_of_neg (by linarith)]
        linarith
    have e := cayleyConj_cayleyCircle H t
    rw [hζt] at e
    rw [e, dist_comm, kc_dist_circle, Circle.coe_one, kc_norm_sub_one]
    have h5 := kc_abs_le_norm (H t)
    have h6 : 0 < 2 / ε + 1 := by positivity
    rw [div_lt_iff₀ (by linarith)]
    have h7 : ε * (2 / ε + 1) = 2 + ε := by field_simp
    nlinarith
  · set t₀ := (cayleyInv (ζ₀ : ℂ)).re with ht₀
    have hζ₀ : cayleyCircle t₀ = ζ₀ := cayleyCircle_cayleyInv_re ζ₀ h1
    obtain ⟨δ, hδ, hmod⟩ := kc_modulus hρ (|t₀| + 1) (ε / 2) (by positivity)
    have hne : (ζ₀ : ℂ) ≠ 1 := by rw [Ne, Circle.coe_eq_one]; exact h1
    have hτ : ContinuousAt (fun ζ : Circle => (cayleyInv (ζ : ℂ)).re) ζ₀ :=
      Complex.continuous_re.continuousAt.comp
        ((kc_continuousAt_cayleyInv hne).comp kc_continuous_coe.continuousAt)
    have hev1 : ∀ᶠ ζ in 𝓝 ζ₀, ζ ≠ 1 := eventually_ne_nhds h1
    have hev2 : ∀ᶠ ζ in 𝓝 ζ₀, dist (cayleyInv ((ζ : Circle) : ℂ)).re t₀ < min δ 1 :=
      hτ (Metric.ball_mem_nhds _ (lt_min hδ one_pos))
    filter_upwards [hev1, hev2] with ζ hζ1 hζd
    rintro ⟨g, H, hH, hgH⟩
    show dist (g ζ₀) (g ζ) < ε
    set s := (cayleyInv (ζ : ℂ)).re with hs
    have e₀ := cayleyConj_cayleyCircle H t₀
    rw [hζ₀] at e₀
    have e := cayleyConj_cayleyCircle H s
    rw [cayleyCircle_cayleyInv_re ζ hζ1] at e
    rw [hgH, e₀, e, kc_dist_circle]
    rw [Real.dist_eq] at hζd
    have hsd : |s - t₀| < δ := lt_of_lt_of_le hζd (min_le_left _ _)
    have hs1 : |s - t₀| < 1 := lt_of_lt_of_le hζd (min_le_right _ _)
    have hsR : |s| ≤ |t₀| + 1 := by
      have := abs_sub_abs_le_abs_sub s t₀
      linarith
    have h := hmod H hH t₀ s (by linarith [abs_nonneg t₀]) hsR (by rwa [abs_sub_comm])
    have := kc_norm_sub_le (H t₀) (H s)
    linarith

/-! ## Closedness for pointwise convergence (Step 5) -/

/-- The members of `KImage ρ`, as functions. -/
private def kcFun (ρ : ℝ) : Set (Circle → Circle) :=
  { f | ∃ H ∈ KFamily ρ, f = cayleyConj H }

private lemma kc_image_eq (ρ : ℝ) : ContinuousMap.toFun '' KImage ρ = kcFun ρ := by
  ext f
  constructor
  · rintro ⟨g, ⟨H, hH, hgH⟩, rfl⟩
    exact ⟨H, hH, hgH⟩
  · rintro ⟨H, hH, rfl⟩
    exact ⟨kConj H hH, kConj_mem_KImage H hH, rfl⟩

/-- `f ↦ Re γ⁻¹(f(γ(t)))`, recovering `H(t)` from `γ ∘ H ∘ γ⁻¹`. -/
private def kcTau (t : ℝ) (f : Circle → Circle) : ℝ :=
  (cayleyInv ((f (cayleyCircle t) : Circle) : ℂ)).re

private lemma kcTau_cayleyConj (H : ℝ → ℝ) (t : ℝ) : kcTau t (cayleyConj H) = H t := by
  rw [kcTau, cayleyConj_cayleyCircle, cayleyInv_cayleyCircle]

private lemma kc_closure_mem {f : Circle → Circle} {T : Set (Circle → Circle)}
    (hf : f ∈ closure T) {ψ : (Circle → Circle) → ℝ} (hψ : ContinuousAt ψ f) {A : Set ℝ}
    (hA : IsClosed A) (h : ∀ g ∈ T, ψ g ∈ A) : ψ f ∈ A := by
  have := hψ.continuousWithinAt.mem_closure hf (fun g hg => h g hg)
  rwa [hA.closure_eq] at this

private lemma kc_isClosed (ρ : ℝ) (hρ : 1 ≤ ρ) : IsClosed (kcFun ρ) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  -- `f(1) = 1`
  have hf1 : f 1 = 1 := by
    have := map_mem_closure (continuous_apply 1) hf (t := {1})
      (by rintro g ⟨H, hH, rfl⟩; exact cayleyConj_one H)
    simpa using this
  -- `f(γ(t)) ∈ γ(ℝ)`
  have hval : ∀ t, ∃ s, f (cayleyCircle t) = cayleyCircle s := by
    intro t
    obtain ⟨C, hC⟩ := kc_bound hρ |t|
    have hK : IsCompact (cayleyCircle '' Icc (-C) C) :=
      isCompact_Icc.image continuous_cayleyCircle
    have := map_mem_closure (continuous_apply (cayleyCircle t)) hf
      (t := cayleyCircle '' Icc (-C) C) (by
        rintro g ⟨H, hH, rfl⟩
        exact ⟨H t, abs_le.mp (hC H hH t le_rfl), (cayleyConj_cayleyCircle H t).symm⟩)
    rw [hK.isClosed.closure_eq] at this
    obtain ⟨s, -, hs⟩ := this
    exact ⟨s, hs.symm⟩
  set H : ℝ → ℝ := fun t => kcTau t f with hHdef
  have hfH : ∀ t, f (cayleyCircle t) = cayleyCircle (H t) := by
    intro t
    obtain ⟨s, hs⟩ := hval t
    simp only [hHdef, kcTau, hs, cayleyInv_cayleyCircle]
  have hcont : ∀ t, ContinuousAt (kcTau t) f := by
    intro t
    have hne : ((f (cayleyCircle t) : Circle) : ℂ) ≠ 1 := by
      rw [hfH t, Ne, Circle.coe_eq_one]; exact cayleyCircle_ne_one _
    have hin : Continuous (fun φ : Circle → Circle => ((φ (cayleyCircle t) : Circle) : ℂ)) :=
      kc_continuous_coe.comp (continuous_apply _)
    exact Complex.continuous_re.continuousAt.comp
      ((kc_continuousAt_cayleyInv hne).comp (f := fun φ : Circle → Circle =>
        ((φ (cayleyCircle t) : Circle) : ℂ)) hin.continuousAt)
  -- transfer of closed conditions
  have T1 : ∀ (x : ℝ) (A : Set ℝ), IsClosed A → (∀ H' ∈ KFamily ρ, H' x ∈ A) → H x ∈ A := by
    intro x A hA h
    refine kc_closure_mem hf (hcont x) hA ?_
    rintro g ⟨H', hH', rfl⟩
    rw [kcTau_cayleyConj]; exact h H' hH'
  have T2 : ∀ (x y : ℝ) (A : Set ℝ), IsClosed A →
      (∀ H' ∈ KFamily ρ, H' y - H' x ∈ A) → H y - H x ∈ A := by
    intro x y A hA h
    refine kc_closure_mem (ψ := fun φ => kcTau y φ - kcTau x φ) hf
      ((hcont y).sub (hcont x)) hA ?_
    rintro g ⟨H', hH', rfl⟩
    simp only [kcTau_cayleyConj]; exact h H' hH'
  have T4 : ∀ (a b d e c : ℝ) (A : Set ℝ), IsClosed A →
      (∀ H' ∈ KFamily ρ, H' a - H' b - c * (H' d - H' e) ∈ A) →
        H a - H b - c * (H d - H e) ∈ A := by
    intro a b d e c A hA h
    refine kc_closure_mem (ψ := fun φ => kcTau a φ - kcTau b φ - c * (kcTau d φ - kcTau e φ)) hf
      (((hcont a).sub (hcont b)).sub (continuousAt_const.mul ((hcont d).sub (hcont e)))) hA ?_
    rintro g ⟨H', hH', rfl⟩
    simp only [kcTau_cayleyConj]; exact h H' hH'
  -- the normalization
  have hHm1 : H (-1) = 0 := T1 (-1) {0} isClosed_singleton fun H' hH' => hH'.2.1
  have hH1 : H 1 = 1 := T1 1 {1} isClosed_singleton fun H' hH' => hH'.2.2
  -- the `M`-condition
  have hM : ∀ x t : ℝ, 0 < t →
      H (x + t) - H x ≤ ρ * (H x - H (x - t)) ∧ H x - H (x - t) ≤ ρ * (H (x + t) - H x) := by
    intro x t ht
    have h1 := T4 (x + t) x x (x - t) ρ (Iic 0) isClosed_Iic fun H' hH' => by
      have := (hH'.1.2.2.2 x t ht).1
      simp only [mem_Iic]; linarith
    have h2 := T4 x (x - t) (x + t) x ρ (Iic 0) isClosed_Iic fun H' hH' => by
      have := (hH'.1.2.2.2 x t ht).2
      simp only [mem_Iic]; linarith
    simp only [mem_Iic] at h1 h2
    constructor <;> linarith
  -- strict monotonicity
  have hmono : StrictMono H := by
    intro x y hxy
    obtain ⟨δ, hδ, hgap⟩ := kc_gap hρ hxy
    have := T2 x y (Ici δ) isClosed_Ici fun H' hH' => hgap H' hH'
    simp only [mem_Ici] at this
    linarith
  -- continuity
  have hHc : Continuous H := by
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨δ, hδ, hmod⟩ := kc_modulus hρ (|b| + 1) (ε / 2) (by positivity)
    refine ⟨min δ 1, lt_min hδ one_pos, fun a hab => ?_⟩
    rw [Real.dist_eq] at hab ⊢
    have hab1 : |a - b| < δ := lt_of_lt_of_le hab (min_le_left _ _)
    have hab2 : |a - b| < 1 := lt_of_lt_of_le hab (min_le_right _ _)
    have haR : |a| ≤ |b| + 1 := by
      have := abs_sub_abs_le_abs_sub a b
      linarith
    have := T2 b a (Icc (-(ε / 2)) (ε / 2)) isClosed_Icc fun H' hH' => by
      have := hmod H' hH' a b haR (by linarith [abs_nonneg b]) hab1
      exact abs_le.mp this.le
    rw [mem_Icc, ← abs_le] at this
    linarith
  -- surjectivity
  have hsurj : Function.Surjective H := by
    intro y
    obtain ⟨R, -, hesc⟩ := kc_escape hρ |y|
    have hR := T1 R (Ici |y|) isClosed_Ici fun H' hH' => (hesc H' hH').1
    have hR' := T1 (-R) (Iic (-|y|)) isClosed_Iic fun H' hH' => (hesc H' hH').2
    simp only [mem_Ici, mem_Iic] at hR hR'
    exact intermediate_value_univ (-R) R hHc
      ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  refine ⟨H, ⟨⟨hmono, hHc, hsurj, hM⟩, hHm1, hH1⟩, funext fun ζ => ?_⟩
  by_cases hζ : ζ = 1
  · rw [hζ, hf1, cayleyConj_one]
  · rw [← cayleyCircle_cayleyInv_re ζ hζ, hfH, cayleyConj_cayleyCircle]

/-- **Lemma (Compactness)**: `𝒦_ρ` is compact for uniform convergence on `ℝ̄`
with the spherical metric, i.e. its Cayley conjugates form a compact subset of
`C(S¹, S¹)`. -/
theorem compact_KFamily (ρ : ℝ) (hρ : 1 ≤ ρ) : IsCompact (KImage ρ) := by
  refine ArzelaAscoli.isCompact_of_equicontinuous (KImage ρ) ?_ ?_
  · rw [kc_image_eq]
    exact (kc_isClosed ρ hρ).isCompact
  · exact kc_equicontinuous ρ hρ

/-- **Lemma (Continuity of the extension at the origin)**: `g ↦ e(g)(0)` is
continuous for uniform convergence on the homeomorphisms of `S¹`. -/
theorem de_continuous_at_origin :
    ContinuousOn (fun g : C(Circle, Circle) => extension g 0)
      { g : C(Circle, Circle) | Function.Bijective g } := by
  intro φ₀ hφ₀
  obtain ⟨V, G, hV, hmem, hG, hEq⟩ := extension_continuousOn_pair 0 (by simp) φ₀ hφ₀
  have hi : Continuous (fun g : C(Circle, Circle) => ((0 : ℂ), g)) :=
    continuous_const.prodMk continuous_id
  have hU : (fun g : C(Circle, Circle) => ((0 : ℂ), g)) ⁻¹' V ∈ 𝓝 φ₀ :=
    hi.continuousAt.preimage_mem_nhds (hV.mem_nhds hmem)
  have hGc : ContinuousAt (fun g : C(Circle, Circle) => G ((0 : ℂ), g)) φ₀ :=
    ContinuousAt.comp (f := fun g : C(Circle, Circle) => ((0 : ℂ), g))
      (hG.continuousAt (hV.mem_nhds hmem)) hi.continuousAt
  refine hGc.continuousWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with g hgV hgb
    exact hEq _ hgV hgb (by simp)
  · exact hEq _ hmem hφ₀ (by simp)

/-- The value of the extension at `i`: `e(H)(i) = γ⁻¹(E(g_H)(0))`. -/
theorem douadyEarle_I_eq {ρ : ℝ} (H : ℝ → ℝ) (hH : H ∈ KFamily ρ) :
    douadyEarle H Complex.I = cayleyInv (extension (kConj H hH) 0) := by
  rw [douadyEarle_eq_cayley H hH.1.1 hH.1.2.1 hH.1.2.2.1 Complex.I (by simp), cayley_I]
  rfl

/-- **Corollary (Compact functionals)**: any functional `Φ(H) = φ(e(H)(i))`
with `φ` continuous attains a finite maximum and minimum on `𝒦_ρ`. -/
theorem compact_functionals (ρ : ℝ) (hρ : 1 ≤ ρ) (φ : ℂ → ℝ) (hφ : Continuous φ) :
    ∃ H₁ ∈ KFamily ρ, ∃ H₂ ∈ KFamily ρ, ∀ H ∈ KFamily ρ,
      φ (douadyEarle H Complex.I) ≤ φ (douadyEarle H₁ Complex.I) ∧
      φ (douadyEarle H₂ Complex.I) ≤ φ (douadyEarle H Complex.I) := by
  set Φ : C(Circle, Circle) → ℝ := fun g => φ (cayleyInv (extension g 0)) with hΦ
  have hcont : ContinuousOn Φ (KImage ρ) := by
    intro g hg
    have hbij := (KImage_spec hg).1
    have hin : ‖extension g 0‖ < 1 := extension_mem_disk g hbij g.continuous 0 (by simp)
    have hne : extension g 0 ≠ 1 := by
      intro h
      rw [h, norm_one] at hin
      exact lt_irrefl _ hin
    have h1 : ContinuousWithinAt (fun g : C(Circle, Circle) => extension g 0) (KImage ρ) g :=
      (de_continuous_at_origin g hbij).mono fun g' hg' => (KImage_spec hg').1
    have h2 : ContinuousWithinAt (fun g : C(Circle, Circle) => cayleyInv (extension g 0))
        (KImage ρ) g :=
      ContinuousAt.comp_continuousWithinAt (f := fun g : C(Circle, Circle) => extension g 0)
        (kc_continuousAt_cayleyInv hne) h1
    exact ContinuousAt.comp_continuousWithinAt
      (f := fun g : C(Circle, Circle) => cayleyInv (extension g 0)) hφ.continuousAt h2
  have hne : (KImage ρ).Nonempty := ⟨_, kConj_mem_KImage _ (affine_mem_KFamily ρ hρ)⟩
  obtain ⟨g₁, ⟨H₁, hH₁, hg₁H⟩, hmax⟩ := (compact_KFamily ρ hρ).exists_isMaxOn hne hcont
  obtain ⟨g₂, ⟨H₂, hH₂, hg₂H⟩, hmin⟩ := (compact_KFamily ρ hρ).exists_isMinOn hne hcont
  have key : ∀ H (hH : H ∈ KFamily ρ), φ (douadyEarle H Complex.I) = Φ (kConj H hH) :=
    fun H hH => by rw [douadyEarle_I_eq H hH]
  have e₁ : kConj H₁ hH₁ = g₁ := ContinuousMap.ext fun ζ => (congrFun hg₁H ζ).symm
  have e₂ : kConj H₂ hH₂ = g₂ := ContinuousMap.ext fun ζ => (congrFun hg₂H ζ).symm
  refine ⟨H₁, hH₁, H₂, hH₂, fun H hH => ⟨?_, ?_⟩⟩
  · rw [key H hH, key H₁ hH₁, e₁]
    exact hmax (kConj_mem_KImage H hH)
  · rw [key H hH, key H₂ hH₂, e₂]
    exact hmin (kConj_mem_KImage H hH)

end VanishingCarleson

end
