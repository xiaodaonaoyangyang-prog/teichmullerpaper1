/-
# Basic definitions

Formalization support for "Vanishing Carleson Measures for the Douady–Earle
Extension of Strongly Symmetric Homeomorphisms of the Real Line".

This file collects the basic vocabulary of the paper (Section 2, Notation and
Preliminaries):

* interval averages, BMO / VMO and the local BMO modulus;
* Muckenhoupt `A_∞`-weights (forms (A1) and (A2));
* Carleson boxes, the `T²`-norm and (vanishing) Carleson measures of the
  form `F(x,y)² dx dy / y`;
* the Poisson kernel of the upper half-plane.

All analytic objects are defined on the whole real line / plane; as usual in
mathlib, integrals of non-integrable functions are `0`, so most definitions
compile without integrability side conditions. The Carleson predicates
`IsCarlesonFn` / `IsVanishingCarleson` are the exception: they are stated
through an `ℝ≥0∞`-valued box integral, for which divergence gives `∞` rather
than the junk value `0`.
-/
import Mathlib

open MeasureTheory Real Set
open scoped Interval ENNReal

noncomputable section

namespace VanishingCarleson

/-! ## Interval averages -/

/-- Average of `u` over the interval `[a, b]`, written `u_K` in the paper. -/
def intervalAvg (u : ℝ → ℝ) (a b : ℝ) : ℝ := (∫ t in a..b, u t) / (b - a)

/-- Mean oscillation of `u` over `[a, b]`. -/
def intervalOscillation (u : ℝ → ℝ) (a b : ℝ) : ℝ :=
  intervalAvg (fun t => |u t - intervalAvg u a b|) a b

/-! ## BMO and VMO (Section 2.2) -/

/-- BMO seminorm restricted to subintervals of `[a, b]`, `‖u‖_{BMO(K)}`. -/
def bmoSeminorm (u : ℝ → ℝ) (a b : ℝ) : ℝ :=
  sSup { r : ℝ | ∃ c d : ℝ, a ≤ c ∧ c < d ∧ d ≤ b ∧ r = intervalOscillation u c d }

/-- Global BMO seminorm on the real line. -/
def bmoNorm (u : ℝ → ℝ) : ℝ :=
  sSup { r : ℝ | ∃ a b : ℝ, a < b ∧ r = intervalOscillation u a b }

/-- The local BMO modulus `ω_u(r) := sup_{|K| ≤ r} ‖u‖_{BMO(K)}`. -/
def vmoModulus (u : ℝ → ℝ) (r : ℝ) : ℝ :=
  sSup { s : ℝ | ∃ a b : ℝ, a < b ∧ b - a ≤ r ∧ s = intervalOscillation u a b }

/-- Bounded mean oscillation on `ℝ`. -/
def BMO (u : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ a b : ℝ, a < b → intervalOscillation u a b ≤ C

/-- Vanishing mean oscillation on `ℝ` (Sarason): BMO together with
`ω_u(r) → 0` as `r → 0`. -/
def VMO (u : ℝ → ℝ) : Prop :=
  BMO u ∧ ∀ ε : ℝ, 0 < ε → ∃ r : ℝ, 0 < r ∧ vmoModulus u r ≤ ε

/-! ## `A_∞`-weights (Section 2.2) -/

/-- Arithmetic mean of the weight `w` over `[a, b]`, `(w)_K` in the paper. -/
def weightMean (w : ℝ → ℝ) (a b : ℝ) : ℝ := intervalAvg w a b

/-- Geometric mean of `w` over `[a, b]`, `m_K = e^{α_K}` with `α = log w`. -/
def weightGeomMean (w : ℝ → ℝ) (a b : ℝ) : ℝ :=
  Real.exp (intervalAvg (fun t => Real.log (w t)) a b)

/-- The `(A1)` condition with explicit constants `C₁ ≥ 1`, `σ ∈ (0, 1]`:
`w > 0` almost everywhere and `w(E) / w(K) ≤ C₁ (|E| / |K|)^σ` for every
interval `K` and `E ⊆ K`.

Positivity is required only almost everywhere: for `w = f'` with `f` locally
absolutely continuous, `f'` is only defined almost everywhere, and Lean's
`deriv f` is the junk value `0` wherever `f` is not differentiable, so an
everywhere-positivity clause would silently force `f` to be differentiable at
every point. -/
def WeightA1 (w : ℝ → ℝ) (C₁ σ : ℝ) : Prop :=
  (∀ᵐ t ∂volume, 0 < w t) ∧
  ∀ a b : ℝ, a < b → ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc a b →
    (∫ x in E, w x) / (∫ x in Set.Icc a b, w x) ≤
      C₁ * ((volume E).toReal / (b - a)) ^ σ

/-- The `(A1)` condition with positivity at *every* point. This is the form
used internally by the proof of `(A1) ⇒ (A2)` (`A1A2`); `WeightA1.exists_pos`
reduces the general case to it by changing `w` on a null set. -/
def WeightA1Pos (w : ℝ → ℝ) (C₁ σ : ℝ) : Prop :=
  (∀ t : ℝ, 0 < w t) ∧
  ∀ a b : ℝ, a < b → ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Icc a b →
    (∫ x in E, w x) / (∫ x in Set.Icc a b, w x) ≤
      C₁ * ((volume E).toReal / (b - a)) ^ σ

/-- An `(A1)` weight agrees almost everywhere with an `(A1)` weight that is
positive at every point, with the same constants. -/
theorem WeightA1.exists_pos {w : ℝ → ℝ} {C₁ σ : ℝ} (hw : WeightA1 w C₁ σ) :
    ∃ v : ℝ → ℝ, v =ᵐ[volume] w ∧ WeightA1Pos v C₁ σ := by
  classical
  refine ⟨fun t => if 0 < w t then w t else 1, ?_, ?_, ?_⟩
  · filter_upwards [hw.1] with t ht
    simp [ht]
  · intro t
    dsimp only
    split_ifs with ht
    · exact ht
    · exact one_pos
  · intro a b hab E hE hEsub
    have hvw : (fun t => if 0 < w t then w t else 1) =ᵐ[volume] w := by
      filter_upwards [hw.1] with t ht
      simp [ht]
    rw [integral_congr_ae (ae_restrict_of_ae hvw), integral_congr_ae (ae_restrict_of_ae hvw)]
    exact hw.2 a b hab E hE hEsub

/-- The Muckenhoupt class `A_∞(ℝ)`: condition (A1) for some constants. -/
def AInfinityWeight (w : ℝ → ℝ) : Prop :=
  ∃ C₁ σ : ℝ, 1 ≤ C₁ ∧ 0 < σ ∧ σ ≤ 1 ∧ WeightA1 w C₁ σ

/-- The `(A2)` condition with explicit constant: `(w)_K ≤ A₀ m_K` for every
interval `K`. -/
def WeightA2 (w : ℝ → ℝ) (A₀ : ℝ) : Prop :=
  ∀ a b : ℝ, a < b → weightMean w a b ≤ A₀ * weightGeomMean w a b

namespace A1A2

open Filter

/-- The contraction factor produced by the `A_∞` condition. -/
def kap (C₁ σ : ℝ) : ℝ := 1 - (1 / (2 * C₁)) ^ (1 / σ)

lemma base_pos {C₁ : ℝ} (hC₁ : 1 ≤ C₁) : 0 < 1 / (2 * C₁) := by positivity

lemma base_le_half {C₁ : ℝ} (hC₁ : 1 ≤ C₁) : 1 / (2 * C₁) ≤ 1 / 2 := by
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

lemma kap_lt_one {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁) (_hσ : 0 < σ) : kap C₁ σ < 1 := by
  have : (0:ℝ) < (1 / (2 * C₁)) ^ (1 / σ) := Real.rpow_pos_of_pos (base_pos hC₁) _
  simp only [kap]; linarith

lemma kap_nonneg {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1) : 0 ≤ kap C₁ σ := by
  have h1 : (1:ℝ) ≤ 1 / σ := by rw [le_div_iff₀ hσ]; linarith
  have h2 : (1 / (2 * C₁)) ^ (1 / σ) ≤ (1 / (2 * C₁)) ^ (1:ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge (base_pos hC₁) (le_trans (base_le_half hC₁) (by norm_num)) h1
  rw [Real.rpow_one] at h2
  have h3 : 1 / (2 * C₁) ≤ 1/2 := base_le_half hC₁
  simp only [kap]; linarith

/-- Rewriting a set integral over `Icc` as an interval integral. -/
lemma integral_Icc_eq_intervalIntegral (f : ℝ → ℝ) {a b : ℝ} (h : a ≤ b) :
    ∫ x in Icc a b, f x = ∫ x in a..b, f x := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le h]


/-- **Total length bound.**  If `J_1, …, J_n` are pairwise disjoint subintervals of `[α,β]` on
each of which the average of `w` is at most half the average of `w` over `[α,β]`, then their
total length is at most `kap C₁ σ · (β-α)`, with `kap C₁ σ < 1`.  This is the only place where
the `A_∞`-condition (A1) is used. -/
lemma length_bound {w : ℝ → ℝ} {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁) (hσ : 0 < σ)
    (hA1 : WeightA1Pos w C₁ σ) {α β : ℝ} (hab : α < β)
    (hint : IntervalIntegrable w volume α β)
    (s : Finset (ℝ × ℝ))
    (hsub : ∀ pq ∈ s, α ≤ pq.1 ∧ pq.1 ≤ pq.2 ∧ pq.2 ≤ β)
    (hdisj : (s : Set (ℝ × ℝ)).PairwiseDisjoint (fun pq => Ioo pq.1 pq.2))
    (hval : ∀ pq ∈ s, ∫ x in pq.1..pq.2, w x ≤ (weightMean w α β / 2) * (pq.2 - pq.1)) :
    ∑ pq ∈ s, (pq.2 - pq.1) ≤ kap C₁ σ * (β - α) := by
  obtain ⟨hpos, hineq⟩ := hA1
  have hba : (0:ℝ) < β - α := by linarith
  have hIcc : IntegrableOn w (Icc α β) volume :=
    (integrableOn_Icc_iff_integrableOn_Ioc).mpr hint.1
  set W : ℝ := ∫ x in α..β, w x with hWdef
  have hW : 0 < W := intervalIntegral.intervalIntegral_pos_of_pos_on hint
    (fun x _ => hpos x) hab
  have hWIcc : ∫ x in Icc α β, w x = W := integral_Icc_eq_intervalIntegral w hab.le
  have hA : weightMean w α β = W / (β - α) := rfl
  -- the union of the intervals
  set U : Set ℝ := ⋃ pq ∈ s, Ioo pq.1 pq.2 with hUdef
  have hUmeas : MeasurableSet U := by
    exact Finset.measurableSet_biUnion _ (fun pq _ => measurableSet_Ioo)
  have hUsub : U ⊆ Icc α β := by
    intro x hx
    simp only [hUdef, Set.mem_iUnion] at hx
    obtain ⟨pq, hpq, hx⟩ := hx
    obtain ⟨h1, h2, h3⟩ := hsub pq hpq
    exact ⟨le_trans h1 hx.1.le, le_trans hx.2.le h3⟩
  set T : ℝ := ∑ pq ∈ s, (pq.2 - pq.1) with hTdef
  have hTnn : 0 ≤ T := Finset.sum_nonneg (fun pq h => by linarith [(hsub pq h).2.1])
  have hvolU : volume U = ENNReal.ofReal T := by
    rw [hUdef, measure_biUnion_finset hdisj (fun pq _ => measurableSet_Ioo)]
    rw [hTdef, ENNReal.ofReal_sum_of_nonneg (fun pq h => by linarith [(hsub pq h).2.1])]
    exact Finset.sum_congr rfl (fun pq _ => Real.volume_Ioo)
  have hvolUne : volume U ≠ ⊤ := by rw [hvolU]; exact ENNReal.ofReal_ne_top
  have hTU : (volume U).toReal = T := by rw [hvolU, ENNReal.toReal_ofReal hTnn]
  -- the integral over the union
  have hintU : ∫ x in U, w x = ∑ pq ∈ s, ∫ x in pq.1..pq.2, w x := by
    rw [hUdef, MeasureTheory.integral_biUnion_finset _ (fun pq _ => measurableSet_Ioo) hdisj
      (fun pq h => hIcc.mono_set (by
        intro x hx
        obtain ⟨h1, h2, h3⟩ := hsub pq h
        exact ⟨le_trans h1 hx.1.le, le_trans hx.2.le h3⟩))]
    exact Finset.sum_congr rfl (fun pq h => by
      rw [intervalIntegral.integral_of_le (hsub pq h).2.1, integral_Ioc_eq_integral_Ioo])
  have hintU_le : ∫ x in U, w x ≤ (W / (β - α) / 2) * T := by
    rw [hintU, hTdef, Finset.mul_sum]
    exact Finset.sum_le_sum (fun pq h => by simpa [hA] using hval pq h)
  -- the complement
  set E : Set ℝ := Icc α β \ U with hEdef
  have hEmeas : MeasurableSet E := measurableSet_Icc.diff hUmeas
  have hintE : ∫ x in E, w x = W - ∫ x in U, w x := by
    rw [hEdef, MeasureTheory.setIntegral_sdiff hUmeas hIcc hUsub, hWIcc]
  have hvolE : (volume E).toReal = (β - α) - T := by
    rw [hEdef, measure_sdiff hUsub hUmeas.nullMeasurableSet hvolUne]
    rw [ENNReal.toReal_sub_of_le (measure_mono hUsub) (by simp [Real.volume_Icc])]
    rw [hTU, Real.volume_Icc, ENNReal.toReal_ofReal hba.le]
  have hTle : T ≤ β - α := by
    have := measure_mono (μ := volume) hUsub
    rw [hvolU, Real.volume_Icc] at this
    have := (ENNReal.ofReal_le_ofReal_iff hba.le).mp this
    exact this
  -- apply (A1)
  have key := hineq α β hab E hEmeas Set.sdiff_subset
  rw [hWIcc, hintE, hvolE] at key
  -- unwind
  have hhalf : ∫ x in U, w x ≤ W / 2 := by
    refine le_trans hintU_le ?_
    have hpos' : 0 < W / (β - α) / 2 := by positivity
    calc (W / (β - α) / 2) * T ≤ (W / (β - α) / 2) * (β - α) := by nlinarith
      _ = W / 2 := by field_simp
  have hlow : (1:ℝ) / 2 ≤ C₁ * (((β - α) - T) / (β - α)) ^ σ := by
    refine le_trans ?_ key
    rw [le_div_iff₀ hW]; linarith
  have hu0 : 0 ≤ ((β - α) - T) / (β - α) := by positivity
  have hC₁pos : (0:ℝ) < C₁ := by linarith
  have hstep : 1 / (2 * C₁) ≤ (((β - α) - T) / (β - α)) ^ σ := by
    rw [div_le_iff₀ (by positivity)] at *
    nlinarith [hlow]
  have hfin : (1 / (2 * C₁)) ^ (1 / σ) ≤ ((β - α) - T) / (β - α) := by
    rw [one_div σ]
    exact (Real.rpow_inv_le_iff_of_pos (by positivity) hu0 hσ).mpr hstep
  rw [le_div_iff₀ hba] at hfin
  simp only [kap]
  nlinarith [hfin]



/-! ### The rising sun lemma

Throughout this section `g : ℝ → ℝ` is continuous; it will be the "potential"
`g x = ℓ (x - α) - ∫_α^x w`, whose derivative is `ℓ - w`.  The *shade* is the set of points of
`[α,β]` from which `g` never rises again; `w ≥ ℓ` almost everywhere on the shade, and the
complement of the shade splits into intervals across which `g` takes equal values, i.e. on
which the average of `w` is exactly `ℓ`. -/

/-- The set of points of `[α,β]` from which the potential `g` never rises again. -/
def Shade (g : ℝ → ℝ) (α β : ℝ) : Set ℝ := {x | x ∈ Icc α β ∧ ∀ y ∈ Icc x β, g y ≤ g x}

lemma shade_subset {g : ℝ → ℝ} {α β : ℝ} : Shade g α β ⊆ Icc α β := fun _ hx => hx.1

lemma right_mem_shade {g : ℝ → ℝ} {α β : ℝ} (hab : α ≤ β) : β ∈ Shade g α β :=
  ⟨⟨hab, le_rfl⟩, fun y hy => by
    have : y = β := le_antisymm hy.2 hy.1
    simp [this]⟩

lemma isClosed_shade {g : ℝ → ℝ} (hg : Continuous g) (α β : ℝ) : IsClosed (Shade g α β) := by
  rw [← isSeqClosed_iff_isClosed]
  intro u x hu hux
  refine ⟨isClosed_Icc.mem_of_tendsto hux (.of_forall fun n => (hu n).1), ?_⟩
  intro y hy
  rcases eq_or_lt_of_le hy.1 with h | h
  · simp [← h]
  · have hev : ∀ᶠ n in atTop, g y ≤ g (u n) := by
      filter_upwards [hux.eventually_lt_const h] with n hn
      exact (hu n).2 y ⟨hn.le, hy.2⟩
    exact ge_of_tendsto ((hg.tendsto x).comp hux) hev

/-- **Rising sun lemma.**  If `b` lies in the shade and the whole open interval `(a,b)` is
sunlit, then `g a ≤ g b`. -/
lemma rising_sun {g : ℝ → ℝ} (hg : Continuous g) {α β a b : ℝ} (hαa : α ≤ a) (hab : a ≤ b)
    (hbβ : b ≤ β) (hb : b ∈ Shade g α β) (hgap : ∀ x ∈ Ioo a b, x ∉ Shade g α β) :
    g a ≤ g b := by
  have key : ∀ x ∈ Ioo a b, g x ≤ g b := by
    intro x hx
    obtain ⟨c, hc, hcmax⟩ := (isCompact_Icc (a := x) (b := b)).exists_isMaxOn
      ⟨x, ⟨le_rfl, hx.2.le⟩⟩ hg.continuousOn
    rcases eq_or_lt_of_le hc.2 with h | h
    · have := hcmax ⟨le_rfl, hx.2.le⟩
      simpa [h] using this
    · exfalso
      have hcIoo : c ∈ Ioo a b := ⟨lt_of_lt_of_le hx.1 hc.1, h⟩
      have hcnot := hgap c hcIoo
      have hcIcc : c ∈ Icc α β := ⟨le_trans hαa hcIoo.1.le, le_trans hcIoo.2.le hbβ⟩
      simp only [Shade, Set.mem_ofPred_eq, not_and, not_forall] at hcnot
      obtain ⟨y, hy, hlt⟩ := hcnot hcIcc
      simp only [not_le] at hlt
      rcases le_or_gt y b with hyb | hyb
      · exact absurd (hcmax ⟨le_trans hc.1 hy.1, hyb⟩) (not_le.mpr hlt)
      · have h1 : g y ≤ g b := hb.2 y ⟨hyb.le, hy.2⟩
        have h2 : g b ≤ g c := hcmax ⟨hx.2.le, le_rfl⟩
        linarith
  rcases eq_or_lt_of_le hab with h | h
  · simp [h]
  · have hne : (nhdsWithin a (Ioo a b)).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT h]; infer_instance
    refine le_of_tendsto (hg.continuousWithinAt (s := Ioo a b) (x := a)) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx using key x hx



/-- The last point at which the potential is still at its initial level; the interval
`[α, bstar]` is the first stopping interval. -/
def bstar (g : ℝ → ℝ) (α β : ℝ) : ℝ := sSup (Icc α β ∩ {x | g α ≤ g x})

lemma bstar_mem {g : ℝ → ℝ} (hg : Continuous g) {α β : ℝ} (hab : α ≤ β) :
    bstar g α β ∈ Icc α β ∩ {x | g α ≤ g x} := by
  refine IsClosed.csSup_mem (isClosed_Icc.inter (isClosed_le continuous_const hg))
    ⟨α, ⟨le_rfl, hab⟩, (le_rfl : g α ≤ g α)⟩ ⟨β, fun x hx => hx.1.2⟩

lemma bstar_spec {g : ℝ → ℝ} (hg : Continuous g) {α β : ℝ} (hab : α < β) (hlt : g β < g α) :
    α ≤ bstar g α β ∧ bstar g α β < β ∧ g (bstar g α β) = g α ∧
      bstar g α β ∈ Shade g α β := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := bstar_mem hg hab.le
  simp only [Set.mem_ofPred_eq] at h3
  have hne : bstar g α β ≠ β := by
    intro h; rw [h] at h3; linarith
  have hblt : bstar g α β < β := lt_of_le_of_ne h2 hne
  -- above `bstar` the potential is strictly below its initial level
  have habove : ∀ y, bstar g α β < y → y ≤ β → g y < g α := by
    intro y hy hyβ
    by_contra hcon
    push Not at hcon
    have : y ≤ bstar g α β :=
      le_csSup ⟨β, fun x hx => hx.1.2⟩ ⟨⟨le_trans h1 hy.le, hyβ⟩, hcon⟩
    linarith
  have hle : g (bstar g α β) ≤ g α := by
    have hnb : (nhdsWithin (bstar g α β) (Ioo (bstar g α β) β)).NeBot := by
      rw [nhdsWithin_Ioo_eq_nhdsGT hblt]; infer_instance
    refine le_of_tendsto (hg.continuousWithinAt (s := Ioo (bstar g α β) β)) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy using (habove y hy.1 hy.2.le).le
  have hgeq : g (bstar g α β) = g α := le_antisymm hle h3
  refine ⟨h1, hblt, hgeq, ⟨⟨h1, h2⟩, ?_⟩⟩
  intro y hy
  rcases eq_or_lt_of_le hy.1 with h | h
  · simp [← h]
  · rw [hgeq]; exact (habove y h hy.2).le

/-- Left endpoint of the sunlit component of `x`. -/
def cl (g : ℝ → ℝ) (α β b₀ x : ℝ) : ℝ := sSup (Shade g α β ∩ Icc b₀ x)

/-- Right endpoint of the sunlit component of `x`. -/
def cr (g : ℝ → ℝ) (α β x : ℝ) : ℝ := sInf (Shade g α β ∩ Icc x β)

variable {g : ℝ → ℝ} {α β b₀ x : ℝ}

lemma cl_mem (hg : Continuous g) (_hab : α ≤ β) (hb₀ : b₀ ∈ Shade g α β) (hx : b₀ ≤ x) :
    cl g α β b₀ x ∈ Shade g α β ∩ Icc b₀ x :=
  IsClosed.csSup_mem ((isClosed_shade hg α β).inter isClosed_Icc)
    ⟨b₀, hb₀, le_rfl, hx⟩ ⟨x, fun _ hz => hz.2.2⟩

lemma cr_mem (hg : Continuous g) (hab : α ≤ β) (hxβ : x ≤ β) :
    cr g α β x ∈ Shade g α β ∩ Icc x β :=
  IsClosed.csInf_mem ((isClosed_shade hg α β).inter isClosed_Icc)
    ⟨β, right_mem_shade hab, hxβ, le_rfl⟩ ⟨x, fun _ hz => hz.2.1⟩

lemma component_spec (hg : Continuous g) (hab : α ≤ β) (hb₀ : b₀ ∈ Shade g α β)
    (hx : b₀ ≤ x) (hxβ : x ≤ β) (hxn : x ∉ Shade g α β) :
    b₀ ≤ cl g α β b₀ x ∧ cl g α β b₀ x < x ∧ x < cr g α β x ∧ cr g α β x ≤ β ∧
      cl g α β b₀ x ∈ Shade g α β ∧ cr g α β x ∈ Shade g α β ∧
      (∀ y ∈ Ioo (cl g α β b₀ x) (cr g α β x), y ∉ Shade g α β) ∧
      g (cl g α β b₀ x) = g (cr g α β x) := by
  obtain ⟨hlS, hl1, hl2⟩ := cl_mem hg hab hb₀ hx
  obtain ⟨hrS, hr1, hr2⟩ := cr_mem (g := g) hg hab hxβ
  have hlx : cl g α β b₀ x < x := lt_of_le_of_ne hl2 (by intro h; rw [h] at hlS; exact hxn hlS)
  have hxr : x < cr g α β x := lt_of_le_of_ne hr1 (by rintro h; exact hxn (h ▸ hrS))
  have hgap : ∀ y ∈ Ioo (cl g α β b₀ x) (cr g α β x), y ∉ Shade g α β := by
    intro y hy hyS
    rcases le_or_gt y x with h | h
    · have : y ≤ cl g α β b₀ x :=
        le_csSup ⟨x, fun z hz => hz.2.2⟩ ⟨hyS, le_trans hl1 hy.1.le, h⟩
      linarith [hy.1]
    · have : cr g α β x ≤ y :=
        csInf_le ⟨x, fun z hz => hz.2.1⟩ ⟨hyS, h.le, le_trans hy.2.le hr2⟩
      linarith [hy.2]
  refine ⟨hl1, hlx, hxr, hr2, hlS, hrS, hgap, le_antisymm ?_ ?_⟩
  · exact rising_sun hg (le_trans hb₀.1.1 hl1) (le_of_lt (lt_trans hlx hxr)) hr2 hrS hgap
  · exact hlS.2 _ ⟨le_of_lt (lt_trans hlx hxr), hr2⟩

lemma component_stable (hg : Continuous g) (hab : α ≤ β) (hb₀ : b₀ ∈ Shade g α β)
    (hx : b₀ ≤ x) (hxβ : x ≤ β) (hxn : x ∉ Shade g α β)
    {y : ℝ} (hy : y ∈ Ioo (cl g α β b₀ x) (cr g α β x)) :
    cl g α β b₀ y = cl g α β b₀ x ∧ cr g α β y = cr g α β x := by
  obtain ⟨hl1, hlx, hxr, hr2, hlS, hrS, hgap, -⟩ := component_spec hg hab hb₀ hx hxβ hxn
  have hyβ : y ≤ β := le_trans hy.2.le hr2
  have hb₀y : b₀ ≤ y := le_trans hl1 hy.1.le
  constructor
  · refine le_antisymm (csSup_le ⟨cl g α β b₀ x, hlS, hl1, hy.1.le⟩ ?_)
      (le_csSup ⟨y, fun z hz => hz.2.2⟩ ⟨hlS, hl1, hy.1.le⟩)
    rintro z ⟨hzS, -, hzy⟩
    by_contra hcon
    push Not at hcon
    exact hgap z ⟨hcon, lt_of_le_of_lt hzy hy.2⟩ hzS
  · refine le_antisymm (csInf_le ⟨y, fun z hz => hz.2.1⟩ ⟨hrS, hy.2.le, hr2⟩)
      (le_csInf ⟨cr g α β x, hrS, hy.2.le, hr2⟩ ?_)
    rintro z ⟨hzS, hyz, -⟩
    by_contra hcon
    push Not at hcon
    exact hgap z ⟨lt_of_lt_of_le hy.1 hyz, hcon⟩ hzS



/-! ### The potential attached to a weight -/

/-- `w` cut off outside `[α,β]`; a globally integrable function agreeing with `w` on `[α,β]`. -/
def wcut (w : ℝ → ℝ) (α β : ℝ) : ℝ → ℝ := (Icc α β).indicator w

/-- The rising-sun potential `g x = ℓ (x - α) - ∫_α^x w`, whose derivative is `ℓ - w`. -/
def pot (w : ℝ → ℝ) (α β ℓ : ℝ) : ℝ → ℝ := fun x => ℓ * (x - α) - ∫ t in α..x, wcut w α β t

lemma wcut_eq {w : ℝ → ℝ} {α β x : ℝ} (hx : x ∈ Icc α β) : wcut w α β x = w x :=
  Set.indicator_of_mem hx w

lemma wcut_integrable {w : ℝ → ℝ} {α β : ℝ} (hint : IntervalIntegrable w volume α β) :
    Integrable (wcut w α β) volume :=
  (integrable_indicator_iff measurableSet_Icc).mpr
    ((integrableOn_Icc_iff_integrableOn_Ioc).mpr hint.1)

lemma wcut_ii {w : ℝ → ℝ} {α β : ℝ} (hint : IntervalIntegrable w volume α β) (a b : ℝ) :
    IntervalIntegrable (wcut w α β) volume a b :=
  (wcut_integrable hint).intervalIntegrable

lemma pot_continuous {w : ℝ → ℝ} {α β ℓ : ℝ} (hint : IntervalIntegrable w volume α β) :
    Continuous (pot w α β ℓ) :=
  Continuous.sub (by fun_prop) (intervalIntegral.continuous_primitive (wcut_ii hint) α)

lemma pot_sub {w : ℝ → ℝ} {α β ℓ p q : ℝ} (hint : IntervalIntegrable w volume α β)
    (hp : α ≤ p) (hpq : p ≤ q) (hq : q ≤ β) :
    pot w α β ℓ q - pot w α β ℓ p = ℓ * (q - p) - ∫ t in p..q, w t := by
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (wcut_ii hint α p) (wcut_ii hint p q)
  have hcong : ∫ t in p..q, wcut w α β t = ∫ t in p..q, w t := by
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [uIcc_of_le hpq] at ht
    exact wcut_eq ⟨le_trans hp ht.1, le_trans ht.2 hq⟩
  simp only [pot]
  rw [← hadd, ← hcong]
  ring

lemma pot_avg {w : ℝ → ℝ} {α β ℓ p q : ℝ} (hint : IntervalIntegrable w volume α β)
    (hp : α ≤ p) (hpq : p ≤ q) (hq : q ≤ β)
    (h : pot w α β ℓ p = pot w α β ℓ q) : ∫ t in p..q, w t = ℓ * (q - p) := by
  have := pot_sub (ℓ := ℓ) hint hp hpq hq
  rw [← h] at this
  linarith

lemma pot_left {w : ℝ → ℝ} {α β ℓ : ℝ} : pot w α β ℓ α = 0 := by simp [pot]

lemma pot_right_lt {w : ℝ → ℝ} {α β ℓ : ℝ} (hint : IntervalIntegrable w volume α β)
    (hab : α ≤ β) (hℓ : ℓ * (β - α) < ∫ t in α..β, w t) :
    pot w α β ℓ β < pot w α β ℓ α := by
  have := pot_sub (ℓ := ℓ) hint le_rfl hab le_rfl
  rw [pot_left] at *
  linarith

lemma pot_hasDerivAt {w : ℝ → ℝ} {α β ℓ : ℝ} (hint : IntervalIntegrable w volume α β) :
    ∀ᵐ x, HasDerivAt (pot w α β ℓ) (ℓ - wcut w α β x) x := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
    (wcut_integrable hint).locallyIntegrable] with x hx
  have h1 : HasDerivAt (fun y : ℝ => ℓ * (y - α)) ℓ x := by
    simpa using ((hasDerivAt_id x).sub_const α).const_mul ℓ
  exact h1.sub (hx α)

/-- Almost everywhere on the shade the weight is at least `ℓ`: this is where the
Lebesgue differentiation theorem enters. -/
lemma ae_ge_of_mem_shade {w : ℝ → ℝ} {α β ℓ : ℝ} (hint : IntervalIntegrable w volume α β)
    (_hab : α < β) :
    ∀ᵐ x, x ∈ Shade (pot w α β ℓ) α β → ℓ ≤ w x := by
  have hβ : ∀ᵐ x : ℝ, x ≠ β := by simp [ae_iff, measure_singleton]
  filter_upwards [pot_hasDerivAt (ℓ := ℓ) hint, hβ] with x hd hxβ hxS
  rw [← wcut_eq (w := w) hxS.1]
  by_contra hcon
  push Not at hcon
  have hxlt : x < β := lt_of_le_of_ne hxS.1.2 hxβ
  have hslope := hasDerivAt_iff_tendsto_slope.mp hd
  have h1 : ∀ᶠ y in nhdsWithin x {x}ᶜ, 0 < slope (pot w α β ℓ) x y :=
    hslope.eventually (eventually_gt_nhds (by linarith))
  have hsub : nhdsWithin x (Ioo x β) ≤ nhdsWithin x {x}ᶜ :=
    nhdsWithin_mono x (fun y hy => ne_of_gt hy.1)
  have hne : (nhdsWithin x (Ioo x β)).NeBot := by
    rw [nhdsWithin_Ioo_eq_nhdsGT hxlt]; infer_instance
  obtain ⟨y, hy1, hy2⟩ := ((h1.filter_mono hsub).and self_mem_nhdsWithin).exists
  have hgy : pot w α β ℓ x < pot w α β ℓ y := by
    have hyx : (0:ℝ) < y - x := by linarith [hy2.1]
    have hy1' : 0 < (y - x)⁻¹ * (pot w α β ℓ y - pot w α β ℓ x) := by
      simpa [slope, div_eq_inv_mul] using hy1
    rcases mul_pos_iff.mp hy1' with ⟨-, h⟩ | ⟨h, -⟩
    · linarith
    · exact absurd h (not_lt.mpr (le_of_lt (inv_pos.mpr hyx)))
  exact absurd (hxS.2 y ⟨hy2.1.le, hy2.2.le⟩) (not_le.mpr hgy)



/-! ### The stopping family -/

/-- **Stopping decomposition.**  For every `ε > 0` there is a finite pairwise disjoint family of
subintervals of `[α,β]`, on each of which the average of `w` is exactly half the average of `w`
over `[α,β]`, which covers `{w < ℓ}` up to a set of measure `ε`. -/
lemma stopping_family {w : ℝ → ℝ} (hpos : ∀ t, 0 < w t) {α β : ℝ} (hab : α < β)
    (hint : IntervalIntegrable w volume α β) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Finset (ℝ × ℝ),
      (∀ pq ∈ s, α ≤ pq.1 ∧ pq.1 ≤ pq.2 ∧ pq.2 ≤ β) ∧
      ((s : Set (ℝ × ℝ)).PairwiseDisjoint (fun pq => Ioo pq.1 pq.2)) ∧
      (∀ pq ∈ s, ∫ x in pq.1..pq.2, w x = (weightMean w α β / 2) * (pq.2 - pq.1)) ∧
      volume ({x | x ∈ Icc α β ∧ w x < weightMean w α β / 2} \ ⋃ pq ∈ s, Ioo pq.1 pq.2)
        ≤ ENNReal.ofReal ε := by
  classical
  have hba : (0:ℝ) < β - α := by linarith
  set W : ℝ := ∫ x in α..β, w x with hWdef
  have hW : 0 < W := intervalIntegral.intervalIntegral_pos_of_pos_on hint
    (fun x _ => hpos x) hab
  set ℓ : ℝ := weightMean w α β / 2 with hℓdef
  have hℓW : ℓ * (β - α) = W / 2 := by
    have hmean : weightMean w α β = W / (β - α) := rfl
    rw [hℓdef, hmean]
    field_simp
  have hℓlt : ℓ * (β - α) < W := by rw [hℓW]; linarith
  set g : ℝ → ℝ := pot w α β ℓ with hgdef
  have hgc : Continuous g := pot_continuous hint
  have hgβ : g β < g α := pot_right_lt hint hab.le hℓlt
  obtain ⟨hb1, hb2, hb3, hb4⟩ := bstar_spec hgc hab hgβ
  set b₀ : ℝ := bstar g α β with hb₀def
  set S : Set ℝ := Shade g α β with hSdef
  -- almost everywhere on the shade the weight is at least `ℓ`
  have hae : volume {x | x ∈ S ∧ w x < ℓ} = 0 := by
    refine measure_mono_null (fun x hx => ?_) (ae_ge_of_mem_shade (ℓ := ℓ) hint hab)
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    exact fun hcon => absurd (hcon hx.1) (not_le.mpr hx.2)
  -- the sunlit part to the right of `b₀`
  set V : Set ℝ := Ioo b₀ β \ S with hVdef
  have hVopen : IsOpen V := isOpen_Ioo.sdiff (isClosed_shade hgc α β)
  have hVne : volume V ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (fun x hx => hx.1)) ?_)
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  obtain ⟨K, hKV, hKcomp, hKlt⟩ :=
    hVopen.measurableSet.exists_isCompact_lt_add hVne
      (ε := ENNReal.ofReal ε) (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; exact hε)
  have hVK : volume (V \ K) < ENNReal.ofReal ε :=
    measure_sdiff_lt_of_lt_add hKcomp.measurableSet.nullMeasurableSet hKV
      (ne_of_lt (lt_of_le_of_lt (measure_mono hKV) (lt_top_iff_ne_top.mpr hVne))) hKlt
  -- every point of `V` lies in its own component
  have hVspec : ∀ x : ℝ, x ∈ V → b₀ ≤ x ∧ x ≤ β ∧ x ∉ S := fun x hx =>
    ⟨hx.1.1.le, hx.1.2.le, hx.2⟩
  have hcover : K ⊆ ⋃ i : V, Ioo (cl g α β b₀ (i : ℝ)) (cr g α β (i : ℝ)) := by
    intro x hx
    have hxV : x ∈ V := hKV hx
    obtain ⟨h1, h2, h3, -⟩ := component_spec hgc hab.le hb4 (hVspec x hxV).1
      (hVspec x hxV).2.1 (hVspec x hxV).2.2
    exact Set.mem_iUnion.mpr ⟨⟨x, hxV⟩, h2, h3⟩
  obtain ⟨t, ht⟩ := hKcomp.elim_finite_subcover _
    (fun _ : V => isOpen_Ioo) hcover
  refine ⟨insert (α, b₀) (t.image (fun i : V => (cl g α β b₀ (i : ℝ), cr g α β (i : ℝ)))),
    ?_, ?_, ?_, ?_⟩
  · -- endpoints
    intro pq hpq
    rcases Finset.mem_insert.mp hpq with h | h
    · subst h; exact ⟨le_rfl, hb1, hb2.le⟩
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨h1, h2, h3, h4, -⟩ := component_spec hgc hab.le hb4 (hVspec i i.2).1
        (hVspec i i.2).2.1 (hVspec i i.2).2.2
      exact ⟨le_trans hb1 h1, le_of_lt (lt_trans h2 h3), h4⟩
  · -- pairwise disjointness
    intro p hp q hq hne
    have hkey : ∀ i : V, b₀ ≤ cl g α β b₀ (i : ℝ) := fun i =>
      (component_spec hgc hab.le hb4 (hVspec i i.2).1 (hVspec i i.2).2.1 (hVspec i i.2).2.2).1
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_image] at hp hq
    have hsep : ∀ i : V, Disjoint (Ioo α b₀)
        (Ioo (cl g α β b₀ (i : ℝ)) (cr g α β (i : ℝ))) := by
      intro i
      rw [Set.disjoint_left]
      intro x hx hx'
      exact absurd (lt_of_le_of_lt (hkey i) hx'.1) (not_lt.mpr hx.2.le)
    rcases hp with rfl | ⟨i, hi, rfl⟩ <;> rcases hq with rfl | ⟨j, hj, rfl⟩
    · exact absurd rfl hne
    · exact hsep j
    · exact (hsep i).symm
    · simp only [Function.onFun]
      rw [Set.disjoint_left]
      intro x hx hx'
      obtain ⟨e1, e2⟩ := component_stable hgc hab.le hb4 (hVspec i i.2).1
        (hVspec i i.2).2.1 (hVspec i i.2).2.2 hx
      obtain ⟨f1, f2⟩ := component_stable hgc hab.le hb4 (hVspec j j.2).1
        (hVspec j j.2).2.1 (hVspec j j.2).2.2 hx'
      exact hne (Prod.ext (by rw [← e1, ← f1]) (by rw [← e2, ← f2]))
  · -- exact averages
    intro pq hpq
    rcases Finset.mem_insert.mp hpq with h | h
    · subst h; exact pot_avg hint le_rfl hb1 hb2.le hb3.symm
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨h1, h2, h3, h4, -, -, -, h8⟩ := component_spec hgc hab.le hb4 (hVspec i i.2).1
        (hVspec i i.2).2.1 (hVspec i i.2).2.2
      exact pot_avg hint (le_trans hb1 h1) (le_of_lt (lt_trans h2 h3)) h4 h8
  · -- the covering estimate
    set U : Set ℝ := ⋃ pq ∈ insert (α, b₀)
      (t.image (fun i : V => (cl g α β b₀ (i : ℝ), cr g α β (i : ℝ)))), Ioo pq.1 pq.2 with hUdef
    have hUα : Ioo α b₀ ⊆ U := by
      intro x hx
      exact Set.mem_biUnion (Finset.mem_insert_self _ _) hx
    have hUi : ∀ i ∈ t, Ioo (cl g α β b₀ (i : ℝ)) (cr g α β (i : ℝ)) ⊆ U := by
      intro i hi x hx
      exact Set.mem_biUnion (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨i, hi, rfl⟩)) hx
    have hsubset : {x | x ∈ Icc α β ∧ w x < ℓ} \ U ⊆ (V \ K) ∪ ({x | x ∈ S ∧ w x < ℓ} ∪ {α}) := by
      rintro x ⟨⟨hx1, hx2⟩, hxU⟩
      by_cases hxS : x ∈ S
      · exact Or.inr (Or.inl ⟨hxS, hx2⟩)
      rcases eq_or_lt_of_le hx1.1 with h | h
      · exact Or.inr (Or.inr (by simp [← h]))
      rcases le_or_gt x b₀ with hle | hgt
      · exact absurd (hUα ⟨h, lt_of_le_of_ne hle (by rintro rfl; exact hxS hb4)⟩) hxU
      · have hxβ : x < β := lt_of_le_of_ne hx1.2 (by
          rintro rfl; exact hxS (right_mem_shade hab.le))
        have hxV : x ∈ V := ⟨⟨hgt, hxβ⟩, hxS⟩
        by_cases hxK : x ∈ K
        · obtain ⟨i, hi, hmem⟩ := Set.mem_iUnion₂.mp (ht hxK)
          exact absurd (hUi i hi hmem) hxU
        · exact Or.inl ⟨hxV, hxK⟩
    have hZ : volume ({x | x ∈ S ∧ w x < ℓ} ∪ ({α} : Set ℝ)) = 0 :=
      measure_union_null hae (by simp)
    calc volume ({x | x ∈ Icc α β ∧ w x < ℓ} \ U)
        ≤ volume ((V \ K) ∪ ({x | x ∈ S ∧ w x < ℓ} ∪ {α})) := measure_mono hsubset
      _ ≤ volume (V \ K) + volume ({x | x ∈ S ∧ w x < ℓ} ∪ {α}) := measure_union_le _ _
      _ = volume (V \ K) := by rw [hZ, add_zero]
      _ ≤ ENNReal.ofReal ε := hVK.le



/-! ### The truncated logarithmic deficit -/

/-- `tdef N c u = min N (log⁺ (e^c / u))`, the truncated positive part of `c - log u`. -/
def tdef (N c u : ℝ) : ℝ := min N (max 0 (c - Real.log u))

lemma tdef_nonneg {N c u : ℝ} (hN : 0 ≤ N) : 0 ≤ tdef N c u :=
  le_min hN (le_max_left _ _)

lemma tdef_le {N c u : ℝ} : tdef N c u ≤ N := min_le_left _ _

lemma tdef_le_of_le {N c u d : ℝ} (hd : 0 ≤ d) (h : c - Real.log u ≤ d) : tdef N c u ≤ d :=
  le_trans (min_le_right _ _) (max_le hd h)

lemma tdef_shift {N c u d : ℝ} (hd : 0 ≤ d) : tdef N (d + c) u ≤ d + tdef N c u := by
  simp only [tdef]
  rcases le_total (max 0 (c - Real.log u)) N with h | h
  · refine le_trans (min_le_right _ _) ?_
    rw [min_eq_right h]
    rcases le_total 0 (c - Real.log u) with h2 | h2
    · rw [max_eq_right h2, max_eq_right (by linarith)]; linarith
    · rw [max_eq_left h2]
      exact max_le (by linarith) (by linarith)
  · rw [min_eq_left h]
    exact le_trans (min_le_left _ _) (by linarith)

/-- The truncated deficit is interval integrable. -/
lemma tdef_intervalIntegrable {w : ℝ → ℝ} {N c p q : ℝ} (hN : 0 ≤ N)
    (hint : IntervalIntegrable w volume p q) :
    IntervalIntegrable (fun x => tdef N c (w x)) volume p q := by
  rw [intervalIntegrable_iff] at hint ⊢
  have hmeas : AEStronglyMeasurable (fun x => tdef N c (w x)) (volume.restrict (uIoc p q)) := by
    have hw : AEMeasurable w (volume.restrict (uIoc p q)) := hint.aemeasurable
    have h1 : AEMeasurable (fun x => Real.log (w x)) (volume.restrict (uIoc p q)) :=
      Real.measurable_log.comp_aemeasurable hw
    have h2 : AEMeasurable (fun x => tdef N c (w x)) (volume.restrict (uIoc p q)) :=
      AEMeasurable.min aemeasurable_const
        (AEMeasurable.max aemeasurable_const (aemeasurable_const.sub h1))
    exact h2.aestronglyMeasurable
  refine Integrable.mono' (g := fun _ : ℝ => N) ?_ hmeas (.of_forall fun x => ?_)
  · exact integrableOn_const (by simp [Set.uIoc])
  · rw [Real.norm_eq_abs, abs_of_nonneg (tdef_nonneg hN)]
    exact tdef_le

/-- The mean truncated logarithmic deficit of `w` over `[p,q]`. -/
def defc (w : ℝ → ℝ) (N p q : ℝ) : ℝ :=
  (q - p)⁻¹ * ∫ x in p..q, tdef N (Real.log (weightMean w p q)) (w x)

lemma defc_nonneg {w : ℝ → ℝ} {N p q : ℝ} (hN : 0 ≤ N) (hpq : p ≤ q) : 0 ≤ defc w N p q := by
  refine mul_nonneg (by positivity) ?_
  refine intervalIntegral.integral_nonneg hpq (fun x _ => tdef_nonneg hN)

lemma defc_le {w : ℝ → ℝ} {N p q : ℝ} (hN : 0 ≤ N) (hpq : p < q)
    (hint : IntervalIntegrable w volume p q) : defc w N p q ≤ N := by
  have h : ∫ x in p..q, tdef N (Real.log (weightMean w p q)) (w x) ≤ ∫ _ in p..q, N :=
    intervalIntegral.integral_mono_on hpq.le (tdef_intervalIntegrable hN hint)
      intervalIntegrable_const (fun x _ => tdef_le)
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  rw [defc]
  rw [inv_mul_le_iff₀ (by linarith)]
  linarith

/-- The set of mean deficits, and its supremum. -/
def defSet (w : ℝ → ℝ) (N : ℝ) : Set ℝ :=
  insert 0 {r | ∃ p q : ℝ, p < q ∧ IntervalIntegrable w volume p q ∧ r = defc w N p q}

def Psi (w : ℝ → ℝ) (N : ℝ) : ℝ := sSup (defSet w N)

lemma defSet_bddAbove {w : ℝ → ℝ} {N : ℝ} (hN : 0 ≤ N) : BddAbove (defSet w N) := by
  refine ⟨N, ?_⟩
  rintro r (rfl | ⟨p, q, hpq, hint, rfl⟩)
  · exact hN
  · exact defc_le hN hpq hint

lemma Psi_nonneg {w : ℝ → ℝ} {N : ℝ} (hN : 0 ≤ N) : 0 ≤ Psi w N :=
  le_csSup (defSet_bddAbove hN) (Set.mem_insert _ _)

lemma defc_le_Psi {w : ℝ → ℝ} {N p q : ℝ} (hN : 0 ≤ N) (hpq : p < q)
    (hint : IntervalIntegrable w volume p q) : defc w N p q ≤ Psi w N :=
  le_csSup (defSet_bddAbove hN) (Set.mem_insert_of_mem _ ⟨p, q, hpq, hint, rfl⟩)




/-! ### The self-improvement inequality -/

lemma integrableOn_const_of_subset {s : Set ℝ} {a b : ℝ} (h : s ⊆ Ioc a b) (c : ℝ) :
    IntegrableOn (fun _ : ℝ => c) s volume :=
  integrableOn_const (ne_of_lt (lt_of_le_of_lt (measure_mono h) (by simp)))

lemma defc_self_improve_eps {w : ℝ → ℝ} {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁) (hσ : 0 < σ)
    (hA1 : WeightA1Pos w C₁ σ) {N : ℝ} (hN : 0 ≤ N)
    {α β : ℝ} (hab : α < β) (hint : IntervalIntegrable w volume α β) {ε : ℝ} (hε : 0 < ε) :
    ∫ x in α..β, tdef N (Real.log (weightMean w α β)) (w x)
      ≤ (β - α) * Real.log 2 + N * ε
        + kap C₁ σ * (β - α) * (Real.log 2 + Psi w N) := by
  classical
  have hpos := hA1.1
  have hba : (0:ℝ) < β - α := by linarith
  have hW : 0 < ∫ x in α..β, w x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun x _ => hpos x) hab
  set A : ℝ := weightMean w α β with hAdef
  have hA : 0 < A := by rw [hAdef, weightMean, intervalAvg]; exact div_pos hW hba
  set ℓ : ℝ := A / 2 with hℓdef
  have hℓ : 0 < ℓ := by positivity
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlogA : Real.log A = Real.log 2 + Real.log ℓ := by
    rw [hℓdef, show A = 2 * (A / 2) by ring, Real.log_mul (by norm_num) (by positivity)]
    ring_nf
  set Φ : ℝ → ℝ := fun x => tdef N (Real.log A) (w x) with hΦdef
  have hΦii : IntervalIntegrable Φ volume α β := tdef_intervalIntegrable hN hint
  have hΦon : IntegrableOn Φ (Ioc α β) volume := hΦii.1
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := stopping_family hpos hab hint hε
  set U : Set ℝ := ⋃ pq ∈ s, Ioo pq.1 pq.2 with hUdef
  have hUmeas : MeasurableSet U := Finset.measurableSet_biUnion _ fun _ _ => measurableSet_Ioo
  have hUsub : U ⊆ Ioc α β := by
    intro x hx
    simp only [hUdef, Set.mem_iUnion] at hx
    obtain ⟨pq, hpq, hx⟩ := hx
    obtain ⟨h1, h2, h3⟩ := hs1 pq hpq
    exact ⟨lt_of_le_of_lt h1 hx.1, le_trans hx.2.le h3⟩
  have hsplit : ∫ x in α..β, Φ x
      = (∫ x in Ioc α β \ U, Φ x) + ∫ x in U, Φ x := by
    have h := MeasureTheory.integral_inter_add_sdiff (μ := volume) (f := Φ) hUmeas hΦon
    rw [Set.inter_eq_self_of_subset_right hUsub] at h
    rw [intervalIntegral.integral_of_le hab.le, ← h, add_comm]
  have hUbound : ∫ x in U, Φ x ≤ kap C₁ σ * (β - α) * (Real.log 2 + Psi w N) := by
    have hPsi0 : 0 ≤ Real.log 2 + Psi w N := by
      have := Psi_nonneg (w := w) hN; linarith
    have hbi : ∫ x in U, Φ x = ∑ pq ∈ s, ∫ x in Ioo pq.1 pq.2, Φ x := by
      refine MeasureTheory.integral_biUnion_finset _ (fun _ _ => measurableSet_Ioo) hs2
        (fun pq hpq => hΦon.mono_set ?_)
      intro x hx
      obtain ⟨h1, h2, h3⟩ := hs1 pq hpq
      exact ⟨lt_of_le_of_lt h1 hx.1, le_trans hx.2.le h3⟩
    have hterm : ∀ pq ∈ s, ∫ x in Ioo pq.1 pq.2, Φ x
        ≤ (pq.2 - pq.1) * (Real.log 2 + Psi w N) := by
      intro pq hpq
      obtain ⟨h1, h2, h3⟩ := hs1 pq hpq
      rcases eq_or_lt_of_le h2 with h | hlt
      · simp [← h]
      have hii : IntervalIntegrable w volume pq.1 pq.2 :=
        hint.mono_set (by rw [uIcc_of_le h2, uIcc_of_le hab.le]; exact Icc_subset_Icc h1 h3)
      have hmean : weightMean w pq.1 pq.2 = ℓ := by
        rw [weightMean, intervalAvg, hs3 pq hpq, mul_div_assoc,
          div_self (sub_ne_zero_of_ne hlt.ne'), mul_one, hℓdef, hAdef]
      have hsubIoo : Ioo pq.1 pq.2 ⊆ Ioc α β := by
        intro x hx; exact ⟨lt_of_le_of_lt h1 hx.1, le_trans hx.2.le h3⟩
      have htint : IntegrableOn
          (fun x => tdef N (Real.log (weightMean w pq.1 pq.2)) (w x)) (Ioo pq.1 pq.2) volume :=
        ((tdef_intervalIntegrable (c := Real.log (weightMean w pq.1 pq.2)) hN hii).1).mono_set
          Ioo_subset_Ioc_self
      have hconst : IntegrableOn (fun _ : ℝ => Real.log 2) (Ioo pq.1 pq.2) volume :=
        integrableOn_const_of_subset Ioo_subset_Ioc_self _
      have hkey : ∀ x, Φ x ≤ Real.log 2 + tdef N (Real.log (weightMean w pq.1 pq.2)) (w x) := by
        intro x
        rw [hmean]
        simp only [hΦdef]
        rw [hlogA]
        exact tdef_shift hlog2
      calc ∫ x in Ioo pq.1 pq.2, Φ x
          ≤ ∫ x in Ioo pq.1 pq.2,
              (Real.log 2 + tdef N (Real.log (weightMean w pq.1 pq.2)) (w x)) :=
            setIntegral_mono_on (hΦon.mono_set hsubIoo)
              (Integrable.add hconst htint) measurableSet_Ioo (fun x _ => hkey x)
        _ = (pq.2 - pq.1) * Real.log 2
              + ∫ x in Ioo pq.1 pq.2, tdef N (Real.log (weightMean w pq.1 pq.2)) (w x) := by
            rw [MeasureTheory.integral_add hconst htint, setIntegral_const,
              MeasureTheory.measureReal_def, Real.volume_Ioo,
              ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        _ = (pq.2 - pq.1) * Real.log 2 + (pq.2 - pq.1) * defc w N pq.1 pq.2 := by
            rw [defc, ← MeasureTheory.integral_Ioc_eq_integral_Ioo,
              ← intervalIntegral.integral_of_le h2]
            field_simp
        _ ≤ (pq.2 - pq.1) * (Real.log 2 + Psi w N) := by
            have hle := defc_le_Psi (w := w) hN hlt hii
            nlinarith [hle, hlt]
    calc ∫ x in U, Φ x = ∑ pq ∈ s, ∫ x in Ioo pq.1 pq.2, Φ x := hbi
      _ ≤ ∑ pq ∈ s, (pq.2 - pq.1) * (Real.log 2 + Psi w N) := Finset.sum_le_sum hterm
      _ = (∑ pq ∈ s, (pq.2 - pq.1)) * (Real.log 2 + Psi w N) := by rw [Finset.sum_mul]
      _ ≤ (kap C₁ σ * (β - α)) * (Real.log 2 + Psi w N) := by
          refine mul_le_mul_of_nonneg_right ?_ hPsi0
          exact length_bound hC₁ hσ hA1 hab hint s hs1 hs2
            (fun pq hpq => le_of_eq (hs3 pq hpq))
      _ = kap C₁ σ * (β - α) * (Real.log 2 + Psi w N) := by ring
  have hOut : ∫ x in Ioc α β \ U, Φ x ≤ (β - α) * Real.log 2 + N * ε := by
    set Bad : Set ℝ := {x | x ∈ Icc α β ∧ w x < weightMean w α β / 2} with hBaddef
    set G : Set ℝ := toMeasurable volume (Bad \ U) with hGdef
    have hGmeas : MeasurableSet G := measurableSet_toMeasurable _ _
    have hGvol : volume G ≤ ENNReal.ofReal ε := by
      rw [hGdef, measure_toMeasurable]; exact hs4
    have hGsub : Bad \ U ⊆ G := subset_toMeasurable _ _
    set s0 : Set ℝ := Ioc α β \ U with hs0def
    have hs0meas : MeasurableSet s0 := measurableSet_Ioc.diff hUmeas
    have hs0sub : s0 ⊆ Ioc α β := Set.sdiff_subset
    have hs0int : IntegrableOn Φ s0 volume := hΦon.mono_set hs0sub
    have hdec := MeasureTheory.integral_inter_add_sdiff (μ := volume) (f := Φ) hGmeas hs0int
    have h1 : ∫ x in s0 ∩ G, Φ x ≤ N * ε := by
      have hbd : ∫ x in s0 ∩ G, Φ x ≤ ∫ _ in s0 ∩ G, N :=
        setIntegral_mono_on (hs0int.mono_set Set.inter_subset_left)
          (integrableOn_const_of_subset (le_trans Set.inter_subset_left hs0sub) _)
          (hs0meas.inter hGmeas) (fun x _ => tdef_le)
      rw [setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul] at hbd
      refine le_trans hbd ?_
      have hvol : (volume (s0 ∩ G)).toReal ≤ ε := by
        have h2 : volume (s0 ∩ G) ≤ ENNReal.ofReal ε :=
          le_trans (measure_mono Set.inter_subset_right) hGvol
        calc (volume (s0 ∩ G)).toReal ≤ (ENNReal.ofReal ε).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
          _ = ε := ENNReal.toReal_ofReal hε.le
      nlinarith [hvol, (volume (s0 ∩ G)).toReal_nonneg]
    have h2 : ∫ x in s0 \ G, Φ x ≤ (β - α) * Real.log 2 := by
      have hptw : ∀ x ∈ s0 \ G, Φ x ≤ Real.log 2 := by
        rintro x ⟨hx0, hxG⟩
        have hxBad : x ∉ Bad := fun hb => hxG (hGsub ⟨hb, hx0.2⟩)
        have hwx : ℓ ≤ w x := by
          by_contra hcon
          exact hxBad ⟨⟨hx0.1.1.le, hx0.1.2⟩, not_le.mp hcon⟩
        refine tdef_le_of_le hlog2 ?_
        have hmono : Real.log ℓ ≤ Real.log (w x) := Real.log_le_log hℓ hwx
        rw [hlogA]; linarith
      have hbd : ∫ x in s0 \ G, Φ x ≤ ∫ _ in s0 \ G, Real.log 2 :=
        setIntegral_mono_on (hs0int.mono_set Set.sdiff_subset)
          (integrableOn_const_of_subset (le_trans Set.sdiff_subset hs0sub) _)
          (hs0meas.diff hGmeas) hptw
      rw [setIntegral_const, MeasureTheory.measureReal_def, smul_eq_mul] at hbd
      refine le_trans hbd ?_
      have hvol : (volume (s0 \ G)).toReal ≤ β - α := by
        have hmm : volume (s0 \ G) ≤ volume (Ioc α β) :=
          measure_mono (le_trans Set.sdiff_subset hs0sub)
        rw [Real.volume_Ioc] at hmm
        calc (volume (s0 \ G)).toReal ≤ (ENNReal.ofReal (β - α)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top hmm
          _ = β - α := ENNReal.toReal_ofReal hba.le
      nlinarith [hvol, hlog2]
    linarith [hdec, h1, h2]
  rw [hsplit]
  calc (∫ x in Ioc α β \ U, Φ x) + ∫ x in U, Φ x
      ≤ ((β - α) * Real.log 2 + N * ε)
          + kap C₁ σ * (β - α) * (Real.log 2 + Psi w N) := add_le_add hOut hUbound
    _ = (β - α) * Real.log 2 + N * ε
          + kap C₁ σ * (β - α) * (Real.log 2 + Psi w N) := by ring



/-! ### The fixed point -/

/-- The constant produced by the fixed-point argument. -/
def Mconst (C₁ σ : ℝ) : ℝ := (1 + kap C₁ σ) * Real.log 2 / (1 - kap C₁ σ)

lemma Mconst_nonneg {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    0 ≤ Mconst C₁ σ := by
  have h1 : kap C₁ σ < 1 := kap_lt_one hC₁ hσ
  have h0 : 0 ≤ kap C₁ σ := kap_nonneg hC₁ hσ hσ1
  have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [Mconst]
  positivity

lemma defc_self_improve {w : ℝ → ℝ} {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁) (hσ : 0 < σ)
    (hA1 : WeightA1Pos w C₁ σ) {N : ℝ} (hN : 0 ≤ N)
    {α β : ℝ} (hab : α < β) (hint : IntervalIntegrable w volume α β) :
    defc w N α β ≤ (1 + kap C₁ σ) * Real.log 2 + kap C₁ σ * Psi w N := by
  have hba : (0:ℝ) < β - α := by linarith
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  have hεpos : 0 < δ * (β - α) / (N + 1) := by positivity
  have key := defc_self_improve_eps hC₁ hσ hA1 hN hab hint hεpos
  have hfrac : N / (N + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hNe : N * (δ * (β - α) / (N + 1)) ≤ δ * (β - α) := by
    have hrw : N * (δ * (β - α) / (N + 1)) = (N / (N + 1)) * (δ * (β - α)) := by ring
    rw [hrw]
    nlinarith [hfrac, mul_pos hδ hba]
  rw [defc, inv_mul_le_iff₀ hba]
  calc ∫ x in α..β, tdef N (Real.log (weightMean w α β)) (w x)
      ≤ (β - α) * Real.log 2 + N * (δ * (β - α) / (N + 1))
          + kap C₁ σ * (β - α) * (Real.log 2 + Psi w N) := key
    _ ≤ (β - α) * Real.log 2 + δ * (β - α)
          + kap C₁ σ * (β - α) * (Real.log 2 + Psi w N) := by linarith
    _ = (β - α) * ((1 + kap C₁ σ) * Real.log 2 + kap C₁ σ * Psi w N + δ) := by ring

lemma Psi_le_Mconst {w : ℝ → ℝ} {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hA1 : WeightA1Pos w C₁ σ) {N : ℝ} (hN : 0 ≤ N) : Psi w N ≤ Mconst C₁ σ := by
  have hk1 : kap C₁ σ < 1 := kap_lt_one hC₁ hσ
  have hk0 : 0 ≤ kap C₁ σ := kap_nonneg hC₁ hσ hσ1
  have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hP0 : 0 ≤ Psi w N := Psi_nonneg hN
  have hbound : Psi w N ≤ (1 + kap C₁ σ) * Real.log 2 + kap C₁ σ * Psi w N := by
    refine csSup_le ⟨0, Set.mem_insert _ _⟩ ?_
    rintro r (rfl | ⟨p, q, hpq, hii, rfl⟩)
    · nlinarith
    · exact defc_self_improve hC₁ hσ hA1 hN hpq hii
  rw [Mconst, le_div_iff₀ (by linarith)]
  nlinarith [hbound]

/-! ### Passing to the limit -/

lemma weightMean_le {w : ℝ → ℝ} {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hA1 : WeightA1Pos w C₁ σ) {a b : ℝ} (hab : a < b)
    (hint : IntervalIntegrable w volume a b) :
    weightMean w a b ≤ Real.exp (Mconst C₁ σ) * weightGeomMean w a b := by
  have hpos := hA1.1
  have hba : (0:ℝ) < b - a := by linarith
  have hW : 0 < ∫ x in a..b, w x :=
    intervalIntegral.intervalIntegral_pos_of_pos_on hint (fun x _ => hpos x) hab
  set A : ℝ := weightMean w a b with hAdef
  have hA : 0 < A := by rw [hAdef, weightMean, intervalAvg]; exact div_pos hW hba
  set M : ℝ := Mconst C₁ σ with hMdef
  have hM0 : 0 ≤ M := Mconst_nonneg hC₁ hσ hσ1
  set F : ℝ → ℝ := fun x => max 0 (Real.log A - Real.log (w x)) with hFdef
  have hF0 : ∀ x, 0 ≤ F x := fun x => le_max_left _ _
  have hwmeas : AEMeasurable w (volume.restrict (Ioc a b)) := hint.1.aemeasurable
  have hFmeas : AEStronglyMeasurable F (volume.restrict (Ioc a b)) := by
    have h1 : AEMeasurable (fun x => Real.log (w x)) (volume.restrict (Ioc a b)) :=
      Real.measurable_log.comp_aemeasurable hwmeas
    exact (AEMeasurable.max aemeasurable_const
      (aemeasurable_const.sub h1)).aestronglyMeasurable
  -- the truncations
  have htr : ∀ n : ℕ, (fun x => tdef (n : ℝ) (Real.log A) (w x))
      = fun x => min (n : ℝ) (F x) := fun n => rfl
  have hfn : ∀ n : ℕ, IntegrableOn (fun x => min (n : ℝ) (F x)) (Ioc a b) volume := by
    intro n
    have := (tdef_intervalIntegrable (N := (n : ℝ)) (c := Real.log A)
      (Nat.cast_nonneg n) hint).1
    rwa [htr n] at this
  have hbd : ∀ n : ℕ, ∫ x in Ioc a b, min (n : ℝ) (F x) ≤ M * (b - a) := by
    intro n
    have h1 : defc w (n : ℝ) a b ≤ M :=
      le_trans (defc_le_Psi (Nat.cast_nonneg n) hab hint)
        (Psi_le_Mconst hC₁ hσ hσ1 hA1 (Nat.cast_nonneg n))
    rw [defc, inv_mul_le_iff₀ hba, ← hAdef, intervalIntegral.integral_of_le hab.le,
      htr n] at h1
    linarith [h1]
  -- monotone convergence
  have hsup : ∀ x, (⨆ n : ℕ, ENNReal.ofReal (min (n : ℝ) (F x))) = ENNReal.ofReal (F x) := by
    intro x
    refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_right _ _)) ?_
    obtain ⟨n, hn⟩ := exists_nat_ge (F x)
    exact le_iSup_of_le n (ENNReal.ofReal_le_ofReal (le_min hn le_rfl))
  have hmono : ∀ x : ℝ, Monotone fun n : ℕ => ENNReal.ofReal (min (n : ℝ) (F x)) := by
    intro x m n hmn
    exact ENNReal.ofReal_le_ofReal
      (min_le_min (by exact_mod_cast hmn) le_rfl)
  have hameas : ∀ n : ℕ, AEMeasurable (fun x => ENNReal.ofReal (min (n : ℝ) (F x)))
      (volume.restrict (Ioc a b)) :=
    fun n => ENNReal.measurable_ofReal.comp_aemeasurable
      ((hfn n).aemeasurable)
  have hlint : ∫⁻ x in Ioc a b, ENNReal.ofReal (F x)
      = ⨆ n : ℕ, ∫⁻ x in Ioc a b, ENNReal.ofReal (min (n : ℝ) (F x)) := by
    rw [← MeasureTheory.lintegral_iSup' hameas (.of_forall hmono)]
    simp only [hsup]
  have hlint_le : ∫⁻ x in Ioc a b, ENNReal.ofReal (F x) ≤ ENNReal.ofReal (M * (b - a)) := by
    rw [hlint]
    refine iSup_le fun n => ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hfn n)
      (.of_forall fun x => le_min (Nat.cast_nonneg n) (hF0 x))]
    exact ENNReal.ofReal_le_ofReal (hbd n)
  have hFint : IntegrableOn F (Ioc a b) volume := by
    refine ⟨hFmeas, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal (.of_forall hF0)]
    exact lt_of_le_of_lt hlint_le ENNReal.ofReal_lt_top
  have hFbd : ∫ x in Ioc a b, F x ≤ M * (b - a) := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (.of_forall hF0) hFmeas]
    calc (∫⁻ x in Ioc a b, ENNReal.ofReal (F x)).toReal
        ≤ (ENNReal.ofReal (M * (b - a))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint_le
      _ = M * (b - a) := ENNReal.toReal_ofReal (by positivity)
  -- `log w` is integrable
  have hlogint : IntegrableOn (fun x => Real.log (w x)) (Ioc a b) volume := by
    have hg : IntegrableOn (fun x => w x + F x + |Real.log A|) (Ioc a b) volume :=
      (hint.1.add hFint).add (integrableOn_const_of_subset (subset_refl (Ioc a b)) _)
    have hm : AEStronglyMeasurable (fun x => Real.log (w x)) (volume.restrict (Ioc a b)) :=
      (Real.measurable_log.comp_aemeasurable hwmeas).aestronglyMeasurable
    refine Integrable.mono' hg hm (.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    rcases le_total 0 (Real.log (w x)) with h | h
    · rw [abs_of_nonneg h]
      have h1 : Real.log (w x) ≤ w x - 1 := Real.log_le_sub_one_of_pos (hpos x)
      have := hF0 x
      have := abs_nonneg (Real.log A)
      linarith
    · rw [abs_of_nonpos h]
      have h1 : Real.log A - Real.log (w x) ≤ F x := le_max_right _ _
      have h2 : -Real.log A ≤ |Real.log A| := neg_le_abs _
      have := (hpos x).le
      linarith
  -- conclusion
  have hconst : IntegrableOn (fun _ : ℝ => Real.log A) (Ioc a b) volume :=
    integrableOn_const_of_subset (subset_refl (Ioc a b)) _
  have hkey : ∫ x in Ioc a b, (Real.log A - Real.log (w x)) ≤ M * (b - a) := by
    refine le_trans (setIntegral_mono_on (hconst.sub hlogint) hFint measurableSet_Ioc
      (fun x _ => le_max_right _ _)) hFbd
  rw [MeasureTheory.integral_sub hconst hlogint, setIntegral_const,
    MeasureTheory.measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal hba.le,
    smul_eq_mul] at hkey
  have havg : Real.log A ≤ M + intervalAvg (fun t => Real.log (w t)) a b := by
    have hdiv : Real.log A - M ≤ (∫ x in Ioc a b, Real.log (w x)) / (b - a) := by
      rw [le_div_iff₀ hba]; nlinarith [hkey]
    rw [intervalAvg, intervalIntegral.integral_of_le hab.le]
    linarith [hdiv]
  calc A = Real.exp (Real.log A) := (Real.exp_log hA).symm
    _ ≤ Real.exp (M + intervalAvg (fun t => Real.log (w t)) a b) := Real.exp_le_exp.mpr havg
    _ = Real.exp M * weightGeomMean w a b := by rw [Real.exp_add, weightGeomMean]


end A1A2

/-- **(A1) implies (A2)**: an `A_∞`-weight in the form (A1) also satisfies
the arithmetic–geometric mean inequality (A2) for some constant `A₀ ≥ 1`.
(This is the bridge used by `beta_carleson_uniform`, whose proof routes
through `entropy_bound_ainfty`.) -/
theorem a1_imp_a2 (w : ℝ → ℝ) (hw : AInfinityWeight w) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ WeightA2 w A₀ := by
  obtain ⟨C₁, σ, hC₁, hσ, hσ1, hA1w⟩ := hw
  obtain ⟨v, hvw, hA1⟩ := hA1w.exists_pos
  refine ⟨Real.exp (A1A2.Mconst C₁ σ), ?_, ?_⟩
  · rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (A1A2.Mconst_nonneg hC₁ hσ hσ1)
  · intro a b hab
    -- `weightMean` and `weightGeomMean` only see `w` through integrals, so they
    -- are unchanged by passing to the everywhere-positive representative `v`
    have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → v x = w x := by
      filter_upwards [hvw] with x hx _ using hx
    have haelog : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b →
        Real.log (v x) = Real.log (w x) := by
      filter_upwards [hvw] with x hx _ using by rw [hx]
    have hmean : weightMean w a b = weightMean v a b := by
      rw [weightMean, weightMean, intervalAvg, intervalAvg,
        intervalIntegral.integral_congr_ae hae]
    have hgeom : weightGeomMean w a b = weightGeomMean v a b := by
      rw [weightGeomMean, weightGeomMean, intervalAvg, intervalAvg,
        intervalIntegral.integral_congr_ae haelog]
    rw [hmean, hgeom]
    by_cases hint : IntervalIntegrable v volume a b
    · exact A1A2.weightMean_le hC₁ hσ hσ1 hA1 hab hint
    · rw [weightMean, intervalAvg, intervalIntegral.integral_undef hint]
      simp only [zero_div]
      unfold weightGeomMean
      positivity

/-! ## Carleson measures on the upper half-plane (Section 2.1) -/

/-- The Carleson box `Q_I = I × (0, |I|]` for `I = [a, b]`, as a subset of
`ℝ × ℝ`. -/
def carlesonBox (a b : ℝ) : Set (ℝ × ℝ) :=
  Set.Ioc a b ×ˢ Set.Ioc (0 : ℝ) (b - a)

/-- The integral of `F² / y` over the Carleson box `Q_I`, as an extended
non-negative real. Since the integrand is non-negative this needs no
integrability side conditions, and it equals `∞` when the integral diverges —
so unlike the Bochner-valued `carlesonBoxIntegral`, no junk value can make a
divergent box integral look small. -/
def carlesonBoxLIntegral (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ p in carlesonBox a b, ENNReal.ofReal ((F p.1 p.2) ^ 2 / p.2)

/-- Integral of `F² / y` over the Carleson box `Q_I = I × (0, |I|]`,
for `I = [a, b]`. (Bochner-valued; used for the `T²`-norm statements.) -/
def carlesonBoxIntegral (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in (0:ℝ)..(b - a), (F x y) ^ 2 / y

/-- The tent-space norm `‖F‖_{T²(J)} := (|J|⁻¹ ∬_{Q_J} |F|² dxdy/y)^{1/2}`. -/
def T2norm (F : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  Real.sqrt ((b - a)⁻¹ * carlesonBoxIntegral F a b)

/-- `F² dxdy/y` is a Carleson measure: the box integrals are uniformly
finite, `∬_{Q_J} F² dxdy/y ≤ C |J|` for every bounded interval `J`.
Stated with the `ℝ≥0∞`-valued box integral, so the predicate is false when
some box integral diverges. -/
def IsCarlesonFn (F : ℝ → ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, a < b →
    carlesonBoxLIntegral F a b ≤ ENNReal.ofReal (C * (b - a))

/-- `F² dxdy/y` is a vanishing Carleson measure: in addition the box
integrals satisfy `∬_{Q_J} F² dxdy/y ≤ ε |J|` for every sufficiently short
interval `J`, uniformly in the position of `J`. -/
def IsVanishingCarleson (F : ℝ → ℝ → ℝ) : Prop :=
  IsCarlesonFn F ∧
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ a b : ℝ, a < b → b - a ≤ δ →
      carlesonBoxLIntegral F a b ≤ ENNReal.ofReal (ε * (b - a))

/-! ## Poisson kernel of the upper half-plane -/

/-- The Poisson kernel `P_z(t) = (1/π) y / ((t - x)² + y²)` at `z = x + iy`. -/
def poissonKernelUHP (z : ℂ) (t : ℝ) : ℝ :=
  z.im / (Real.pi * ((t - z.re) ^ 2 + z.im ^ 2))

end VanishingCarleson

end
