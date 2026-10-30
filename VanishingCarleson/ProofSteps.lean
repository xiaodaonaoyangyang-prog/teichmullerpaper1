/-
# Proof steps: auxiliary results of §§2–9, the comparison theorem and the
beta-number Carleson estimates

This file collects the intermediate results that the paper's proofs invoke
and that do not fit a single upstream file, together with the §8 results that
need them:

* §2  Jensen `m_K ≤ (w)_K`, `|h(K)| = |K| (w)_K`, `(A1) ⇒ log w ∈ L¹_loc`,
  and `SS(ℝ) ⊆ QS` with `ρ = 4 A₀²` (`ainfty_imp_quasisymmetric`).
* §3.1 Scale invariance of the BMO norm (`bmo_norm_scale_invariance`).
* §5  Summation lemmas.
* §8  Theorem (Comparison) (`compare_beta_eps`), the master inequality and the
  beta-number Carleson estimates (C) `isCarlesonFn_betaPt` and (V)
  `isVanishingCarleson_betaPt`.
* §9  The scale identity and the domination principle
  `isVanishingCarleson_of_le` used in the proof of the main theorem.

Every statement of this file is proved, from the results of the upstream files.
-/
import Mathlib
import VanishingCarleson.TentEntropy

open MeasureTheory Real Set

noncomputable section

namespace VanishingCarleson

/-! ## Section 2: preliminaries -/

/-- **Jensen's inequality for the two means**: the geometric mean of a weight
over an interval does not exceed its arithmetic mean, `m_K ≤ (w)_K`. Besides
`w ∈ L¹(K)`, this needs `log w ∈ L¹(K)` (the paper's standing assumption
`α = log w ∈ L¹_loc(ℝ)`, §2 preliminaries): without it the average of `log w`
is mathlib's junk value `0`, making `m_K = 1`, which can exceed `(w)_K`. -/
theorem geomMean_le_mean (w : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hw : ∀ t, 0 < w t) (hint : IntervalIntegrable w volume a b)
    (hlog : IntervalIntegrable (fun t => Real.log (w t)) volume a b) :
    weightGeomMean w a b ≤ weightMean w a b := by
  have h0 : volume (Set.uIoc a b) ≠ 0 := by
    rw [Set.uIoc_of_le hab.le, Real.volume_Ioc]
    exact (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have ht : volume (Set.uIoc a b) ≠ ⊤ := by
    rw [Set.uIoc_of_le hab.le]
    simp
  have hfi : IntegrableOn (fun t => Real.log (w t)) (Set.uIoc a b) volume := by
    rw [Set.uIoc_of_le hab.le]; exact hlog.1
  have hgi : IntegrableOn (Real.exp ∘ fun t => Real.log (w t)) (Set.uIoc a b) volume := by
    rw [Set.uIoc_of_le hab.le]
    have heq : (Real.exp ∘ fun t => Real.log (w t)) = w := by
      funext t
      simp [Function.comp, Real.exp_log (hw t)]
    rw [heq]
    exact hint.1
  have hJensen := convexOn_exp.map_set_average_le Real.continuous_exp.continuousOn
    isClosed_univ h0 ht (by simp) hfi hgi
  rw [interval_average_eq_div, interval_average_eq_div] at hJensen
  have hexp_eq : (fun t => Real.exp (Real.log (w t))) = w := funext fun t => Real.exp_log (hw t)
  rw [hexp_eq] at hJensen
  simpa [weightGeomMean, weightMean, intervalAvg] using hJensen

/-- Transfer absolute continuity along an equality of functions on `uIcc a b`: the defining
`Tendsto` statement only ever evaluates `f`/`F` at points of `uIcc a b`. -/
private theorem absolutelyContinuousOnInterval_congr {f F : ℝ → ℝ} {a b : ℝ}
    (hF : AbsolutelyContinuousOnInterval F a b) (hEq : Set.EqOn f F (Set.uIcc a b)) :
    AbsolutelyContinuousOnInterval f a b := by
  rw [absolutelyContinuousOnInterval_iff] at hF ⊢
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := hF ε hε
  refine ⟨δ, hδpos, fun E hE hlen => ?_⟩
  have heq : (∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (F (E.2 i).1) (F (E.2 i).2) := by
    refine Finset.sum_congr rfl (fun i hi => ?_)
    obtain ⟨hmem, _⟩ := hE
    rw [hEq (hmem i hi).1, hEq (hmem i hi).2]
  rw [heq]
  exact hδ E hE hlen

/-- **`|h(K)| = |K| (w)_K`**: for a locally absolutely continuous increasing
`h` with `w = h'`, the length of the image interval is the arithmetic mean of
the weight times the length of the interval. -/
theorem imageLength_eq_mean (h : ℝ → ℝ) (hac : LocallyAbsolutelyContinuous h)
    (a b : ℝ) (hab : a < b) :
    h b - h a = (b - a) * weightMean (deriv h) a b := by
  obtain ⟨g, hg_int, hg_eq⟩ := hac.2 a b hab
  set F : ℝ → ℝ := fun t => h a + ∫ s in a..t, g s with hFdef
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => h a) a b :=
    LipschitzOnWith.absolutelyContinuousOnInterval (K := 0) (fun x _ y _ => by simp)
  have hintAC : AbsolutelyContinuousOnInterval (fun t => ∫ s in a..t, g s) a b :=
    hg_int.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hFac : AbsolutelyContinuousOnInterval F a b := hconst.add hintAC
  have hEq : Set.EqOn h F (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact hg_eq
  have hhac : AbsolutelyContinuousOnInterval h a b := absolutelyContinuousOnInterval_congr hFac hEq
  have hFTC : (∫ x in a..b, deriv h x) = h b - h a := hhac.integral_deriv_eq_sub
  show h b - h a = (b - a) * ((∫ t in a..b, deriv h t) / (b - a))
  rw [hFTC]
  have hba : (b - a) ≠ 0 := sub_ne_zero.mpr hab.ne'
  field_simp

/-- An everywhere-positive `(A1)` weight has a logarithm integrable on every interval. The
constant of `A1A2.weightMean_le` is scale invariant while the weight is not: if `log v` were not
integrable, the geometric mean of every multiple `c v` would be the junk value `e⁰ = 1`, so
`c (v)_K ≤ e^M` for all `c > 0`, which is absurd. -/
private theorem ps_log_intervalIntegrable_of_A1Pos {v : ℝ → ℝ} {C₁ σ : ℝ} (hC₁ : 1 ≤ C₁)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA1 : WeightA1Pos v C₁ σ) {a b : ℝ} (hab : a < b)
    (hint : IntervalIntegrable v volume a b) :
    IntervalIntegrable (fun t => Real.log (v t)) volume a b := by
  by_contra hnot
  have hmpos : 0 < weightMean v a b := by
    unfold weightMean intervalAvg
    exact div_pos (intervalIntegral.intervalIntegral_pos_of_pos_on hint
      (fun x _ => hA1.1 x) hab) (sub_pos.mpr hab)
  set M : ℝ := Real.exp (A1A2.Mconst C₁ σ) with hMdef
  set c : ℝ := (M + 1) / weightMean v a b with hcdef
  have hc : 0 < c := div_pos (by positivity) hmpos
  have hA1c : WeightA1Pos (fun t => c * v t) C₁ σ := by
    refine ⟨fun t => mul_pos hc (hA1.1 t), ?_⟩
    intro p q hpq E hE hEsub
    rw [integral_const_mul, integral_const_mul, mul_div_mul_left _ _ hc.ne']
    exact hA1.2 p q hpq E hE hEsub
  have hkey := A1A2.weightMean_le hC₁ hσ hσ1 hA1c hab (hint.const_mul c)
  have hmean : weightMean (fun t => c * v t) a b = c * weightMean v a b := by
    unfold weightMean intervalAvg
    rw [intervalIntegral.integral_const_mul]
    ring
  have hgeom : weightGeomMean (fun t => c * v t) a b = 1 := by
    have hnot' : ¬ IntervalIntegrable (fun t => Real.log (c * v t)) volume a b := by
      intro hi
      apply hnot
      have heq : (fun t => Real.log (v t)) = fun t => Real.log (c * v t) - Real.log c := by
        funext t
        rw [Real.log_mul hc.ne' (hA1.1 t).ne']
        ring
      rw [heq]
      exact hi.sub intervalIntegrable_const
    unfold weightGeomMean intervalAvg
    rw [intervalIntegral.integral_undef hnot', zero_div, Real.exp_zero]
  rw [hmean, hgeom, mul_one] at hkey
  have hcm : c * weightMean v a b = M + 1 := by
    rw [hcdef]
    field_simp
  linarith

/-- **(A1) ⇒ `log h' ∈ L¹_loc`**: for strictly increasing `h` whose derivative satisfies (A1),
`log h'` is integrable on every bounded interval (pass to the everywhere-positive
representative of `WeightA1.exists_pos`, which agrees with `h'` almost everywhere). -/
private theorem ps_logDeriv_intervalIntegrable (h : ℝ → ℝ) (hh : StrictMono h) (C₁ σ : ℝ)
    (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hw : WeightA1 (deriv h) C₁ σ) :
    ∀ u v : ℝ, u < v → IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v := by
  intro u v huv
  obtain ⟨g, hgw, hg⟩ := hw.exists_pos
  have hint : IntervalIntegrable (deriv h) volume u v :=
    (hh.monotone.monotoneOn _).intervalIntegrable_deriv
  have hintg : IntervalIntegrable g volume u v := hint.congr_ae (ae_restrict_of_ae hgw.symm)
  have hlogg := ps_log_intervalIntegrable_of_A1Pos hC₁ hσ hσ1 hg huv hintg
  refine hlogg.congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hgw] with t ht
  rw [ht]

/-- **Jensen's inequality, almost-everywhere form**: `m_K ≤ (w)_K` when `w > 0` only almost
everywhere (replace `w` on a null set by a positive function and apply `geomMean_le_mean`). -/
private theorem ps_geomMean_le_mean_ae (w : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hw : ∀ᵐ t ∂volume, 0 < w t) (hint : IntervalIntegrable w volume a b)
    (hlog : IntervalIntegrable (fun t => Real.log (w t)) volume a b) :
    weightGeomMean w a b ≤ weightMean w a b := by
  classical
  set v : ℝ → ℝ := fun t => if 0 < w t then w t else 1 with hvdef
  have hvw : v =ᵐ[volume] w := by
    filter_upwards [hw] with t ht
    simp [hvdef, ht]
  have hvpos : ∀ t, 0 < v t := by
    intro t
    simp only [hvdef]
    split_ifs with ht
    · exact ht
    · exact one_pos
  have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → v x = w x := by
    filter_upwards [hvw] with x hx _ using hx
  have haelog : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b → Real.log (v x) = Real.log (w x) := by
    filter_upwards [hvw] with x hx _ using by rw [hx]
  have hmean : weightMean w a b = weightMean v a b := by
    rw [weightMean, weightMean, intervalAvg, intervalAvg, intervalIntegral.integral_congr_ae hae]
  have hgeom : weightGeomMean w a b = weightGeomMean v a b := by
    rw [weightGeomMean, weightGeomMean, intervalAvg, intervalAvg,
      intervalIntegral.integral_congr_ae haelog]
  rw [hmean, hgeom]
  refine geomMean_le_mean v a b hab hvpos (hint.congr_ae (ae_restrict_of_ae hvw.symm))
    (hlog.congr_ae (ae_restrict_of_ae ?_))
  filter_upwards [hvw] with t ht
  rw [ht]

/-! ## Section 3.1: conformal naturality and scale invariance -/

/-- The signed interval average `intervalAvg` is unchanged when its two
endpoints are swapped. -/
private theorem intervalAvg_symm (f : ℝ → ℝ) (p q : ℝ) : intervalAvg f p q = intervalAvg f q p := by
  unfold intervalAvg
  rw [intervalIntegral.integral_symm]
  rcases eq_or_ne p q with h | h
  · simp [h]
  · have hpq : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    field_simp
    ring

/-- Consequently `intervalOscillation` is also symmetric in its endpoints. -/
private theorem intervalOscillation_symm (f : ℝ → ℝ) (p q : ℝ) :
    intervalOscillation f p q = intervalOscillation f q p := by
  unfold intervalOscillation
  rw [intervalAvg_symm f p q, intervalAvg_symm (fun t => |f t - intervalAvg f q p|) p q]

/-- **Claim in the proof of Lemma (Scale Invariance)**: the `BMO` norm is
invariant under a non-degenerate affine change of variable `t ↦ at + b`. -/
theorem bmoNorm_comp_affine (u : ℝ → ℝ) (a b : ℝ) (ha : a ≠ 0) :
    bmoNorm (fun t => u (a * t + b)) = bmoNorm u := by
  have hAvgSub : ∀ (f : ℝ → ℝ) (p q : ℝ), p ≠ q →
      intervalAvg (fun t => f (a * t + b)) p q = intervalAvg f (a * p + b) (a * q + b) := by
    intro f p q hpq
    unfold intervalAvg
    rw [intervalIntegral.integral_comp_mul_add f ha b, smul_eq_mul,
      show a * q + b - (a * p + b) = a * (q - p) by ring]
    have hqp : q - p ≠ 0 := sub_ne_zero.mpr hpq.symm
    field_simp
  have key : ∀ c d : ℝ, c ≠ d →
      intervalOscillation (fun t => u (a * t + b)) c d =
        intervalOscillation u (a * c + b) (a * d + b) := by
    intro c d hcd
    unfold intervalOscillation
    rw [hAvgSub u c d hcd]
    have hfun_eq : (fun t => |u (a * t + b) - intervalAvg u (a * c + b) (a * d + b)|) =
        (fun t => (fun s => |u s - intervalAvg u (a * c + b) (a * d + b)|) (a * t + b)) := rfl
    rw [hfun_eq, hAvgSub (fun s => |u s - intervalAvg u (a * c + b) (a * d + b)|) c d hcd]
  have hminmax : ∀ c d : ℝ, c ≠ d → min c d < max c d := by
    intro c d hcd
    rcases lt_or_gt_of_ne hcd with h | h
    · rwa [min_eq_left h.le, max_eq_right h.le]
    · rwa [min_eq_right h.le, max_eq_left h.le]
  have hval0 : ∀ (f : ℝ → ℝ) (c d : ℝ),
      intervalOscillation f (min c d) (max c d) = intervalOscillation f c d := by
    intro f c d
    rcases le_total c d with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      exact intervalOscillation_symm f d c
  unfold bmoNorm
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨c, d, hcd, hr⟩
    have hne2 : a * c + b ≠ a * d + b := by
      intro h
      exact hcd.ne (mul_left_cancel₀ ha (by linarith))
    refine ⟨min (a * c + b) (a * d + b), max (a * c + b) (a * d + b), hminmax _ _ hne2, ?_⟩
    rw [hval0 u (a * c + b) (a * d + b), ← key c d hcd.ne, hr]
  · rintro ⟨p, q, hpq, hr⟩
    have hac : a * ((p - b) / a) + b = p := by field_simp; ring
    have had : a * ((q - b) / a) + b = q := by field_simp; ring
    have hcd : (p - b) / a ≠ (q - b) / a := by
      intro h
      apply hpq.ne
      have := congrArg (fun x => a * x + b) h
      simpa [hac, had] using this
    refine ⟨min ((p - b) / a) ((q - b) / a), max ((p - b) / a) ((q - b) / a),
      hminmax _ _ hcd, ?_⟩
    rw [hval0 (fun t => u (a * t + b)) ((p - b) / a) ((q - b) / a),
      key ((p - b) / a) ((q - b) / a) hcd, hac, had, hr]

/-- Adding a constant does not change the `BMO` norm. Besides continuity of
`bmoNorm` itself (no hypothesis on `u`), this needs `u` to be locally
integrable: for a pathological non-measurable `u`, `|u|` and `|u + c|` could
have different integrability, which would break the identity. -/
theorem bmoNorm_add_const (u : ℝ → ℝ) (c : ℝ)
    (hu : ∀ p q : ℝ, IntervalIntegrable u volume p q) :
    bmoNorm (fun t => u t + c) = bmoNorm u := by
  have key : ∀ a b : ℝ, a < b →
      intervalOscillation (fun t => u t + c) a b = intervalOscillation u a b := by
    intro a b hab
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    have havg : intervalAvg (fun t => u t + c) a b = intervalAvg u a b + c := by
      unfold intervalAvg
      rw [intervalIntegral.integral_add (hu a b) intervalIntegrable_const,
        intervalIntegral.integral_const, smul_eq_mul]
      field_simp
    unfold intervalOscillation
    rw [havg]
    have hfun_eq : (fun t => |(u t + c) - (intervalAvg u a b + c)|) =
        (fun t => |u t - intervalAvg u a b|) := by
      funext t
      congr 1
      ring
    rw [hfun_eq]
  unfold bmoNorm
  congr 1
  ext r
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, b, hab, hr⟩
    exact ⟨a, b, hab, hr.trans (key a b hab)⟩
  · rintro ⟨a, b, hab, hr⟩
    exact ⟨a, b, hab, hr.trans (key a b hab).symm⟩

/-- **The computation of `log h_z'`**: the logarithmic derivative of the
normalized map differs from `log f' ∘ (t ↦ x + yt)` by the constant
`log((f(x+y) - f(x))/y)`. -/
theorem normalizedMap_log_deriv (f : ℝ → ℝ) (hf : StrictMono f)
    (_hac : LocallyAbsolutelyContinuous f) (x y : ℝ) (hy : 0 < y) (t : ℝ)
    (hpos : 0 < deriv f (x + y * t)) :
    Real.log (deriv (normalizedMap f x y) t) =
      Real.log (deriv f (x + y * t)) - Real.log (y⁻¹ * (f (x + y) - f x)) := by
  have hdf : DifferentiableAt ℝ f (x + y * t) := by
    by_contra hnd
    rw [deriv_zero_of_not_differentiableAt hnd] at hpos
    exact absurd hpos (lt_irrefl 0)
  have hden_pos : 0 < f (x + y) - f x := by
    have := hf (show x < x + y by linarith)
    linarith
  have hu : HasDerivAt (fun s : ℝ => x + y * s) y t := by
    simpa using ((hasDerivAt_id t).const_mul y).const_add x
  have hcomp : HasDerivAt (f ∘ fun s : ℝ => x + y * s) (deriv f (x + y * t) * y) t :=
    HasDerivAt.comp t hdf.hasDerivAt hu
  have hcompderiv : deriv (fun s : ℝ => f (x + y * s)) t = deriv f (x + y * t) * y :=
    hcomp.deriv
  have hderiv : deriv (normalizedMap f x y) t =
      deriv f (x + y * t) * y / (f (x + y) - f x) := by
    unfold normalizedMap
    rw [deriv_div_const, deriv_sub_const, hcompderiv]
  rw [hderiv]
  have hy0 : y ≠ 0 := hy.ne'
  have hyi0 : y⁻¹ ≠ 0 := inv_ne_zero hy0
  have hden0 : f (x + y) - f x ≠ 0 := hden_pos.ne'
  rw [Real.log_div (by positivity) hden0, Real.log_mul hpos.ne' hy0,
    Real.log_mul hyi0 hden0, Real.log_inv]
  ring

/-- The `BMO` norm only sees a function through its integrals over intervals, so it is unchanged
by a modification on a null set. -/
private theorem ps_bmoNorm_congr_ae {g₁ g₂ : ℝ → ℝ} (hg : g₁ =ᵐ[volume] g₂) :
    bmoNorm g₁ = bmoNorm g₂ := by
  have havg : ∀ (k₁ k₂ : ℝ → ℝ), k₁ =ᵐ[volume] k₂ → ∀ a b : ℝ,
      intervalAvg k₁ a b = intervalAvg k₂ a b := by
    intro k₁ k₂ hk a b
    unfold intervalAvg
    rw [intervalIntegral.integral_congr_ae (hk.mono fun x hx _ => hx)]
  have key : ∀ a b : ℝ, intervalOscillation g₁ a b = intervalOscillation g₂ a b := by
    intro a b
    unfold intervalOscillation
    rw [havg g₁ g₂ hg a b]
    apply havg
    filter_upwards [hg] with x hx
    rw [hx]
  unfold bmoNorm
  simp_rw [key]

/-- **Lemma (Scale Invariance of the BMO Norm)**:
`‖log h_z'‖_{BMO(ℝ)} = ‖log f'‖_{BMO(ℝ)}`.

The paper records it without using it later.  Besides `StrictMono f` (so that
`normalizedMap` does not divide by zero) it needs `f' > 0` almost everywhere
and `log f'` locally integrable: `deriv` and `Real.log` take the junk value
`0` at points of non-differentiability and at `0`, and a fat Cantor set on
which `f' = 0` otherwise breaks the identity. -/
theorem bmo_norm_scale_invariance (f : ℝ → ℝ) (hf : StrictMono f)
    (hpos : ∀ᵐ t ∂volume, 0 < deriv f t)
    (hloc : ∀ a b : ℝ, IntervalIntegrable (fun t => Real.log (deriv f t)) volume a b)
    (x y : ℝ) (hy : 0 < y) :
    bmoNorm (fun t => Real.log (deriv (normalizedMap f x y) t)) =
      bmoNorm (fun t => Real.log (deriv f t)) := by
  set U : ℝ → ℝ := fun t => Real.log (deriv f t) with hUdef
  have hD : 0 < f (x + y) - f x := sub_pos.mpr (hf (by linarith))
  -- `h_z' (t) = y f'(x + yt) / (f(x + y) - f(x))` at *every* `t` (both sides vanish where `f` is
  -- not differentiable, since `t ↦ x + yt` is an affine bijection)
  have hderiv : ∀ t : ℝ, deriv (normalizedMap f x y) t =
      y * deriv f (x + y * t) / (f (x + y) - f x) := by
    intro t
    have hcomp : deriv (fun s => f (x + y * s)) t = y * deriv f (x + y * t) := by
      have h1 : deriv (fun s => f (x + y * s)) t = y • deriv (fun s => f (x + s)) (y * t) :=
        deriv_comp_mul_left (f := fun s => f (x + s)) y t
      rw [h1, smul_eq_mul, deriv_comp_const_add]
    unfold normalizedMap
    rw [deriv_div_const, deriv_sub_const, hcomp]
  -- the affine preimage of the null set `{f' ≤ 0}` is null
  have hae_pos : ∀ᵐ t ∂volume, 0 < deriv f (x + y * t) := by
    rw [ae_iff] at hpos ⊢
    change volume ((fun t => y * t) ⁻¹' ((fun s => x + s) ⁻¹' {s | ¬ 0 < deriv f s})) = 0
    rw [Real.volume_preimage_mul_left hy.ne', measure_preimage_add, hpos, mul_zero]
  set c : ℝ := Real.log y - Real.log (f (x + y) - f x) with hcdef
  have hae_eq : (fun t => Real.log (deriv (normalizedMap f x y) t)) =ᵐ[volume]
      fun t => U (y * t + x) + c := by
    filter_upwards [hae_pos] with t ht
    show Real.log (deriv (normalizedMap f x y) t) =
      Real.log (deriv f (y * t + x)) + (Real.log y - Real.log (f (x + y) - f x))
    rw [hderiv t, Real.log_div (mul_pos hy ht).ne' hD.ne', Real.log_mul hy.ne' ht.ne',
      add_comm (y * t) x]
    ring
  have hint_comp : ∀ p q : ℝ, IntervalIntegrable (fun t => U (y * t + x)) volume p q := by
    intro p q
    have h1 := ((hloc (y * p + x) (y * q + x)).comp_add_right x).comp_mul_left (c := y)
    rw [add_sub_cancel_right, add_sub_cancel_right, mul_div_cancel_left₀ p hy.ne',
      mul_div_cancel_left₀ q hy.ne'] at h1
    exact h1
  calc bmoNorm (fun t => Real.log (deriv (normalizedMap f x y) t))
      = bmoNorm (fun t => U (y * t + x) + c) := ps_bmoNorm_congr_ae hae_eq
    _ = bmoNorm (fun t => U (y * t + x)) := bmoNorm_add_const (fun t => U (y * t + x)) c hint_comp
    _ = bmoNorm U := bmoNorm_comp_affine U y x hy.ne'

/-! ## Section 3.2: compactness of normalized quasisymmetric families -/

/-- Real-valued circle average `(2π)⁻¹ ∫₀^{2π} F(e^{iφ}) dφ`. -/
def circleAvgReal (F : Circle → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ φ in (0:ℝ)..(2 * Real.pi), F (Circle.exp φ)

/-- **Step 2b (continuity of the second moment)**: `g ↦ ⨍ g²` is
`2`-Lipschitz for uniform convergence, since
`|⨍ g² - ⨍ f²| = |⨍ (g - f)(g + f)| ≤ 2 ‖g - f‖_∞`. -/
theorem lipschitz_circleAvg_sq (g f : C(Circle, Circle)) :
    ‖circleAvg (fun ζ => (g ζ : ℂ) ^ 2) - circleAvg (fun ζ => (f ζ : ℂ) ^ 2)‖ ≤
      2 * ⨆ ζ : Circle, ‖(g ζ : ℂ) - (f ζ : ℂ)‖ := by
  have hbdd : BddAbove (Set.range (fun ζ : Circle => ‖(g ζ : ℂ) - (f ζ : ℂ)‖)) :=
    (isCompact_range (by fun_prop)).bddAbove
  have hM_ge : ∀ ζ : Circle, ‖(g ζ : ℂ) - (f ζ : ℂ)‖ ≤ ⨆ ζ : Circle, ‖(g ζ : ℂ) - (f ζ : ℂ)‖ :=
    fun ζ => le_ciSup hbdd ζ
  unfold circleAvg
  have hcont_g2 : Continuous (fun φ : ℝ => (g (Circle.exp φ) : ℂ) ^ 2) := by fun_prop
  have hcont_f2 : Continuous (fun φ : ℝ => (f (Circle.exp φ) : ℂ) ^ 2) := by fun_prop
  rw [← mul_sub,
    ← intervalIntegral.integral_sub (hcont_g2.intervalIntegrable 0 (2 * Real.pi))
      (hcont_f2.intervalIntegrable 0 (2 * Real.pi))]
  rw [norm_mul]
  have h2pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hle : ‖∫ φ in (0 : ℝ)..(2 * Real.pi),
        ((g (Circle.exp φ) : ℂ) ^ 2 - (f (Circle.exp φ) : ℂ) ^ 2)‖ ≤
      ∫ φ in (0 : ℝ)..(2 * Real.pi), ‖(g (Circle.exp φ) : ℂ) ^ 2 - (f (Circle.exp φ) : ℂ) ^ 2‖ :=
    intervalIntegral.norm_integral_le_integral_norm h2pi_pos.le
  have hpt : ∀ φ : ℝ, ‖(g (Circle.exp φ) : ℂ) ^ 2 - (f (Circle.exp φ) : ℂ) ^ 2‖ ≤
      2 * ‖(g (Circle.exp φ) : ℂ) - (f (Circle.exp φ) : ℂ)‖ := by
    intro φ
    have hfactor : (g (Circle.exp φ) : ℂ) ^ 2 - (f (Circle.exp φ) : ℂ) ^ 2 =
        ((g (Circle.exp φ) : ℂ) - (f (Circle.exp φ) : ℂ)) *
          ((g (Circle.exp φ) : ℂ) + (f (Circle.exp φ) : ℂ)) := by ring
    rw [hfactor, norm_mul]
    have hsum_le : ‖(g (Circle.exp φ) : ℂ) + (f (Circle.exp φ) : ℂ)‖ ≤ 2 := by
      calc ‖(g (Circle.exp φ) : ℂ) + (f (Circle.exp φ) : ℂ)‖
          ≤ ‖(g (Circle.exp φ) : ℂ)‖ + ‖(f (Circle.exp φ) : ℂ)‖ := norm_add_le _ _
        _ = 2 := by rw [Circle.norm_coe, Circle.norm_coe]; ring
    calc ‖(g (Circle.exp φ) : ℂ) - (f (Circle.exp φ) : ℂ)‖ *
          ‖(g (Circle.exp φ) : ℂ) + (f (Circle.exp φ) : ℂ)‖
        ≤ ‖(g (Circle.exp φ) : ℂ) - (f (Circle.exp φ) : ℂ)‖ * 2 :=
          mul_le_mul_of_nonneg_left hsum_le (norm_nonneg _)
      _ = 2 * ‖(g (Circle.exp φ) : ℂ) - (f (Circle.exp φ) : ℂ)‖ := by ring
  have hint_le : (∫ φ in (0 : ℝ)..(2 * Real.pi),
        ‖(g (Circle.exp φ) : ℂ) ^ 2 - (f (Circle.exp φ) : ℂ) ^ 2‖) ≤
      ∫ _φ in (0 : ℝ)..(2 * Real.pi), 2 * ⨆ ζ : Circle, ‖(g ζ : ℂ) - (f ζ : ℂ)‖ := by
    apply intervalIntegral.integral_mono_on h2pi_pos.le
    · exact (hcont_g2.sub hcont_f2).norm.intervalIntegrable 0 (2 * Real.pi)
    · exact intervalIntegrable_const
    · intro φ _
      calc ‖(g (Circle.exp φ) : ℂ) ^ 2 - (f (Circle.exp φ) : ℂ) ^ 2‖
          ≤ 2 * ‖(g (Circle.exp φ) : ℂ) - (f (Circle.exp φ) : ℂ)‖ := hpt φ
        _ ≤ 2 * ⨆ ζ : Circle, ‖(g ζ : ℂ) - (f ζ : ℂ)‖ :=
            mul_le_mul_of_nonneg_left (hM_ge (Circle.exp φ)) (by norm_num)
  rw [intervalIntegral.integral_const] at hint_le
  have hnorm_2pi_inv : ‖(((2 * Real.pi)⁻¹ : ℝ) : ℂ)‖ = (2 * Real.pi)⁻¹ :=
    Complex.norm_of_nonneg (by positivity)
  rw [hnorm_2pi_inv]
  calc (2 * Real.pi)⁻¹ *
        ‖∫ φ in (0 : ℝ)..(2 * Real.pi), ((g (Circle.exp φ) : ℂ) ^ 2 - (f (Circle.exp φ) : ℂ) ^ 2)‖
      ≤ (2 * Real.pi)⁻¹ *
          ∫ φ in (0 : ℝ)..(2 * Real.pi), ‖(g (Circle.exp φ) : ℂ) ^ 2 - (f (Circle.exp φ) : ℂ) ^ 2‖ :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ ≤ (2 * Real.pi)⁻¹ *
          ((2 * Real.pi - 0) • (2 * ⨆ ζ : Circle, ‖(g ζ : ℂ) - (f ζ : ℂ)‖)) :=
        mul_le_mul_of_nonneg_left hint_le (by positivity)
    _ = 2 * ⨆ ζ : Circle, ‖(g ζ : ℂ) - (f ζ : ℂ)‖ := by
        rw [smul_eq_mul]
        field_simp
        ring

/-! ## Summation lemmas (Section 5) -/

/-- **Exchange of the order of summation**:
`∑_k 4^{-k} ∑_{j≤k} 2^{k-j} a_j = 2 ∑_j 4^{-j} a_j`. -/
theorem sum_exchange_geometric (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hs : Summable fun j => ((4 : ℝ)⁻¹) ^ j * a j) :
    (∑' k : ℕ, ((4 : ℝ)⁻¹) ^ k * ∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (k - j) * a j) =
      2 * ∑' j : ℕ, ((4 : ℝ)⁻¹) ^ j * a j := by
  set c : ℕ → ℝ := fun k => ∑ j ∈ Finset.range (k + 1), (2 : ℝ) ^ (k - j) * a j with hcdef
  set e : ℕ → ℝ := fun k => (4 : ℝ)⁻¹ ^ k * c k with hedef
  set t : ℕ → ℝ := fun j => (4 : ℝ)⁻¹ ^ j * a j with htdef
  set EP : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, e k with hEPdef
  set TP : ℕ → ℝ := fun n => ∑ j ∈ Finset.range n, t j with hTPdef
  have hcnn : ∀ k, 0 ≤ c k := fun k =>
    Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (ha j))
  have henn : ∀ k, 0 ≤ e k := fun k => mul_nonneg (by positivity) (hcnn k)
  have htnn : ∀ j, 0 ≤ t j := fun j => mul_nonneg (by positivity) (ha j)
  have herec : ∀ i : ℕ, e (i + 1) = (1 / 2 : ℝ) * e i + t (i + 1) := by
    intro i
    show (4 : ℝ)⁻¹ ^ (i + 1) * (∑ j ∈ Finset.range (i + 1 + 1), (2 : ℝ) ^ (i + 1 - j) * a j) =
        (1 / 2) * ((4 : ℝ)⁻¹ ^ i * ∑ j ∈ Finset.range (i + 1), (2 : ℝ) ^ (i - j) * a j) +
          (4 : ℝ)⁻¹ ^ (i + 1) * a (i + 1)
    rw [Finset.sum_range_succ]
    have hterm : (2 : ℝ) ^ (i + 1 - (i + 1)) = 1 := by simp
    rw [hterm, one_mul]
    have hsum_eq : (∑ j ∈ Finset.range (i + 1), (2 : ℝ) ^ (i + 1 - j) * a j) =
        2 * ∑ j ∈ Finset.range (i + 1), (2 : ℝ) ^ (i - j) * a j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have hexp : i + 1 - j = (i - j) + 1 := by omega
      rw [hexp, pow_succ]
      ring
    rw [hsum_eq]
    ring
  have hrec : ∀ n : ℕ, EP (n + 1) = (1 / 2 : ℝ) * EP n + TP (n + 1) := by
    intro n
    have hLHSpeel := Finset.sum_range_succ' e n
    have hRHSpeel := Finset.sum_range_succ' t n
    show (∑ i ∈ Finset.range (n + 1), e i) =
        (1 / 2) * (∑ i ∈ Finset.range n, e i) + ∑ i ∈ Finset.range (n + 1), t i
    rw [hLHSpeel, hRHSpeel]
    have hsum2 : (∑ i ∈ Finset.range n, e (i + 1)) =
        ∑ i ∈ Finset.range n, ((1 / 2 : ℝ) * e i + t (i + 1)) :=
      Finset.sum_congr rfl (fun i _ => herec i)
    rw [hsum2, Finset.sum_add_distrib, ← Finset.mul_sum]
    have he0 : e 0 = a 0 := by show (4 : ℝ)⁻¹ ^ 0 * (∑ j ∈ Finset.range 1, (2 : ℝ) ^ (0 - j) * a j) = a 0; simp
    have ht0 : t 0 = a 0 := by show (4 : ℝ)⁻¹ ^ 0 * a 0 = a 0; simp
    rw [he0, ht0]
    ring
  have hTP_tendsto : Filter.Tendsto TP Filter.atTop (nhds (∑' j, t j)) := hs.hasSum.tendsto_sum_nat
  have hTP_le : ∀ n, TP n ≤ ∑' j, t j := fun n => hs.sum_le_tsum _ (fun j _ => htnn j)
  have hEPTP : ∀ m : ℕ, EP m ≤ 2 * TP m := by
    intro m
    cases m with
    | zero => simp [hEPdef, hTPdef]
    | succ n => exact weighted_dyadic_sum_le a ha n
  have hEP_le : ∀ m, EP m ≤ 2 * ∑' j, t j := fun m => (hEPTP m).trans (by linarith [hTP_le m])
  have hEP_mono : Monotone EP := by
    apply monotone_nat_of_le_succ
    intro n
    have hen := henn n
    show (∑ k ∈ Finset.range n, e k) ≤ ∑ k ∈ Finset.range (n + 1), e k
    rw [Finset.sum_range_succ]
    linarith
  have hEP_bdd : BddAbove (Set.range EP) := ⟨2 * ∑' j, t j, fun x ⟨n, hn⟩ => hn ▸ hEP_le n⟩
  have hL : Filter.Tendsto EP Filter.atTop (nhds (⨆ n, EP n)) := tendsto_atTop_ciSup hEP_mono hEP_bdd
  set L : ℝ := ⨆ n, EP n with hLdef
  have hEsum : HasSum e L := (hasSum_iff_tendsto_nat_of_nonneg henn L).mpr hL
  have hL_eq_tsum : (∑' k, e k) = L := hEsum.tsum_eq
  have hTP1_tendsto : Filter.Tendsto (fun n => TP (n + 1)) Filter.atTop (nhds (∑' j, t j)) :=
    hTP_tendsto.comp (Filter.tendsto_add_atTop_nat 1)
  have hEP1_tendsto : Filter.Tendsto (fun n => EP (n + 1)) Filter.atTop (nhds L) :=
    hL.comp (Filter.tendsto_add_atTop_nat 1)
  have hrec_tendsto : Filter.Tendsto (fun n => (1 / 2 : ℝ) * EP n + TP (n + 1)) Filter.atTop
      (nhds ((1 / 2 : ℝ) * L + ∑' j, t j)) := (hL.const_mul (1 / 2 : ℝ)).add hTP1_tendsto
  have hlimeq : L = (1 / 2 : ℝ) * L + ∑' j, t j := by
    have heq1 : (fun n => EP (n + 1)) = (fun n => (1 / 2 : ℝ) * EP n + TP (n + 1)) := funext hrec
    rw [heq1] at hEP1_tendsto
    exact tendsto_nhds_unique hEP1_tendsto hrec_tendsto
  have hLval : L = 2 * ∑' j, t j := by linarith
  rw [hL_eq_tsum]
  exact hLval

/-! ## Section 8: the beta-number Carleson estimate -/

/-- The comparison constant `C₂ := C₁ / (8 (1 - 2^{-σ/2}))`. -/
def comparisonConst (C₁ σ : ℝ) : ℝ := C₁ / (8 * (1 - 2 ^ (-σ / 2)))

/-- The offset `λ_{n,j} = -1 + (2j + 1) 2^{-n} ∈ (-1, 1)` locating the centre
of the `j`-th level-`n` dyadic subinterval of `I(x, y)`. -/
def dyadicShift (n j : ℕ) : ℝ := -1 + (2 * j + 1) * ((2 : ℝ)⁻¹) ^ n

/-- **The dyadic subintervals of `I(x, y)`**:
`L_{n,j} = I(x + λ_{n,j} y, 2^{-n} y)`. -/
theorem dyadic_subinterval_eq (x y : ℝ) (n j : ℕ) :
    dyadicCenter (x - y) (x + y) n j = x + dyadicShift n j * y ∧
      dyadicHalfLength (x - y) (x + y) n = ((2 : ℝ)⁻¹) ^ n * y := by
  unfold dyadicCenter dyadicHalfLength dyadicShift
  rw [← inv_pow]
  constructor
  · ring
  · ring

/-- **(A1) applied to a dyadic subinterval**:
`|h(L_{n,j})| / |h(I)| = w(L_{n,j}) / w(I) ≤ C₁ 2^{-nσ}`. -/
theorem a1_dyadic_ratio (h : ℝ → ℝ) (_hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (C₁ σ : ℝ) (_hC₁ : 1 ≤ C₁) (_hσ : 0 < σ)
    (_hσ1 : σ ≤ 1) (hw : WeightA1 (deriv h) C₁ σ) (x y : ℝ) (hy : 0 < y) (n j : ℕ)
    (hj : j < 2 ^ n) :
    dyadicImageLength h (x - y) (x + y) n j / (h (x + y) - h (x - y)) ≤
      C₁ * (2 : ℝ) ^ (-(n : ℝ) * σ) := by
  have hFTC : ∀ p q : ℝ, p < q → (∫ t in Set.Icc p q, deriv h t) = h q - h p := by
    intro p q hpq
    have himg := imageLength_eq_mean h hac p q hpq
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hpq.le]
    unfold weightMean intervalAvg at himg
    have hqp : q - p ≠ 0 := sub_ne_zero.mpr hpq.ne'
    field_simp at himg
    linarith [himg]
  have hab : x - y < x + y := by linarith
  have h2n_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hba_pos : (0 : ℝ) < (x + y) - (x - y) := by linarith
  set step : ℝ := ((x + y) - (x - y)) * ((2 : ℝ) ^ n)⁻¹ with hstepdef
  have hstep_pos : 0 < step := by rw [hstepdef]; positivity
  set p : ℝ := (x - y) + (j : ℝ) * step with hpdef
  set q : ℝ := (x - y) + ((j : ℝ) + 1) * step with hqdef
  have hpq : p < q := by rw [hpdef, hqdef]; nlinarith [hstep_pos]
  have himg_eq : dyadicImageLength h (x - y) (x + y) n j = h q - h p := by
    unfold dyadicImageLength
    rw [hpdef, hqdef, hstepdef]
  have hap : (x - y) ≤ p := by
    rw [hpdef]; nlinarith [Nat.cast_nonneg (α := ℝ) j, hstep_pos.le]
  have hqb : q ≤ x + y := by
    rw [hqdef, hstepdef]
    have hjn : (j : ℝ) + 1 ≤ (2 : ℝ) ^ n := by exact_mod_cast hj
    have hfactor_nonneg : (0 : ℝ) ≤ ((x + y) - (x - y)) * ((2 : ℝ) ^ n)⁻¹ := by positivity
    have hmul_le : ((j : ℝ) + 1) * (((x + y) - (x - y)) * ((2 : ℝ) ^ n)⁻¹) ≤
        (2 : ℝ) ^ n * (((x + y) - (x - y)) * ((2 : ℝ) ^ n)⁻¹) :=
      mul_le_mul_of_nonneg_right hjn hfactor_nonneg
    have heq2 : (x - y) + (2 : ℝ) ^ n * (((x + y) - (x - y)) * ((2 : ℝ) ^ n)⁻¹) = x + y := by
      field_simp; ring
    linarith [hmul_le, heq2]
  have hEsub : Set.Icc p q ⊆ Set.Icc (x - y) (x + y) := Set.Icc_subset_Icc hap hqb
  obtain ⟨hwpos, hwA1⟩ := hw
  have hkey := hwA1 (x - y) (x + y) hab (Set.Icc p q) measurableSet_Icc hEsub
  rw [hFTC p q hpq, hFTC (x - y) (x + y) hab] at hkey
  rw [himg_eq]
  have hvolE : (volume (Set.Icc p q)).toReal = q - p := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hpq.le)]
  have hqp_eq : q - p = step := by rw [hpdef, hqdef]; ring
  have hratio_eq : (volume (Set.Icc p q)).toReal / ((x + y) - (x - y)) = ((2 : ℝ) ^ n)⁻¹ := by
    rw [hvolE, hqp_eq, hstepdef]
    have hba_ne : ((x + y) - (x - y)) ≠ 0 := hba_pos.ne'
    field_simp
  rw [hratio_eq] at hkey
  have hbase_eq : ((2 : ℝ) ^ n)⁻¹ = (2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast]
  rw [hbase_eq, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)] at hkey
  exact hkey

/-- For `h` strictly increasing and `v > 0`, `ε_h(u, v) ∈ [-1, 1]`: writing
`A = h(u+v) - h(u) > 0` and `B = h(u) - h(u-v) > 0`, the numerator is `A - B`
and the denominator is `A + B`, so `|A - B| ≤ A + B`. -/
private lemma abs_eps_le_one_general (h : ℝ → ℝ) (hh : StrictMono h) (u v : ℝ) (hv : 0 < v) :
    |eps h u v| ≤ 1 := by
  have hA : (0 : ℝ) < h (u + v) - h u := sub_pos.mpr (hh (by linarith))
  have hB : (0 : ℝ) < h u - h (u - v) := sub_pos.mpr (hh (by linarith))
  unfold eps
  have hnum : h (u + v) + h (u - v) - 2 * h u = (h (u + v) - h u) - (h u - h (u - v)) := by ring
  have hden : h (u + v) - h (u - v) = (h (u + v) - h u) + (h u - h (u - v)) := by ring
  rw [hnum, hden, abs_div,
    abs_of_pos (show (0 : ℝ) < (h (u + v) - h u) + (h u - h (u - v)) by linarith),
    div_le_one (by linarith), abs_le]
  constructor <;> linarith

/-- **The pointwise bound behind Theorem (Comparison)**: combining the squared
tent expansion with (A1),
`β_h(x,y)² ≤ (C₁/8) ∑_n 2^{-n(1 - θ + σ)} ∑_j ε_h(x + λ_{n,j} y, 2^{-n} y)²`
with `θ = σ/2`. -/
theorem beta_sq_pointwise_bound (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hac : LocallyAbsolutelyContinuous h) (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hw : WeightA1 (deriv h) C₁ σ) (x y : ℝ) (hy : 0 < y) :
    betaPt h x y ^ 2 ≤
      C₁ / 8 * ∑' n : ℕ, (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) *
        ∑ j ∈ Finset.range (2 ^ n),
          eps h (x + dyadicShift n j * y) (((2 : ℝ)⁻¹) ^ n * y) ^ 2 := by
  have hxy : x - y < x + y := by linarith
  have hθ : (0 : ℝ) < σ / 2 := by linarith
  have hθ1 : σ / 2 < 1 := by linarith
  have htsq := tent_squared h hh hc (σ / 2) hθ hθ1 (x - y) (x + y) hxy
  set e : ℕ → ℕ → ℝ := fun n j => eps h (x + dyadicShift n j * y) (((2 : ℝ)⁻¹) ^ n * y) with hedef
  have hrw : ∀ n j : ℕ,
      eps h (dyadicCenter (x - y) (x + y) n j) (dyadicHalfLength (x - y) (x + y) n) = e n j := by
    intro n j
    obtain ⟨h1, h2⟩ := dyadic_subinterval_eq x y n j
    rw [h1, h2]
  simp only [hrw] at htsq
  have hv_pos : ∀ n : ℕ, (0 : ℝ) < ((2 : ℝ)⁻¹) ^ n * y := fun n => by positivity
  have he_sq_le_one : ∀ n j : ℕ, e n j ^ 2 ≤ 1 := fun n j =>
    (sq_le_one_iff_abs_le_one (e n j)).mpr
      (abs_eps_le_one_general h hh (x + dyadicShift n j * y) (((2 : ℝ)⁻¹) ^ n * y) (hv_pos n))
  have hratio_le : ∀ n j : ℕ, j < 2 ^ n →
      dyadicImageLength h (x - y) (x + y) n j / (h (x + y) - h (x - y)) ≤
        C₁ * (2 : ℝ) ^ (-(n : ℝ) * σ) :=
    fun n j hj => a1_dyadic_ratio h hh hac C₁ σ hC₁ hσ hσ1 hw x y hy n j hj
  have hratio_nonneg : ∀ n j : ℕ,
      (0 : ℝ) ≤ dyadicImageLength h (x - y) (x + y) n j / (h (x + y) - h (x - y)) := by
    intro n j
    unfold dyadicImageLength
    have hstep_nonneg : (0 : ℝ) ≤ ((x + y) - (x - y)) * ((2 : ℝ) ^ n)⁻¹ := by positivity
    apply div_nonneg
    · apply sub_nonneg.mpr
      apply hh.monotone
      nlinarith [hstep_nonneg]
    · linarith [hh hxy]
  have hterm_le : ∀ n j : ℕ, j < 2 ^ n →
      dyadicImageLength h (x - y) (x + y) n j / (h (x + y) - h (x - y)) * e n j ^ 2 ≤
        C₁ * (2 : ℝ) ^ (-(n : ℝ) * σ) * e n j ^ 2 :=
    fun n j hj => mul_le_mul_of_nonneg_right (hratio_le n j hj) (sq_nonneg _)
  have hsum_n_le : ∀ n : ℕ,
      ∑ j ∈ Finset.range (2 ^ n),
          dyadicImageLength h (x - y) (x + y) n j / (h (x + y) - h (x - y)) * e n j ^ 2 ≤
        ∑ j ∈ Finset.range (2 ^ n), C₁ * (2 : ℝ) ^ (-(n : ℝ) * σ) * e n j ^ 2 := fun n =>
    Finset.sum_le_sum (fun j hj => hterm_le n j (Finset.mem_range.mp hj))
  have hsum_n_eq : ∀ n : ℕ,
      ∑ j ∈ Finset.range (2 ^ n), C₁ * (2 : ℝ) ^ (-(n : ℝ) * σ) * e n j ^ 2 =
        C₁ * (2 : ℝ) ^ (-(n : ℝ) * σ) * ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2 := fun n => by
    rw [Finset.mul_sum]
  have hAB : ∀ n : ℕ,
      (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2)) * (2 : ℝ) ^ (-(n : ℝ) * σ) =
        (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) := by
    intro n
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have htermwise : ∀ n : ℕ,
      (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2)) *
          ∑ j ∈ Finset.range (2 ^ n),
            dyadicImageLength h (x - y) (x + y) n j / (h (x + y) - h (x - y)) * e n j ^ 2 ≤
        C₁ * ((2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2) := by
    intro n
    have hApos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    calc (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2)) *
            ∑ j ∈ Finset.range (2 ^ n),
              dyadicImageLength h (x - y) (x + y) n j / (h (x + y) - h (x - y)) * e n j ^ 2
        ≤ (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2)) *
            ∑ j ∈ Finset.range (2 ^ n), C₁ * (2 : ℝ) ^ (-(n : ℝ) * σ) * e n j ^ 2 :=
          mul_le_mul_of_nonneg_left (hsum_n_le n) hApos
      _ = (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2)) *
            (C₁ * (2 : ℝ) ^ (-(n : ℝ) * σ) * ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2) := by
          rw [hsum_n_eq]
      _ = C₁ * ((2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2)) * (2 : ℝ) ^ (-(n : ℝ) * σ) *
            ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2) := by ring
      _ = C₁ * ((2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2) := by
          rw [hAB]
  have hT_le : ∀ n : ℕ, ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2 ≤ (2 ^ n : ℝ) := by
    intro n
    calc ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2
        ≤ ∑ _j ∈ Finset.range (2 ^ n), (1 : ℝ) := Finset.sum_le_sum (fun j _ => he_sq_le_one n j)
      _ = (2 ^ n : ℝ) := by simp
  have hmaj_bound : ∀ n : ℕ,
      C₁ * ((2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2) ≤
        C₁ * (2 : ℝ) ^ (-(n : ℝ) * (σ / 2)) := by
    intro n
    have hBnn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) :=
      (Real.rpow_pos_of_pos (by norm_num) _).le
    have hstep1 : (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2 ≤
        (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * (2 ^ n : ℝ) :=
      mul_le_mul_of_nonneg_left (hT_le n) hBnn
    have hcalc : (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * (2 ^ n : ℝ) =
        (2 : ℝ) ^ (-(n : ℝ) * (σ / 2)) := by
      rw [show (2 ^ n : ℝ) = (2 : ℝ) ^ (n : ℝ) from (Real.rpow_natCast 2 n).symm,
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    calc C₁ * ((2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2)
        ≤ C₁ * ((2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * (2 ^ n : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep1 (by linarith)
      _ = C₁ * (2 : ℝ) ^ (-(n : ℝ) * (σ / 2)) := by rw [hcalc]
  have hmaj_summable : Summable (fun n : ℕ => C₁ * (2 : ℝ) ^ (-(n : ℝ) * (σ / 2))) := by
    have heq : ∀ n : ℕ, (2 : ℝ) ^ (-(n : ℝ) * (σ / 2)) = ((2 : ℝ) ^ (-(σ / 2))) ^ n := by
      intro n
      rw [show -(n : ℝ) * (σ / 2) = -(σ / 2) * (n : ℝ) by ring, Real.rpow_mul (by norm_num),
        Real.rpow_natCast]
    simp_rw [heq]
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (Real.rpow_pos_of_pos (by norm_num) _).le
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  have hC₁_nonneg : (0 : ℝ) ≤ C₁ := by linarith
  have hg_nonneg : ∀ n : ℕ,
      (0 : ℝ) ≤
        C₁ * ((2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2) := by
    intro n
    apply mul_nonneg hC₁_nonneg
    apply mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hmaj_summable2 : Summable (fun n : ℕ =>
      C₁ * ((2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) * ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2)) :=
    Summable.of_nonneg_of_le hg_nonneg hmaj_bound hmaj_summable
  have hmin_nonneg : ∀ n : ℕ,
      (0 : ℝ) ≤ (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2)) *
        ∑ j ∈ Finset.range (2 ^ n),
          dyadicImageLength h (x - y) (x + y) n j / (h (x + y) - h (x - y)) * e n j ^ 2 := by
    intro n
    apply mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hratio_nonneg n j) (sq_nonneg _))
  have hmin_summable : Summable (fun n : ℕ =>
      (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2)) *
        ∑ j ∈ Finset.range (2 ^ n),
          dyadicImageLength h (x - y) (x + y) n j / (h (x + y) - h (x - y)) * e n j ^ 2) :=
    Summable.of_nonneg_of_le hmin_nonneg htermwise hmaj_summable2
  have hfinal := Summable.tsum_le_tsum htermwise hmin_summable hmaj_summable2
  show beta h (x - y) (x + y) ^ 2 ≤
      C₁ / 8 * ∑' n : ℕ, (2 : ℝ) ^ (-(n : ℝ) * (1 - σ / 2 + σ)) *
        ∑ j ∈ Finset.range (2 ^ n), e n j ^ 2
  refine htsq.trans ?_
  rw [tsum_mul_left] at hfinal
  nlinarith [hfinal]

/-- **The `dy/y = dY/Y` scale invariance**: for `k > 0`, substituting `Y = k y`
in `∫ (G(ky))²/y dy` over `(0, L]` gives `∫ G(Y)²/Y dY` over `(0, kL]`. -/
private lemma lintegral_Ioc_y_scale (k : ℝ) (hk : 0 < k) (L : ℝ) (G : ℝ → ℝ)
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

/-- Translation invariance of the Lebesgue set-lintegral over `Ioc`. -/
private lemma lintegral_Ioc_x_shift (s a b : ℝ) (H : ℝ → ENNReal) (hH : Measurable H) :
    ∫⁻ x in Set.Ioc a b, H (x + s) = ∫⁻ x' in Set.Ioc (a + s) (b + s), H x' := by
  have hpre : (fun x : ℝ => x + s) ⁻¹' (Set.Ioc (a + s) (b + s)) = Set.Ioc a b := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  have hmap : Measure.map (fun x : ℝ => x + s) volume = volume := map_add_right_eq_self volume s
  have hkey := setLIntegral_map (μ := volume) (f := H) (g := fun x : ℝ => x + s)
      (measurableSet_Ioc (a := a + s) (b := b + s)) hH (measurable_id.add_const s)
  rw [hmap, hpre] at hkey
  exact hkey.symm

/-- Tonelli decomposition of the box `lintegral` into an iterated `lintegral`. -/
private lemma carlesonBoxLIntegral_eq_iter (F : ℝ → ℝ → ℝ)
    (hFm : Measurable fun p : ℝ × ℝ => F p.1 p.2) (a b : ℝ) :
    carlesonBoxLIntegral F a b =
      ∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a), ENNReal.ofReal ((F x y) ^ 2 / y) := by
  have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal ((F p.1 p.2) ^ 2 / p.2) :=
    ((hFm.pow_const 2).div measurable_snd).ennreal_ofReal
  unfold carlesonBoxLIntegral carlesonBox
  rw [Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict,
    MeasureTheory.lintegral_prod _ hg.aemeasurable]

/-- **Measure invariance of `Ξ_{n,j}(x, y) = (x + λ_{n,j} y, 2^{-n} y)`** (`ℝ≥0∞`-valued form):
it is linear with Jacobian `2^{-n}`, hence preserves `dx dy / y`, and it maps `Q_J` into `Q_{3J}`.
This holds unconditionally (no integrability side condition), unlike the Bochner-valued form
below, since the `ℝ≥0∞`-valued box `lintegral` has no junk value. -/
private theorem carlesonBoxLIntegral_shift_scale_le (F : ℝ → ℝ → ℝ)
    (hFm : Measurable fun p : ℝ × ℝ => F p.1 p.2) (c k : ℝ) (hk : 0 < k) (hk1 : k ≤ 1)
    (hc : |c| ≤ 1) (a b : ℝ) (hab : a < b) :
    carlesonBoxLIntegral (fun x y => F (x + c * y) (k * y)) a b ≤
      carlesonBoxLIntegral F (a - (b - a)) (b + (b - a)) := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hFmshift : Measurable fun p : ℝ × ℝ => F (p.1 + c * p.2) (k * p.2) :=
    hFm.comp ((measurable_fst.add ((measurable_const_mul c).comp measurable_snd)).prodMk
      ((measurable_const_mul k).comp measurable_snd))
  rw [carlesonBoxLIntegral_eq_iter _ hFmshift]
  have hinner : ∀ x : ℝ,
      (∫⁻ y in Set.Ioc (0:ℝ) (b - a), ENNReal.ofReal ((F (x + c * y) (k * y)) ^ 2 / y)) =
        ∫⁻ Y in Set.Ioc (0:ℝ) (k * (b - a)),
          ENNReal.ofReal ((F (x + (c / k) * Y) Y) ^ 2 / Y) := by
    intro x
    have hGmeas : Measurable fun Y : ℝ => F (x + c / k * Y) Y :=
      hFm.comp ((measurable_const.add (measurable_const_mul (c / k))).prodMk measurable_id)
    have hkey := lintegral_Ioc_y_scale k hk (b - a) (fun Y => F (x + c / k * Y) Y) hGmeas
    have hpt : ∀ y : ℝ,
        F (x + c / k * (k * y)) (k * y) = F (x + c * y) (k * y) := by
      intro y
      have : x + c / k * (k * y) = x + c * y := by field_simp
      rw [this]
    simp_rw [hpt] at hkey
    exact hkey
  simp_rw [hinner]
  have hswap1 : (∫⁻ x in Set.Ioc a b, ∫⁻ Y in Set.Ioc (0:ℝ) (k * (b - a)),
        ENNReal.ofReal ((F (x + c / k * Y) Y) ^ 2 / Y)) =
      ∫⁻ Y in Set.Ioc (0:ℝ) (k * (b - a)), ∫⁻ x in Set.Ioc a b,
        ENNReal.ofReal ((F (x + c / k * Y) Y) ^ 2 / Y) := by
    apply lintegral_lintegral_swap
    apply Measurable.aemeasurable
    apply Measurable.ennreal_ofReal
    exact ((hFm.comp ((measurable_fst.add
      ((measurable_const_mul (c/k)).comp measurable_snd)).prodMk measurable_snd)).pow_const 2).div
      measurable_snd
  rw [hswap1]
  have houter_bound : ∀ Y ∈ Set.Ioc (0:ℝ) (k * (b - a)),
      (∫⁻ x in Set.Ioc a b, ENNReal.ofReal ((F (x + c / k * Y) Y) ^ 2 / Y)) ≤
        ∫⁻ x' in Set.Ioc (a - (b - a)) (b + (b - a)), ENNReal.ofReal ((F x' Y) ^ 2 / Y) := by
    intro Y hY
    have hHmeas : Measurable fun x' : ℝ => ENNReal.ofReal ((F x' Y) ^ 2 / Y) :=
      ((hFm.comp (measurable_id.prodMk measurable_const)).pow_const 2).div
        measurable_const |>.ennreal_ofReal
    have hshift := lintegral_Ioc_x_shift (c / k * Y) a b
      (fun x' => ENNReal.ofReal ((F x' Y) ^ 2 / Y)) hHmeas
    rw [hshift]
    have hbound : |c / k * Y| ≤ b - a := by
      rw [show c / k * Y = c * Y / k by ring, abs_le]
      have h1 := abs_le.mp hc
      constructor
      · rw [le_div_iff₀ hk]
        nlinarith [h1.1, h1.2, hY.1, hY.2]
      · rw [div_le_iff₀ hk]
        nlinarith [h1.1, h1.2, hY.1, hY.2]
    obtain ⟨hb1, hb2⟩ := abs_le.mp hbound
    apply lintegral_mono_set
    apply Set.Ioc_subset_Ioc <;> linarith
  have hstep2 : (∫⁻ Y in Set.Ioc (0:ℝ) (k * (b - a)), ∫⁻ x in Set.Ioc a b,
        ENNReal.ofReal ((F (x + c / k * Y) Y) ^ 2 / Y)) ≤
      ∫⁻ Y in Set.Ioc (0:ℝ) (k * (b - a)), ∫⁻ x' in Set.Ioc (a - (b - a)) (b + (b - a)),
        ENNReal.ofReal ((F x' Y) ^ 2 / Y) :=
    setLIntegral_mono' measurableSet_Ioc houter_bound
  refine hstep2.trans ?_
  have hYdom : (Set.Ioc (0:ℝ) (k * (b - a))) ⊆ Set.Ioc (0:ℝ) (3 * (b - a)) := by
    apply Set.Ioc_subset_Ioc_right
    nlinarith
  have hstep3 := lintegral_mono_set (μ := volume)
    (f := fun Y => ∫⁻ x' in Set.Ioc (a - (b - a)) (b + (b - a)),
      ENNReal.ofReal ((F x' Y) ^ 2 / Y)) hYdom
  refine hstep3.trans ?_
  have hswap2 : (∫⁻ Y in Set.Ioc (0:ℝ) (3 * (b - a)), ∫⁻ x' in Set.Ioc (a - (b - a)) (b + (b - a)),
        ENNReal.ofReal ((F x' Y) ^ 2 / Y)) =
      ∫⁻ x' in Set.Ioc (a - (b - a)) (b + (b - a)), ∫⁻ Y in Set.Ioc (0:ℝ) (3 * (b - a)),
        ENNReal.ofReal ((F x' Y) ^ 2 / Y) := by
    apply lintegral_lintegral_swap
    apply Measurable.aemeasurable
    apply Measurable.ennreal_ofReal
    exact ((hFm.comp (Measurable.prodMk measurable_snd measurable_fst)).pow_const 2).div
      measurable_fst
  rw [hswap2]
  have hboxeq : b + (b - a) - (a - (b - a)) = 3 * (b - a) := by ring
  rw [carlesonBoxLIntegral_eq_iter F hFm, hboxeq]

/-- **Link between the Bochner and `ℝ≥0∞`-valued box integrals**: when the box `lintegral`
is finite, the (potentially junk-valued) Bochner `carlesonBoxIntegral` agrees with its honest
value, the `toReal` of the `lintegral`. -/
private theorem carlesonBoxIntegral_eq_toReal_lintegral (F : ℝ → ℝ → ℝ)
    (hFm : Measurable fun p : ℝ × ℝ => F p.1 p.2)
    (a b : ℝ) (hab : a < b) (hfin : carlesonBoxLIntegral F a b ≠ ⊤) :
    carlesonBoxIntegral F a b = (carlesonBoxLIntegral F a b).toReal := by
  have hL : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hmeas : Measurable fun p : ℝ × ℝ => (F p.1 p.2) ^ 2 / p.2 := (hFm.pow_const 2).div
    measurable_snd
  have hbox : MeasurableSet (carlesonBox a b) := measurableSet_Ioc.prod measurableSet_Ioc
  have hf0 : ∀ p ∈ carlesonBox a b, (0 : ℝ) ≤ (F p.1 p.2) ^ 2 / p.2 := fun p hp =>
    div_nonneg (sq_nonneg _) (Set.mem_prod.mp hp).2.1.le
  have hfi : HasFiniteIntegral (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2 / p.2)
      (volume.restrict (carlesonBox a b)) := by
    rw [hasFiniteIntegral_iff_enorm]
    have hae : Filter.EventuallyEq (MeasureTheory.ae (volume.restrict (carlesonBox a b)))
        (fun p : ℝ × ℝ => ‖(F p.1 p.2) ^ 2 / p.2‖ₑ)
        (fun p => ENNReal.ofReal ((F p.1 p.2) ^ 2 / p.2)) := by
      show ∀ᵐ p ∂(volume.restrict (carlesonBox a b)), _ = _
      rw [ae_restrict_iff' hbox]
      exact Filter.Eventually.of_forall fun p hp => by
        show ‖(F p.1 p.2) ^ 2 / p.2‖ₑ = ENNReal.ofReal ((F p.1 p.2) ^ 2 / p.2)
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hf0 p hp)]
    rw [lintegral_congr_ae hae]
    exact hfin.lt_top
  have hint : Integrable (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2 / p.2)
      (volume.restrict (carlesonBox a b)) := ⟨hmeas.aestronglyMeasurable, hfi⟩
  have hint' : Integrable (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2 / p.2)
      ((volume.restrict (Set.Ioc a b)).prod (volume.restrict (Set.Ioc 0 (b - a)))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ, ← carlesonBox]
    exact hint
  have hiter : (∫ x in Set.Ioc a b, ∫ y in Set.Ioc 0 (b - a), (F x y) ^ 2 / y) =
      ∫ p in carlesonBox a b, (F p.1 p.2) ^ 2 / p.2 := by
    rw [carlesonBox, Measure.volume_eq_prod ℝ ℝ, ← Measure.prod_restrict]
    exact (MeasureTheory.integral_prod _ hint').symm
  unfold carlesonBoxIntegral
  rw [intervalIntegral.integral_of_le hab.le,
    setIntegral_congr_fun measurableSet_Ioc (fun x _ => intervalIntegral.integral_of_le hL.le),
    hiter,
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      ((ae_restrict_iff' hbox).mpr (Filter.Eventually.of_forall hf0))
      hint.aestronglyMeasurable]
  rfl

/-- **Measure invariance of `Ξ_{n,j}(x, y) = (x + λ_{n,j} y, 2^{-n} y)`**: it
is linear with Jacobian `2^{-n}`, hence preserves `dx dy / y`, and it maps
`Q_J` into `Q_{3J}`.

Besides `hF` (used for `carlesonBoxIntegral_eq_toReal_lintegral`'s `Bochner = toReal ∘ lintegral`
identity, applied to both sides), this needs `F` jointly measurable (`hFm`) and the *target* box
integral to be genuinely finite (`hfin`): the Bochner-valued `carlesonBoxIntegral` silently
evaluates to the junk value `0` when its integrand fails to be Lebesgue-integrable (unlike the
`ℝ≥0∞`-valued `carlesonBoxLIntegral`, proved unconditionally above as
`carlesonBoxLIntegral_shift_scale_le`), so without `hfin` the comparison could fail for a
pathological non-integrable `F`. -/
theorem carlesonBoxIntegral_dyadicShift (F : ℝ → ℝ → ℝ) (_hF : ∀ x y, 0 ≤ F x y)
    (hFm : Measurable fun p : ℝ × ℝ => F p.1 p.2)
    (n j : ℕ) (hj : j < 2 ^ n) (a b : ℝ) (hab : a < b)
    (hfin : carlesonBoxLIntegral F (a - (b - a)) (b + (b - a)) ≠ ⊤) :
    carlesonBoxIntegral
        (fun x y => F (x + dyadicShift n j * y) (((2 : ℝ)⁻¹) ^ n * y)) a b ≤
      carlesonBoxIntegral F (a - (b - a)) (b + (b - a)) := by
  set c : ℝ := dyadicShift n j with hcdef
  set k : ℝ := ((2 : ℝ)⁻¹) ^ n with hkdef
  have hk : (0 : ℝ) < k := by rw [hkdef]; positivity
  have hk1 : k ≤ 1 := by rw [hkdef]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hc : |c| ≤ 1 := by
    rw [hcdef, dyadicShift]
    have hjn : (j : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
      have h2 : (j + 1 : ℕ) ≤ 2 ^ n := hj
      calc (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h2
        _ = (2 : ℝ) ^ n := by push_cast; ring
    have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ (2 * (j : ℝ) + 1) * ((2 : ℝ)⁻¹) ^ n := by positivity
      linarith
    · have hstep : (2 * (j : ℝ) + 1) * ((2 : ℝ)⁻¹) ^ n ≤ 2 := by
        rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hpow_pos]
        linarith
      linarith
  have hFmshift : Measurable fun p : ℝ × ℝ => F (p.1 + c * p.2) (k * p.2) :=
    hFm.comp ((measurable_fst.add ((measurable_const_mul c).comp measurable_snd)).prodMk
      ((measurable_const_mul k).comp measurable_snd))
  have hlin_le := carlesonBoxLIntegral_shift_scale_le F hFm c k hk hk1 hc a b hab
  have hlin_fin : carlesonBoxLIntegral (fun x y => F (x + c * y) (k * y)) a b ≠ ⊤ :=
    (lt_of_le_of_lt hlin_le hfin.lt_top).ne
  rw [carlesonBoxIntegral_eq_toReal_lintegral _ hFmshift a b hab hlin_fin,
    carlesonBoxIntegral_eq_toReal_lintegral F hFm (a - (b - a)) (b + (b - a)) (by linarith) hfin]
  exact ENNReal.toReal_mono hfin hlin_le

/-- **The geometric series of Theorem (Comparison)**:
`∑_n 2^n 2^{-n(1 - σ/2 + σ)} = ∑_n 2^{-nσ/2} = (1 - 2^{-σ/2})⁻¹`, giving
`C₂ = C₁ / (8(1 - 2^{-σ/2}))`. -/
theorem comparisonConst_geometric (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (_hσ1 : σ ≤ 1) :
    C₁ / 8 * ∑' n : ℕ, (2 : ℝ) ^ (-(n : ℝ) * (σ / 2)) = comparisonConst C₁ σ := by
  have hr_eq : ∀ n : ℕ, (2 : ℝ) ^ (-(n : ℝ) * (σ / 2)) = ((2 : ℝ) ^ (-(σ / 2))) ^ n := by
    intro n
    rw [show -(n : ℝ) * (σ / 2) = (-(σ / 2)) * (n : ℝ) by ring, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  have hr_nonneg : (0 : ℝ) ≤ (2 : ℝ) ^ (-(σ / 2)) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hr_lt_one : (2 : ℝ) ^ (-(σ / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsum_eq : (∑' n : ℕ, (2 : ℝ) ^ (-(n : ℝ) * (σ / 2))) = (1 - (2 : ℝ) ^ (-(σ / 2)))⁻¹ := by
    simp_rw [hr_eq]
    exact tsum_geometric_of_lt_one hr_nonneg hr_lt_one
  rw [hsum_eq]
  unfold comparisonConst
  have h1sub : (1 : ℝ) - (2 : ℝ) ^ (-(σ / 2)) ≠ 0 := by linarith
  field_simp

/-- `|λ_{n,j}| ≤ 1` for `j < 2^n`: `λ_{n,j} = -1 + (2j+1) 2^{-n}` ranges over
`[-1 + 2^{-n}, 1 - 2^{-n}] ⊆ [-1, 1]`. -/
private lemma dyadicShift_abs_le_one (n j : ℕ) (hj : j < 2 ^ n) : |dyadicShift n j| ≤ 1 := by
  unfold dyadicShift
  have hjn : (j : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
    have h2 : (j + 1 : ℕ) ≤ 2 ^ n := hj
    calc (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((2 ^ n : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (2 : ℝ) ^ n := by push_cast; ring
  have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [abs_le]
  constructor
  · have : (0 : ℝ) ≤ (2 * (j : ℝ) + 1) * ((2 : ℝ)⁻¹) ^ n := by positivity
    linarith
  · have hstep : (2 * (j : ℝ) + 1) * ((2 : ℝ)⁻¹) ^ n ≤ 2 := by
      rw [inv_pow, ← div_eq_mul_inv, div_le_iff₀ hpow_pos]
      linarith
    linarith

/-- `0 < 2^{-n} ≤ 1`. -/
private lemma dyadicScale_bounds (n : ℕ) : (0 : ℝ) < ((2 : ℝ)⁻¹) ^ n ∧ ((2 : ℝ)⁻¹) ^ n ≤ 1 :=
  ⟨by positivity, pow_le_one₀ (by norm_num) (by norm_num)⟩

/-- Local, non-private copy of the joint measurability of `β_h`, via a piecewise combination
of the continuity off the `y = 0` line (`continuous_betaPt`) and the vanishing of `β_h` on
`y ≤ 0` (degenerate/reversed intervals). -/
private lemma betaPt_measurable' (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h) :
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

/-- Local, non-private copy of the joint measurability of `ε_h`. -/
private lemma eps_measurable' (h : ℝ → ℝ) (hac : LocallyAbsolutelyContinuous h) :
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

private lemma compare_hterm_meas (h : ℝ → ℝ) (hac : LocallyAbsolutelyContinuous h)
    (C₁ σ : ℝ) (n j : ℕ) : Measurable fun p : ℝ × ℝ =>
    ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
      eps h (p.1 + dyadicShift n j * p.2) (((2:ℝ)⁻¹) ^ n * p.2) ^ 2 / p.2) := by
  have hem : Measurable fun p : ℝ × ℝ => eps h p.1 p.2 := eps_measurable' h hac
  have hshift_meas : Measurable fun p : ℝ × ℝ =>
      eps h (p.1 + dyadicShift n j * p.2) (((2:ℝ)⁻¹) ^ n * p.2) :=
    hem.comp ((measurable_fst.add
      ((measurable_const_mul (dyadicShift n j)).comp measurable_snd)).prodMk
      ((measurable_const_mul (((2:ℝ)⁻¹) ^ n)).comp measurable_snd))
  exact ((((hshift_meas).pow_const 2).const_mul _).div measurable_snd).ennreal_ofReal

private lemma compare_hSummand_meas (h : ℝ → ℝ) (hac : LocallyAbsolutelyContinuous h)
    (C₁ σ : ℝ) (n : ℕ) : Measurable fun p : ℝ × ℝ => ∑ j ∈ Finset.range (2 ^ n),
    ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
      eps h (p.1 + dyadicShift n j * p.2) (((2:ℝ)⁻¹) ^ n * p.2) ^ 2 / p.2) :=
  Finset.measurable_sum _ (fun j _ => compare_hterm_meas h hac C₁ σ n j)

private lemma compare_hterm_meas_fixedX (h : ℝ → ℝ) (hac : LocallyAbsolutelyContinuous h)
    (C₁ σ : ℝ) (n j : ℕ) (x : ℝ) : Measurable fun y : ℝ =>
    ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
      eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) := by
  have hem : Measurable fun p : ℝ × ℝ => eps h p.1 p.2 := eps_measurable' h hac
  have hshift_meas : Measurable fun y : ℝ =>
      eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) :=
    hem.comp ((measurable_const.add (measurable_const_mul (dyadicShift n j))).prodMk
      (measurable_const_mul (((2:ℝ)⁻¹) ^ n)))
  exact (((hshift_meas.pow_const 2).const_mul _).div measurable_id).ennreal_ofReal

/-- `C₂ = C₁ / (8(1 - 2^{-σ/2})) ≥ 0`. -/
private lemma comparisonConst_nonneg (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    0 ≤ comparisonConst C₁ σ := by
  rw [← comparisonConst_geometric C₁ σ hC₁ hσ hσ1]
  have : (0:ℝ) ≤ ∑' n : ℕ, (2:ℝ) ^ (-(n:ℝ) * (σ / 2)) := by
    apply tsum_nonneg
    intro n
    positivity
  have hC₁0 : (0:ℝ) ≤ C₁ := by linarith
  positivity

set_option maxHeartbeats 1000000 in
/-- **Theorem (Comparison), `ℝ≥0∞`-valued form**, assembled from `beta_sq_pointwise_bound` and
`carlesonBoxLIntegral_shift_scale_le` (applied to every dyadic piece `(n, j)` and summed via the
geometric series `comparisonConst_geometric`):
`∬_{Q_J} β_h² dxdy/y ≤ C₂ ∬_{Q_{3J}} ε_h² dxdy/y` as extended nonnegative reals. At this level
the comparison is unconditional: no finiteness hypothesis is needed. -/
private theorem compare_beta_eps_lintegral (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hw : WeightA1 (deriv h) C₁ σ)
    (a b : ℝ) (hab : a < b) :
    carlesonBoxLIntegral (betaPt h) a b ≤
      ENNReal.ofReal (comparisonConst C₁ σ) *
        carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a)) := by
  have hc : Continuous h := hac.1
  have hbm : Measurable fun p : ℝ × ℝ => betaPt h p.1 p.2 := betaPt_measurable' h hh hc
  have hem : Measurable fun p : ℝ × ℝ => eps h p.1 p.2 := eps_measurable' h hac
  -- The per-`(n, j)` shifted/scaled copy of `ε_h` is jointly measurable and `carlesonBoxLIntegral`
  -- of it is bounded by the tripled box's, unconditionally.
  have hshift_le : ∀ n j : ℕ, j < 2 ^ n →
      carlesonBoxLIntegral
          (fun x y => eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y)) a b ≤
        carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a)) := by
    intro n j hj
    exact carlesonBoxLIntegral_shift_scale_le (eps h) hem (dyadicShift n j) (((2:ℝ)⁻¹) ^ n)
      (dyadicScale_bounds n).1 (dyadicScale_bounds n).2 (dyadicShift_abs_le_one n j hj) a b hab
  have hshift_meas : ∀ n j : ℕ, Measurable fun p : ℝ × ℝ =>
      eps h (p.1 + dyadicShift n j * p.2) (((2:ℝ)⁻¹) ^ n * p.2) :=
    fun n j => hem.comp ((measurable_fst.add
      ((measurable_const_mul (dyadicShift n j)).comp measurable_snd)).prodMk
      ((measurable_const_mul (((2:ℝ)⁻¹) ^ n)).comp measurable_snd))
  -- Step 1: the pointwise `ℝ≥0∞`-valued bound (per `n, j`, not yet summed).
  have hpt : ∀ x y : ℝ, 0 < y →
      ENNReal.ofReal (betaPt h x y ^ 2 / y) ≤
        ∑' n : ℕ, ∑ j ∈ Finset.range (2 ^ n),
          ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
            eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) := by
    intro x y hy
    set S : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (2 ^ n),
        C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
          eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y with hSdef
    have halg : (C₁ / 8 * ∑' n : ℕ, (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
        ∑ j ∈ Finset.range (2 ^ n),
          eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2) / y = ∑' n : ℕ, S n := by
      rw [show (C₁ / 8 * ∑' n : ℕ, (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
          ∑ j ∈ Finset.range (2 ^ n),
            eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2) / y =
          (C₁ / 8 / y) * ∑' n : ℕ, (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
            ∑ j ∈ Finset.range (2 ^ n),
              eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 by ring]
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      rw [hSdef]
      dsimp only
      rw [← mul_assoc, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hb := beta_sq_pointwise_bound h hh hc hac C₁ σ hC₁ hσ hσ1 hw x y hy
    have hdiv : betaPt h x y ^ 2 / y ≤ ∑' n : ℕ, S n := by
      rw [← halg]
      exact div_le_div_of_nonneg_right hb hy.le
    calc ENNReal.ofReal (betaPt h x y ^ 2 / y) ≤ ENNReal.ofReal (∑' n : ℕ, S n) :=
          ENNReal.ofReal_le_ofReal hdiv
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (S n) := by
          by_cases hsum : Summable S
          · exact le_of_eq (ENNReal.ofReal_tsum_of_nonneg
              (fun n => Finset.sum_nonneg fun j _ => by positivity) hsum)
          · rw [tsum_eq_zero_of_not_summable hsum, ENNReal.ofReal_zero]
            exact bot_le
      _ = ∑' n : ℕ, ∑ j ∈ Finset.range (2 ^ n),
            ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
              eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) := by
          apply tsum_congr
          intro n
          rw [hSdef]
          exact ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)
  have hterm_meas : ∀ n j : ℕ, Measurable fun p : ℝ × ℝ =>
      ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
        eps h (p.1 + dyadicShift n j * p.2) (((2:ℝ)⁻¹) ^ n * p.2) ^ 2 / p.2) :=
    fun n j => compare_hterm_meas h hac C₁ σ n j
  have hSummand_meas : ∀ n : ℕ, Measurable fun p : ℝ × ℝ => ∑ j ∈ Finset.range (2 ^ n),
      ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
        eps h (p.1 + dyadicShift n j * p.2) (((2:ℝ)⁻¹) ^ n * p.2) ^ 2 / p.2) :=
    fun n => compare_hSummand_meas h hac C₁ σ n
  have hswapN : (∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a),
        ∑' n : ℕ, ∑ j ∈ Finset.range (2 ^ n),
          ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
            eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y)) =
      ∑' n : ℕ, ∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a), ∑ j ∈ Finset.range (2 ^ n),
        ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
          eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) := by
    have h1 := MeasureTheory.lintegral_prod
      (μ := volume.restrict (Set.Ioc a b)) (ν := volume.restrict (Set.Ioc (0:ℝ) (b - a)))
      (fun p : ℝ × ℝ => ∑' n : ℕ, ∑ j ∈ Finset.range (2 ^ n),
        ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
          eps h (p.1 + dyadicShift n j * p.2) (((2:ℝ)⁻¹) ^ n * p.2) ^ 2 / p.2))
      (Measurable.tsum hSummand_meas).aemeasurable
    rw [← h1, MeasureTheory.lintegral_tsum (fun n => (hSummand_meas n).aemeasurable)]
    apply tsum_congr
    intro n
    exact MeasureTheory.lintegral_prod (μ := volume.restrict (Set.Ioc a b))
      (ν := volume.restrict (Set.Ioc (0:ℝ) (b - a))) _ (hSummand_meas n).aemeasurable
  have hswapJ : ∀ n : ℕ, (∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a),
        ∑ j ∈ Finset.range (2 ^ n),
          ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
            eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y)) =
      ∑ j ∈ Finset.range (2 ^ n), ∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a),
        ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
          eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) := by
    intro n
    have hswapJ_y : ∀ x : ℝ, (∫⁻ y in Set.Ioc (0:ℝ) (b - a), ∑ j ∈ Finset.range (2 ^ n),
          ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
            eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y)) =
        ∑ j ∈ Finset.range (2 ^ n), ∫⁻ y in Set.Ioc (0:ℝ) (b - a),
          ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
            eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) := fun x =>
      MeasureTheory.lintegral_finsetSum _
        (fun j _ => compare_hterm_meas_fixedX h hac C₁ σ n j x)
    have hstepA : (∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a),
          ∑ j ∈ Finset.range (2 ^ n),
            ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
              eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y)) =
        ∫⁻ x in Set.Ioc a b, ∑ j ∈ Finset.range (2 ^ n), ∫⁻ y in Set.Ioc (0:ℝ) (b - a),
          ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
            eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) := by
      congr 1
      funext x
      exact hswapJ_y x
    rw [hstepA]
    exact MeasureTheory.lintegral_finsetSum _
      (fun j _ => Measurable.lintegral_prod_right (f := fun x y =>
        ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
          eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y)) (hterm_meas n j))
  have hfactor : ∀ n j : ℕ, (∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a),
        ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
          eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y)) =
      ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
        carlesonBoxLIntegral
          (fun x y => eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y)) a b := by
    intro n j
    rw [carlesonBoxLIntegral_eq_iter _ (hshift_meas n j)]
    have hc_nonneg : (0:ℝ) ≤ C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) := by positivity
    have hpt2 : ∀ x y : ℝ,
        ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
            eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) =
          ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
            ENNReal.ofReal (eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) := by
      intro x y
      rw [← ENNReal.ofReal_mul hc_nonneg]
      congr 1
      ring
    simp_rw [hpt2, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsum_j : ∀ n : ℕ, ∑ j ∈ Finset.range (2 ^ n),
      (ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
        carlesonBoxLIntegral
          (fun x y => eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y)) a b) ≤
      (2 ^ n : ℕ) * (ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
        carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a))) := by
    intro n
    calc ∑ j ∈ Finset.range (2 ^ n),
          (ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
            carlesonBoxLIntegral
              (fun x y => eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y)) a b)
        ≤ ∑ j ∈ Finset.range (2 ^ n),
            (ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
              carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a))) :=
          Finset.sum_le_sum (fun j hj =>
            mul_le_mul_right (hshift_le n j (Finset.mem_range.mp hj)) _)
      _ = (2 ^ n : ℕ) * (ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
            carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a))) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgeom_summable : Summable (fun n : ℕ => C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (σ / 2))) := by
    have heq : ∀ n : ℕ, (2:ℝ) ^ (-(n:ℝ) * (σ / 2)) = ((2:ℝ) ^ (-(σ / 2))) ^ n := by
      intro n
      rw [show -(n:ℝ) * (σ / 2) = -(σ / 2) * (n:ℝ) by ring, Real.rpow_mul (by norm_num),
        Real.rpow_natCast]
    simp_rw [heq]
    exact Summable.mul_left _ (summable_geometric_of_lt_one
      (Real.rpow_pos_of_pos (by norm_num) _).le
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)))
  have hgeom : (∑' n : ℕ, (2 ^ n : ℕ) * (ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
        carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a)))) =
      ENNReal.ofReal (comparisonConst C₁ σ) *
        carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a)) := by
    have hstep1 : ∀ n : ℕ, (2 ^ n : ℕ) * (ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
          carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a))) =
        ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (σ / 2))) *
          carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a)) := by
      intro n
      rw [← mul_assoc]
      congr 1
      rw [show ((2 ^ n : ℕ) : ENNReal) = ENNReal.ofReal ((2:ℝ) ^ n) by
          rw [ENNReal.ofReal_pow (by norm_num)]; norm_cast,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (2:ℝ) ^ n * (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) =
          C₁ / 8 * ((2:ℝ) ^ n * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) by ring,
        ← Real.rpow_natCast 2 n, ← Real.rpow_add (by norm_num)]
      congr 2
      ring
    simp_rw [hstep1]
    rw [ENNReal.tsum_mul_right]
    congr 1
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hgeom_summable, tsum_mul_left,
      comparisonConst_geometric C₁ σ hC₁ hσ hσ1]
  rw [carlesonBoxLIntegral_eq_iter _ hbm]
  refine (setLIntegral_mono' measurableSet_Ioc (fun x _ =>
    setLIntegral_mono' measurableSet_Ioc (fun y hy => hpt x y hy.1))).trans ?_
  rw [hswapN, ← hgeom]
  refine (ENNReal.tsum_le_tsum (fun n => ?_)).trans_eq rfl
  calc ∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a), ∑ j ∈ Finset.range (2 ^ n),
        ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
          eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y)
      = ∑ j ∈ Finset.range (2 ^ n), ∫⁻ x in Set.Ioc a b, ∫⁻ y in Set.Ioc (0:ℝ) (b - a),
          ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ)) *
            eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y) ^ 2 / y) := hswapJ n
    _ = ∑ j ∈ Finset.range (2 ^ n),
          (ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
            carlesonBoxLIntegral
              (fun x y => eps h (x + dyadicShift n j * y) (((2:ℝ)⁻¹) ^ n * y)) a b) := by
        apply Finset.sum_congr rfl
        intro j _
        exact hfactor n j
    _ ≤ (2 ^ n : ℕ) * (ENNReal.ofReal (C₁ / 8 * (2:ℝ) ^ (-(n:ℝ) * (1 - σ / 2 + σ))) *
          carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a))) := hsum_j n

/-- **Theorem (Comparison)**, the Bochner-valued form: `compare_beta_eps_lintegral` transferred
down to the reals with `carlesonBoxIntegral_eq_toReal_lintegral`.

Besides the standing (A1) hypotheses, this needs the box `lintegral` of `ε_h` over the *tripled*
interval to be finite (`hfin`): as in `carlesonBoxIntegral_dyadicShift`, the Bochner-valued
`carlesonBoxIntegral` is a junk value `0` when its integrand is not Lebesgue-integrable, and
nothing in the bare (A1) hypothesis rules that out. The whole argument is carried out at the
`ℝ≥0∞`-valued (`carlesonBoxLIntegral`) level, where it is unconditional, and only transferred down
to the Bochner reals at the very end using `hfin`. -/
theorem compare_beta_eps (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hw : WeightA1 (deriv h) C₁ σ)
    (a b : ℝ) (hab : a < b)
    (hfin : carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a)) ≠ ⊤) :
    carlesonBoxIntegral (betaPt h) a b ≤
      comparisonConst C₁ σ *
        carlesonBoxIntegral (eps h) (a - (b - a)) (b + (b - a)) := by
  have hbm : Measurable fun p : ℝ × ℝ => betaPt h p.1 p.2 := betaPt_measurable' h hh hac.1
  have hem : Measurable fun p : ℝ × ℝ => eps h p.1 p.2 := eps_measurable' h hac
  have hlin := compare_beta_eps_lintegral h hh hac C₁ σ hC₁ hσ hσ1 hw a b hab
  have hfin_beta : carlesonBoxLIntegral (betaPt h) a b ≠ ⊤ := by
    have hCfin : ENNReal.ofReal (comparisonConst C₁ σ) *
        carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    exact (lt_of_le_of_lt hlin hCfin.lt_top).ne
  rw [carlesonBoxIntegral_eq_toReal_lintegral _ hbm a b hab hfin_beta,
    carlesonBoxIntegral_eq_toReal_lintegral _ hem (a - (b - a)) (b + (b - a)) (by linarith) hfin]
  have hcC : (0:ℝ) ≤ comparisonConst C₁ σ := comparisonConst_nonneg C₁ σ hC₁ hσ hσ1
  calc (carlesonBoxLIntegral (betaPt h) a b).toReal ≤
        (ENNReal.ofReal (comparisonConst C₁ σ) *
          carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a))).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hlin
    _ = comparisonConst C₁ σ *
          (carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a))).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcC]

/-- Under (A2) with constant `A₀`, the entropy defect is at most `log A₀` on every interval. -/
private theorem ps_entropyDefect_le_log (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (A₀ : ℝ) (hA2 : WeightA2 (deriv h) A₀)
    (u v : ℝ) (huv : u < v) :
    entropyDefect (deriv h) u v ≤ Real.log A₀ := by
  have hgm : 0 < weightGeomMean (deriv h) u v := Real.exp_pos _
  have hmeanpos : 0 < weightMean (deriv h) u v := by
    have h1 : 0 < h v - h u := sub_pos.mpr (hh huv)
    rw [imageLength_eq_mean h hac u v huv] at h1
    exact pos_of_mul_pos_right h1 (sub_pos.mpr huv).le
  unfold entropyDefect
  exact Real.log_le_log (div_pos hmeanpos hgm) ((div_le_iff₀ hgm).mpr (hA2 u v huv))

/-- If the entropy defect is at most `M` on every interval, so is every defect average in
`entropyBoundSet`. -/
private theorem ps_entropyBoundSet_le (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (M : ℝ) (hM : ∀ u v : ℝ, u < v → entropyDefect (deriv h) u v ≤ M) (a b : ℝ) (hab : a < b) :
    ∀ r ∈ entropyBoundSet (deriv h) a b, r ≤ M := by
  rintro r ⟨y₀, hy₀, -, rfl⟩
  have hAB : a - (b - a) ≤ b + (b - a) := by linarith
  have hint : IntervalIntegrable (fun x => entropyDefect (deriv h) (x - y₀) (x + y₀)) volume
      (a - (b - a)) (b + (b - a)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr
      (entropyDefect_integrableOn h hh hac hα y₀ hy₀ (a - (b - a)) (b + (b - a)))
  have hmono : (∫ x in (a - (b - a))..(b + (b - a)),
      entropyDefect (deriv h) (x - y₀) (x + y₀)) ≤
        ∫ _x in (a - (b - a))..(b + (b - a)), M :=
    intervalIntegral.integral_mono_on hAB hint intervalIntegrable_const
      (fun x _ => hM (x - y₀) (x + y₀) (by linarith))
  rw [intervalIntegral.integral_const, smul_eq_mul,
    show b + (b - a) - (a - (b - a)) = 3 * (b - a) by ring] at hmono
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 3 * (b - a)), mul_comm M (3 * (b - a))]
  exact hmono

/-- Under (A1) the defect averages defining `E_h(J)` are bounded above, by `log A₀` with `A₀`
the (A2) constant of `a1_imp_a2`: `E_h(J)` is a genuine supremum. -/
private theorem ps_entropyBoundSet_bddAbove (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hw : WeightA1 (deriv h) C₁ σ) (a b : ℝ) (hab : a < b) :
    BddAbove (entropyBoundSet (deriv h) a b) := by
  obtain ⟨A₀, -, hA2⟩ := a1_imp_a2 (deriv h) ⟨C₁, σ, hC₁, hσ, hσ1, hw⟩
  exact ⟨Real.log A₀, ps_entropyBoundSet_le h hh hac
    (ps_logDeriv_intervalIntegrable h hh C₁ σ hC₁ hσ hσ1 hw) (Real.log A₀)
    (ps_entropyDefect_le_log h hh hac A₀ hA2) a b hab⟩

/-- **The master inequality at the `ℝ≥0∞` level**:
`∬_{Q_J} β_h² dxdy/y ≤ 18 log 2 · C₂ · E_h(3J) · |J|`, from `compare_beta_eps_lintegral` and
`eps_carleson_lintegral` applied to `3J` (where `|3J| = 3|J|`). -/
private theorem ps_beta_box_le (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hw : WeightA1 (deriv h) C₁ σ) (a b : ℝ) (hab : a < b) :
    carlesonBoxLIntegral (betaPt h) a b ≤
      ENNReal.ofReal (18 * Real.log 2 * comparisonConst C₁ σ *
        entropyBound (deriv h) (a - (b - a)) (b + (b - a)) * (b - a)) := by
  have hab3 : a - (b - a) < b + (b - a) := by linarith
  have heps := eps_carleson_lintegral h hh hac hw.1
    (ps_logDeriv_intervalIntegrable h hh C₁ σ hC₁ hσ hσ1 hw) _ _ hab3
    (ps_entropyBoundSet_bddAbove h hh hac C₁ σ hC₁ hσ hσ1 hw _ _ hab3)
  have hC := comparisonConst_nonneg C₁ σ hC₁ hσ hσ1
  refine (compare_beta_eps_lintegral h hh hac C₁ σ hC₁ hσ hσ1 hw a b hab).trans ?_
  calc ENNReal.ofReal (comparisonConst C₁ σ) *
        carlesonBoxLIntegral (eps h) (a - (b - a)) (b + (b - a))
      ≤ ENNReal.ofReal (comparisonConst C₁ σ) *
          ENNReal.ofReal (6 * Real.log 2 *
            entropyBound (deriv h) (a - (b - a)) (b + (b - a)) *
              (b + (b - a) - (a - (b - a)))) := mul_le_mul_right heps _
    _ = _ := by
        rw [← ENNReal.ofReal_mul hC]
        congr 1
        ring

/-- `18 log 2 · C₂ ≥ 0`. -/
private lemma ps_masterConst_nonneg (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    0 ≤ 18 * Real.log 2 * comparisonConst C₁ σ :=
  mul_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
    (comparisonConst_nonneg C₁ σ hC₁ hσ hσ1)

/-- The master inequality `‖β_h‖²_{T²(J)} ≤ 18 log 2 · C₂ · E_h(3J)`, stated here so that the
two parts below can use it (it is restated as `beta_carleson_master`). -/
private theorem ps_beta_master (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hw : WeightA1 (deriv h) C₁ σ) (a b : ℝ) (hab : a < b) :
    (T2norm (betaPt h) a b) ^ 2 ≤
      18 * Real.log 2 * comparisonConst C₁ σ *
        entropyBound (deriv h) (a - (b - a)) (b + (b - a)) := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have hL' : b - a ≠ 0 := hL.ne'
  have hab3 : a - (b - a) < b + (b - a) := by linarith
  have hE0 : 0 ≤ entropyBound (deriv h) (a - (b - a)) (b + (b - a)) :=
    entropyBound_nonneg h hh hac hw.1 (ps_logDeriv_intervalIntegrable h hh C₁ σ hC₁ hσ hσ1 hw)
      _ _ hab3 (ps_entropyBoundSet_bddAbove h hh hac C₁ σ hC₁ hσ hσ1 hw _ _ hab3)
  have hK0 : 0 ≤ 18 * Real.log 2 * comparisonConst C₁ σ *
      entropyBound (deriv h) (a - (b - a)) (b + (b - a)) :=
    mul_nonneg (ps_masterConst_nonneg C₁ σ hC₁ hσ hσ1) hE0
  have hbox := ps_beta_box_le h hh hac C₁ σ hC₁ hσ hσ1 hw a b hab
  have hfin : carlesonBoxLIntegral (betaPt h) a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbox
  have hreal := ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK0 hL.le) hbox
  unfold T2norm
  rw [carlesonBoxIntegral_eq_toReal_lintegral _ (betaPt_measurable' h hh hac.1) a b hab hfin,
    Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr hL.le) ENNReal.toReal_nonneg)]
  calc (b - a)⁻¹ * (carlesonBoxLIntegral (betaPt h) a b).toReal
      ≤ (b - a)⁻¹ * (18 * Real.log 2 * comparisonConst C₁ σ *
          entropyBound (deriv h) (a - (b - a)) (b + (b - a)) * (b - a)) :=
        mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr hL.le)
    _ = _ := by field_simp

/-- **`(A2)` forces `log w ∈ BMO`**: with `v = log w - (log w)_K`, the pointwise bound
`|v| ≤ 2 e^v - v`, `∫_K v = 0` and `(e^v)_K = (w)_K / m_K ≤ A₀` give `(|v|)_K ≤ 2 A₀`. -/
private theorem ps_bmo_log_of_A2 (h : ℝ → ℝ) (hh : StrictMono h)
    (hw : ∀ᵐ t ∂volume, 0 < deriv h t)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv h t)) volume u v)
    (A₀ : ℝ) (hA2 : WeightA2 (deriv h) A₀) :
    BMO (fun t => Real.log (deriv h t)) := by
  refine ⟨2 * A₀, fun c d hcd => ?_⟩
  set u : ℝ → ℝ := fun t => Real.log (deriv h t) with hu
  set m : ℝ := intervalAvg u c d with hm
  have hdc : 0 < d - c := sub_pos.mpr hcd
  have hui : IntervalIntegrable u volume c d := hα c d hcd
  have hwi : IntervalIntegrable (deriv h) volume c d :=
    (hh.monotone.monotoneOn _).intervalIntegrable_deriv
  have humi : IntervalIntegrable (fun t => u t - m) volume c d := hui.sub intervalIntegrable_const
  have hint_um : ∫ t in c..d, (u t - m) = 0 := by
    rw [intervalIntegral.integral_sub hui intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, hm, intervalAvg]
    field_simp
    ring
  have hexp_ae : ∀ᵐ t ∂volume, Real.exp (-m) * deriv h t = Real.exp (u t - m) := by
    filter_upwards [hw] with t ht
    rw [hu, sub_eq_add_neg, Real.exp_add, Real.exp_log ht, mul_comm]
  have hexp_int : IntervalIntegrable (fun t => Real.exp (u t - m)) volume c d :=
    (hwi.const_mul (Real.exp (-m))).congr_ae (ae_restrict_of_ae hexp_ae)
  have hexp_eq : ∫ t in c..d, Real.exp (u t - m) =
      Real.exp (-m) * ∫ t in c..d, deriv h t := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_ae (hexp_ae.mono fun t ht _ => ht.symm)
  have hwint : ∫ t in c..d, deriv h t = weightMean (deriv h) c d * (d - c) := by
    unfold weightMean intervalAvg
    field_simp
  have hA2' : weightMean (deriv h) c d ≤ A₀ * Real.exp m := hA2 c d hcd
  have hexp_le : ∫ t in c..d, Real.exp (u t - m) ≤ A₀ * (d - c) := by
    rw [hexp_eq, hwint]
    calc Real.exp (-m) * (weightMean (deriv h) c d * (d - c))
        ≤ Real.exp (-m) * (A₀ * Real.exp m * (d - c)) := by gcongr
      _ = A₀ * (d - c) * (Real.exp (-m) * Real.exp m) := by ring
      _ = A₀ * (d - c) := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hpt : ∀ t, |u t - m| ≤ 2 * Real.exp (u t - m) - (u t - m) := by
    intro t
    have h1 := Real.add_one_le_exp (u t - m)
    have h2 := Real.exp_pos (u t - m)
    rcases le_total 0 (u t - m) with h0 | h0
    · rw [abs_of_nonneg h0]
      linarith
    · rw [abs_of_nonpos h0]
      linarith
  have hmono : ∫ t in c..d, |u t - m| ≤ ∫ t in c..d, (2 * Real.exp (u t - m) - (u t - m)) :=
    intervalIntegral.integral_mono_on hcd.le humi.abs ((hexp_int.const_mul 2).sub humi)
      (fun t _ => hpt t)
  rw [intervalIntegral.integral_sub (hexp_int.const_mul 2) humi,
    intervalIntegral.integral_const_mul, hint_um] at hmono
  show (∫ t in c..d, |u t - m|) / (d - c) ≤ 2 * A₀
  rw [div_le_iff₀ hdc]
  linarith

/-- On an interval of length at most `r`, the local `BMO` seminorm is dominated by the `VMO`
modulus at scale `r` (both are suprema of mean oscillations; `BMO` makes them genuine). -/
private theorem ps_bmoSeminorm_le_vmoModulus {u : ℝ → ℝ} (hu : BMO u) {A B r : ℝ}
    (hAB : A < B) (hr : B - A ≤ r) :
    bmoSeminorm u A B ≤ vmoModulus u r := by
  obtain ⟨C, hC⟩ := hu
  apply csSup_le_csSup
  · exact ⟨C, by rintro s ⟨c, d, hcd, -, rfl⟩; exact hC c d hcd⟩
  · exact ⟨_, A, B, le_refl A, hAB, le_refl B, rfl⟩
  · rintro s ⟨c, d, hAc, hcd, hdB, rfl⟩
    exact ⟨c, d, hcd, by linarith, rfl⟩

/-- The local `BMO` seminorm of a `BMO` function is nonnegative. -/
private theorem ps_bmoSeminorm_nonneg {u : ℝ → ℝ} (hu : BMO u) {A B : ℝ} (hAB : A < B) :
    0 ≤ bmoSeminorm u A B := by
  obtain ⟨C, hC⟩ := hu
  have h0 : 0 ≤ intervalOscillation u A B := by
    unfold intervalOscillation intervalAvg
    exact div_nonneg (intervalIntegral.integral_nonneg hAB.le (fun x _ => abs_nonneg _))
      (sub_pos.mpr hAB).le
  exact h0.trans (le_csSup ⟨C, by rintro s ⟨c, d, -, hcd, -, rfl⟩; exact hC c d hcd⟩
    ⟨A, B, le_refl A, hAB, le_refl B, rfl⟩)

/-- **Part (C) of Theorem (Beta-number Carleson estimate)**: with `A₀` the
`(A2)` constant, `E_h(3J) ≤ log A₀` uniformly, so the master inequality gives
`V_* ≤ (18 log 2 · C₂ · log A₀)^{1/2}`. -/
theorem beta_carleson_uniform_bound (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (_hsurj : Function.Surjective h)
    (C₁ σ A₀ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hA₀ : 1 ≤ A₀)
    (hw : WeightA1 (deriv h) C₁ σ) (hw2 : WeightA2 (deriv h) A₀) (a b : ℝ) (hab : a < b) :
    T2norm (betaPt h) a b ≤
      Real.sqrt (18 * Real.log 2 * comparisonConst C₁ σ * Real.log A₀) := by
  have hab3 : a - (b - a) < b + (b - a) := by linarith
  have hE := entropy_bound_ainfty h hh hac
    (ps_logDeriv_intervalIntegrable h hh C₁ σ hC₁ hσ hσ1 hw) A₀ hA₀ hw2 _ _ hab3
  have hK := ps_masterConst_nonneg C₁ σ hC₁ hσ hσ1
  refine (Real.le_sqrt (Real.sqrt_nonneg _) (mul_nonneg hK (Real.log_nonneg hA₀))).mpr ?_
  exact (ps_beta_master h hh hac C₁ σ hC₁ hσ hσ1 hw a b hab).trans
    (mul_le_mul_of_nonneg_left hE hK)

/-- **Part (V) of Theorem (Beta-number Carleson estimate)**: the entropy over
`3J` involves only intervals contained in `15J`, so the `VMO` modulus at scale
`15|J|` controls `‖β_h‖_{T²(J)}`. -/
theorem beta_carleson_vanishing_bound (h : ℝ → ℝ) (hh : StrictMono h)
    (hac : LocallyAbsolutelyContinuous h) (_hsurj : Function.Surjective h)
    (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hw : WeightA1 (deriv h) C₁ σ) :
    ∃ Cstar η₀ : ℝ, 0 < Cstar ∧ 0 < η₀ ∧
      ∀ a b : ℝ, a < b →
        vmoModulus (fun t => Real.log (deriv h t)) (15 * (b - a)) ≤ η₀ →
          T2norm (betaPt h) a b ^ 2 ≤
            18 * Real.log 2 * comparisonConst C₁ σ * Cstar *
              vmoModulus (fun t => Real.log (deriv h t)) (15 * (b - a)) ^ 2 := by
  obtain ⟨η₀, Cs, hη₀, -, hCs, hbmo⟩ := entropy_bound_bmo
  refine ⟨Cs, η₀, by linarith, hη₀, fun a b hab hvmo => ?_⟩
  have hα := ps_logDeriv_intervalIntegrable h hh C₁ σ hC₁ hσ hσ1 hw
  obtain ⟨A₀, -, hA2⟩ := a1_imp_a2 (deriv h) ⟨C₁, σ, hC₁, hσ, hσ1, hw⟩
  have hBMO := ps_bmo_log_of_A2 h hh hw.1 hα A₀ hA2
  have hab3 : a - (b - a) < b + (b - a) := by linarith
  have hAB : a - (b - a) - 2 * (b + (b - a) - (a - (b - a))) <
      b + (b - a) + 2 * (b + (b - a) - (a - (b - a))) := by linarith
  have hlen : b + (b - a) + 2 * (b + (b - a) - (a - (b - a))) -
      (a - (b - a) - 2 * (b + (b - a) - (a - (b - a)))) ≤ 15 * (b - a) := by linarith
  have hle := ps_bmoSeminorm_le_vmoModulus hBMO hAB hlen
  have hnn := ps_bmoSeminorm_nonneg hBMO hAB
  have hE := hbmo h hh hac hw.1 hα hBMO _ _ hab3 (hle.trans hvmo)
  have hK := ps_masterConst_nonneg C₁ σ hC₁ hσ hσ1
  calc T2norm (betaPt h) a b ^ 2
      ≤ 18 * Real.log 2 * comparisonConst C₁ σ *
          entropyBound (deriv h) (a - (b - a)) (b + (b - a)) :=
        ps_beta_master h hh hac C₁ σ hC₁ hσ hσ1 hw a b hab
    _ ≤ 18 * Real.log 2 * comparisonConst C₁ σ *
          (Cs * vmoModulus (fun t => Real.log (deriv h t)) (15 * (b - a)) ^ 2) :=
        mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hnn hle 2) (by linarith))) hK
    _ = _ := by ring

/-- **Theorem (Beta-number Carleson estimate), master inequality**: for an
increasing, locally absolutely continuous homeomorphism `h` of `ℝ` with
`h' = w ∈ A_∞(ℝ)` (constants `C₁, σ` as in (A1)), and every bounded
interval `J`,
`‖β_h‖²_{T²(J)} ≤ 18 log 2 · C₂ · E_h(3J)`. -/
theorem beta_carleson_master (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (_hsurj : Function.Surjective h)
    (C₁ σ : ℝ) (hC₁ : 1 ≤ C₁) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (hw : WeightA1 (deriv h) C₁ σ)
    (a b : ℝ) (hab : a < b) :
    (T2norm (betaPt h) a b) ^ 2 ≤
      18 * Real.log 2 * comparisonConst C₁ σ *
        entropyBound (deriv h) (a - (b - a)) (b + (b - a)) :=
  ps_beta_master h hh hac C₁ σ hC₁ hσ hσ1 hw a b hab

/-- **Theorem (Beta-number Carleson estimate), part (C)**: `β_h² dxdy/y` is a
Carleson measure on `𝕌`. -/
theorem isCarlesonFn_betaPt (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (_hsurj : Function.Surjective h)
    (hw : AInfinityWeight (deriv h)) :
    IsCarlesonFn (betaPt h) := by
  obtain ⟨C₁, σ, hC₁, hσ, hσ1, hA1⟩ := hw
  obtain ⟨A₀, hA₀, hA2⟩ := a1_imp_a2 (deriv h) ⟨C₁, σ, hC₁, hσ, hσ1, hA1⟩
  have hα := ps_logDeriv_intervalIntegrable h hh C₁ σ hC₁ hσ hσ1 hA1
  have hK := ps_masterConst_nonneg C₁ σ hC₁ hσ hσ1
  refine ⟨18 * Real.log 2 * comparisonConst C₁ σ * Real.log A₀,
    mul_nonneg hK (Real.log_nonneg hA₀), fun a b hab => ?_⟩
  have hab3 : a - (b - a) < b + (b - a) := by linarith
  have hE := entropy_bound_ainfty h hh hac hα A₀ hA₀ hA2 _ _ hab3
  refine (ps_beta_box_le h hh hac C₁ σ hC₁ hσ hσ1 hA1 a b hab).trans
    (ENNReal.ofReal_le_ofReal ?_)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hK) (sub_pos.mpr hab).le

/-- **Theorem (Beta-number Carleson estimate), part (V)**: if moreover
`log h' ∈ VMO(ℝ)`, `β_h² dxdy/y` is a vanishing Carleson measure on `𝕌`. -/
theorem isVanishingCarleson_betaPt (h : ℝ → ℝ)
    (hh : StrictMono h) (hac : LocallyAbsolutelyContinuous h)
    (hsurj : Function.Surjective h)
    (hw : AInfinityWeight (deriv h))
    (hvmo : VMO (fun t => Real.log (deriv h t))) :
    IsVanishingCarleson (betaPt h) := by
  refine ⟨isCarlesonFn_betaPt h hh hac hsurj hw, fun ε hε => ?_⟩
  obtain ⟨C₁, σ, hC₁, hσ, hσ1, hA1⟩ := hw
  have hα := ps_logDeriv_intervalIntegrable h hh C₁ σ hC₁ hσ hσ1 hA1
  obtain ⟨η₀, Cs, hη₀, hη₀half, hCs, hbmo⟩ := entropy_bound_bmo
  have hK := ps_masterConst_nonneg C₁ σ hC₁ hσ hσ1
  set K : ℝ := 18 * Real.log 2 * comparisonConst C₁ σ with hKdef
  have hKCs : 0 ≤ K * Cs := mul_nonneg hK (by linarith)
  have hden : 0 < K * Cs + 1 := by linarith
  set ε' : ℝ := min η₀ (ε / (K * Cs + 1)) with hε'def
  have hε'pos : 0 < ε' := lt_min hη₀ (div_pos hε hden)
  have hε'η : ε' ≤ η₀ := min_le_left _ _
  have hε'ε : ε' * (K * Cs + 1) ≤ ε := (le_div_iff₀ hden).mp (min_le_right _ _)
  have hkey : K * (Cs * ε' ^ 2) ≤ ε := by
    have h1 : ε' ^ 2 ≤ ε' := by nlinarith
    have h2 : K * Cs * ε' ^ 2 ≤ K * Cs * ε' := mul_le_mul_of_nonneg_left h1 hKCs
    nlinarith
  obtain ⟨r, hr, hvmor⟩ := hvmo.2 ε' hε'pos
  refine ⟨r / 15, by positivity, fun a b hab hlen => ?_⟩
  have hab3 : a - (b - a) < b + (b - a) := by linarith
  have hAB : a - (b - a) - 2 * (b + (b - a) - (a - (b - a))) <
      b + (b - a) + 2 * (b + (b - a) - (a - (b - a))) := by linarith
  have hlenr : b + (b - a) + 2 * (b + (b - a) - (a - (b - a))) -
      (a - (b - a) - 2 * (b + (b - a) - (a - (b - a)))) ≤ r := by linarith
  have hle := (ps_bmoSeminorm_le_vmoModulus hvmo.1 hAB hlenr).trans hvmor
  have hnn := ps_bmoSeminorm_nonneg hvmo.1 hAB
  have hE := hbmo h hh hac hA1.1 hα hvmo.1 _ _ hab3 (hle.trans hε'η)
  refine (ps_beta_box_le h hh hac C₁ σ hC₁ hσ hσ1 hA1 a b hab).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (sub_pos.mpr hab).le))
  calc K * entropyBound (deriv h) (a - (b - a)) (b + (b - a))
      ≤ K * (Cs * ε' ^ 2) :=
        mul_le_mul_of_nonneg_left (hE.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hnn hle 2) (by linarith))) hK
    _ ≤ ε := hkey

/-! ## Section 9: from `β_h` to `Θ_h`, and the main theorem -/

/-- **(eq. `scale-id-new`)**: the change of variables `Y = 2^k y` (so that
`dY/Y = dy/y`) turns the dilated tent norm into an integral up to height
`2^k |J|`. -/
theorem T2norm_scale_identity (h : ℝ → ℝ) (a b : ℝ) (hab : a < b) (k : ℕ) :
    T2norm (fun x y => betaPt h x (2 ^ k * y)) a b ^ 2 =
      (b - a)⁻¹ * ∫ x in a..b, ∫ Y in (0:ℝ)..((2 : ℝ) ^ k * (b - a)),
        betaPt h x Y ^ 2 / Y := by
  set c : ℝ := (2 : ℝ) ^ k with hcdef
  have hc : c ≠ 0 := by positivity
  have hinner : ∀ x : ℝ,
      (∫ y in (0:ℝ)..(b - a), betaPt h x (c * y) ^ 2 / y) =
        ∫ Y in (0:ℝ)..(c * (b - a)), betaPt h x Y ^ 2 / Y := by
    intro x
    have hpt : ∀ y : ℝ,
        betaPt h x (c * y) ^ 2 / y = c * (betaPt h x (c * y) ^ 2 / (c * y)) := by
      intro y
      rcases eq_or_ne y 0 with hy0 | hy0
      · simp [hy0]
      · field_simp
    simp_rw [hpt]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun t => betaPt h x t ^ 2 / t) hc]
    rw [mul_zero, smul_eq_mul]
    field_simp
  have hnonneg : (0:ℝ) ≤ (b - a)⁻¹ *
      ∫ x in a..b, ∫ y in (0:ℝ)..(b - a), betaPt h x (c * y) ^ 2 / y := by
    apply mul_nonneg (by positivity)
    apply intervalIntegral.integral_nonneg hab.le
    intro x _
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y hy
    exact div_nonneg (sq_nonneg _) hy.1
  unfold T2norm carlesonBoxIntegral
  rw [Real.sq_sqrt hnonneg]
  congr 1
  simp_rw [hinner]

/-- **The tail series estimate**: `∑_{k > K} 4^{-k} √k ≤ C₄ 4^{-K} √K` for
`K ≥ 1`, with `C₄` absolute. -/
theorem sum_geometric_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ K : ℕ, 1 ≤ K →
      (∑' k : ℕ, ((4 : ℝ)⁻¹) ^ (K + 1 + k) * Real.sqrt (K + 1 + k)) ≤
        C * ((4 : ℝ)⁻¹) ^ K * Real.sqrt K := by
  have hsummable : Summable (fun k : ℕ => (4 : ℝ)⁻¹ ^ k * Real.sqrt (2 + k)) := by
    have hcomp : ∀ k : ℕ, (4 : ℝ)⁻¹ ^ k * Real.sqrt (2 + k) ≤ (4 : ℝ)⁻¹ ^ k * (2 + (k:ℝ)) := by
      intro k
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc Real.sqrt (2 + (k:ℝ)) ≤ Real.sqrt ((2 + (k:ℝ)) ^ 2) := by
            apply Real.sqrt_le_sqrt
            nlinarith [Nat.cast_nonneg (α := ℝ) k]
        _ = 2 + (k:ℝ) := Real.sqrt_sq (by positivity)
    apply Summable.of_nonneg_of_le (fun k => by positivity) hcomp
    have h1 : Summable (fun k : ℕ => (4 : ℝ)⁻¹ ^ k * 2) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right 2
    have h2 : Summable (fun k : ℕ => (k : ℝ) ^ 1 * (4 : ℝ)⁻¹ ^ k) :=
      summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(4 : ℝ)⁻¹‖ < 1)
    have h3 := h1.add (by simpa using h2)
    convert h3 using 1
    funext b
    rw [← inv_pow]
    ring
  set M : ℝ := ∑' k : ℕ, (4 : ℝ)⁻¹ ^ k * Real.sqrt (2 + k) with hMdef
  have hMpos : 0 < M := by
    have h0 : (4 : ℝ)⁻¹ ^ (0:ℕ) * Real.sqrt (2 + (0:ℕ)) ≤ M := by
      have hle := hsummable.sum_le_tsum ({0} : Finset ℕ) (fun k _ => by positivity)
      rwa [Finset.sum_singleton] at hle
    have hpos : (0 : ℝ) < (4 : ℝ)⁻¹ ^ (0:ℕ) * Real.sqrt (2 + (0:ℕ)) := by positivity
    linarith
  refine ⟨M / 4, by positivity, ?_⟩
  intro K hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hbound : ∀ k : ℕ, ((4 : ℝ)⁻¹) ^ (K + 1 + k) * Real.sqrt (K + 1 + k) ≤
      ((4 : ℝ)⁻¹) ^ (K + 1) * Real.sqrt K * ((4 : ℝ)⁻¹ ^ k * Real.sqrt (2 + k)) := by
    intro k
    have hKk : (K : ℝ) + 1 + k ≤ (K : ℝ) * (2 + k) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hsqrt : Real.sqrt ((K : ℝ) + 1 + k) ≤ Real.sqrt K * Real.sqrt (2 + k) := by
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt hKk
    have hpow_eq : ((4 : ℝ)⁻¹) ^ (K + 1 + k) = ((4 : ℝ)⁻¹) ^ (K + 1) * ((4 : ℝ)⁻¹) ^ k := by
      rw [← pow_add]
    rw [hpow_eq]
    calc ((4 : ℝ)⁻¹) ^ (K + 1) * ((4 : ℝ)⁻¹) ^ k * Real.sqrt ((K : ℝ) + 1 + (k:ℝ))
        ≤ ((4 : ℝ)⁻¹) ^ (K + 1) * ((4 : ℝ)⁻¹) ^ k * (Real.sqrt K * Real.sqrt (2 + k)) :=
          mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = ((4 : ℝ)⁻¹) ^ (K + 1) * Real.sqrt K * (((4 : ℝ)⁻¹) ^ k * Real.sqrt (2 + k)) := by ring
  have hRHS_summable : Summable (fun k : ℕ =>
      ((4 : ℝ)⁻¹) ^ (K + 1) * Real.sqrt K * ((4 : ℝ)⁻¹ ^ k * Real.sqrt (2 + k))) :=
    hsummable.mul_left _
  have hLHS_summable : Summable (fun k : ℕ => ((4 : ℝ)⁻¹) ^ (K + 1 + k) * Real.sqrt (K + 1 + k)) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hbound hRHS_summable
  have hsum_le : (∑' k : ℕ, ((4 : ℝ)⁻¹) ^ (K + 1 + k) * Real.sqrt (K + 1 + k)) ≤
      ((4 : ℝ)⁻¹) ^ (K + 1) * Real.sqrt K * M := by
    rw [hMdef, ← tsum_mul_left]
    exact hLHS_summable.tsum_le_tsum hbound hRHS_summable
  calc (∑' k : ℕ, ((4 : ℝ)⁻¹) ^ (K + 1 + k) * Real.sqrt (K + 1 + k))
      ≤ ((4 : ℝ)⁻¹) ^ (K + 1) * Real.sqrt K * M := hsum_le
    _ = M / 4 * ((4 : ℝ)⁻¹) ^ K * Real.sqrt K := by
        rw [pow_succ]
        ring

/-- **Domination principle**: a non-negative function pointwise dominated by a
constant multiple of a vanishing Carleson function is itself a vanishing
Carleson function. This is the last step of the proof of the main theorem,
applied to `|μ_{e(f)}| ≤ C(ρ) Θ_f`. -/
theorem isVanishingCarleson_of_le (F G : ℝ → ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ x y : ℝ, 0 < y → |F x y| ≤ C * G x y) (hG : IsVanishingCarleson G) :
    IsVanishingCarleson F := by
  have hpt : ∀ a b : ℝ,
      carlesonBoxLIntegral F a b ≤ ENNReal.ofReal (C ^ 2) * carlesonBoxLIntegral G a b := by
    intro a b
    unfold carlesonBoxLIntegral
    rw [← lintegral_const_mul' _ _ (by finiteness)]
    apply lintegral_mono
    intro p
    show ENNReal.ofReal (F p.1 p.2 ^ 2 / p.2) ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (G p.1 p.2 ^ 2 / p.2)
    by_cases hy : 0 < p.2
    · rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C ^ 2)]
      apply ENNReal.ofReal_le_ofReal
      have hFy := hFG p.1 p.2 hy
      have h1 : |F p.1 p.2| ^ 2 ≤ (C * G p.1 p.2) ^ 2 :=
        sq_le_sq' (by linarith [abs_nonneg (F p.1 p.2)]) hFy
      have hsq : F p.1 p.2 ^ 2 ≤ C ^ 2 * G p.1 p.2 ^ 2 := by
        rw [← sq_abs (F p.1 p.2)]
        calc |F p.1 p.2| ^ 2 ≤ (C * G p.1 p.2) ^ 2 := h1
          _ = C ^ 2 * G p.1 p.2 ^ 2 := by ring
      calc F p.1 p.2 ^ 2 / p.2 ≤ (C ^ 2 * G p.1 p.2 ^ 2) / p.2 :=
            div_le_div_of_nonneg_right hsq hy.le
        _ = C ^ 2 * (G p.1 p.2 ^ 2 / p.2) := by ring
    · push Not at hy
      have hle0 : F p.1 p.2 ^ 2 / p.2 ≤ 0 := div_nonpos_iff.mpr (Or.inl ⟨sq_nonneg _, hy⟩)
      rw [ENNReal.ofReal_of_nonpos hle0]
      exact bot_le
  constructor
  · obtain ⟨CG, hCGnn, hCGbd⟩ := hG.1
    refine ⟨C ^ 2 * CG, by positivity, ?_⟩
    intro a b hab
    calc carlesonBoxLIntegral F a b
        ≤ ENNReal.ofReal (C ^ 2) * carlesonBoxLIntegral G a b := hpt a b
      _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (CG * (b - a)) :=
          mul_le_mul_right (hCGbd a b hab) _
      _ = ENNReal.ofReal (C ^ 2 * CG * (b - a)) := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
  · intro ε hε
    rcases eq_or_lt_of_le hC with hC0 | hCpos
    · refine ⟨1, one_pos, fun a b _ _ => ?_⟩
      calc carlesonBoxLIntegral F a b
          ≤ ENNReal.ofReal (C ^ 2) * carlesonBoxLIntegral G a b := hpt a b
        _ = 0 := by rw [← hC0]; simp
        _ ≤ ENNReal.ofReal (ε * (b - a)) := bot_le
    · obtain ⟨δ, hδpos, hδbd⟩ := hG.2 (ε / C ^ 2) (by positivity)
      refine ⟨δ, hδpos, ?_⟩
      intro a b hab hlen
      calc carlesonBoxLIntegral F a b
          ≤ ENNReal.ofReal (C ^ 2) * carlesonBoxLIntegral G a b := hpt a b
        _ ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (ε / C ^ 2 * (b - a)) :=
            mul_le_mul_right (hδbd a b hab hlen) _
        _ = ENNReal.ofReal (ε * (b - a)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            field_simp

/-- **The doubling estimate behind `ainfty_imp_quasisymmetric`**: under (A2) with constant `A₀`,
for `I = [x - t, x + t]` with halves `I⁻, I⁺`, Jensen on each half gives
`e^{(log w)_I} ≤ ((w)_{I⁻} (w)_{I⁺})^{1/2}`, and `½ (w)_{I⁻} ≤ (w)_I ≤ A₀ e^{(log w)_I}`, so
`(w)_{I⁻} ≤ 4 A₀² (w)_{I⁺}` (and symmetrically); `|h(I^±)| = t (w)_{I^±}`. -/
private theorem ps_adjacent_image_le (f : ℝ → ℝ) (hf : StrictMono f)
    (hac : LocallyAbsolutelyContinuous f) (hw : ∀ᵐ t ∂volume, 0 < deriv f t)
    (hα : ∀ u v : ℝ, u < v →
      IntervalIntegrable (fun t => Real.log (deriv f t)) volume u v)
    (A₀ : ℝ) (hA2 : WeightA2 (deriv f) A₀) (x t : ℝ) (ht : 0 < t) :
    f (x + t) - f x ≤ 4 * A₀ ^ 2 * (f x - f (x - t)) ∧
      f x - f (x - t) ≤ 4 * A₀ ^ 2 * (f (x + t) - f x) := by
  have hx1 : x - t < x := by linarith
  have hx2 : x < x + t := by linarith
  have hx3 : x - t < x + t := by linarith
  have e1 := imageLength_eq_mean f hac (x - t) x hx1
  have e2 := imageLength_eq_mean f hac x (x + t) hx2
  have e3 := imageLength_eq_mean f hac (x - t) (x + t) hx3
  rw [show x - (x - t) = t by ring] at e1
  rw [show x + t - x = t by ring] at e2
  rw [show x + t - (x - t) = 2 * t by ring] at e3
  have hint : ∀ u v : ℝ, IntervalIntegrable (deriv f) volume u v := fun u v =>
    (hf.monotone.monotoneOn _).intervalIntegrable_deriv
  -- the three means and the three geometric means
  have hmm : 0 < weightMean (deriv f) (x - t) x := by
    have h1 : 0 < f x - f (x - t) := sub_pos.mpr (hf hx1)
    rw [e1] at h1
    exact pos_of_mul_pos_right h1 ht.le
  have hmp : 0 < weightMean (deriv f) x (x + t) := by
    have h1 : 0 < f (x + t) - f x := sub_pos.mpr (hf hx2)
    rw [e2] at h1
    exact pos_of_mul_pos_right h1 ht.le
  have hm : 2 * weightMean (deriv f) (x - t) (x + t) =
      weightMean (deriv f) (x - t) x + weightMean (deriv f) x (x + t) := by
    apply mul_left_cancel₀ ht.ne'
    linarith
  have hGm := ps_geomMean_le_mean_ae (deriv f) (x - t) x hx1 hw (hint _ _) (hα _ _ hx1)
  have hGp := ps_geomMean_le_mean_ae (deriv f) x (x + t) hx2 hw (hint _ _) (hα _ _ hx2)
  have hsplit : intervalAvg (fun s => Real.log (deriv f s)) (x - t) (x + t) =
      (intervalAvg (fun s => Real.log (deriv f s)) (x - t) x +
        intervalAvg (fun s => Real.log (deriv f s)) x (x + t)) / 2 := by
    unfold intervalAvg
    rw [← intervalIntegral.integral_add_adjacent_intervals (hα _ _ hx1) (hα _ _ hx2),
      show x + t - (x - t) = 2 * t by ring, show x - (x - t) = t by ring,
      show x + t - x = t by ring]
    field_simp
  have hG2 : weightGeomMean (deriv f) (x - t) (x + t) ^ 2 =
      weightGeomMean (deriv f) (x - t) x * weightGeomMean (deriv f) x (x + t) := by
    unfold weightGeomMean
    rw [sq, ← Real.exp_add, ← Real.exp_add, hsplit]
    congr 1
    ring
  have hA := hA2 (x - t) (x + t) hx3
  have hGp0 : 0 ≤ weightGeomMean (deriv f) x (x + t) := (Real.exp_pos _).le
  -- `(w)_{I^±}² ≤ 4 A₀² m_I² = 4 A₀² m_{I⁻} m_{I⁺} ≤ 4 A₀² (w)_{I⁻} (w)_{I⁺}`
  have hprod : (2 * A₀ * weightGeomMean (deriv f) (x - t) (x + t)) ^ 2 ≤
      4 * A₀ ^ 2 * (weightMean (deriv f) (x - t) x * weightMean (deriv f) x (x + t)) := by
    rw [mul_pow, hG2]
    have := mul_le_mul hGm hGp hGp0 hmm.le
    nlinarith [sq_nonneg (2 * A₀)]
  have hside : ∀ p q : ℝ, 0 < p →
      p ≤ 2 * A₀ * weightGeomMean (deriv f) (x - t) (x + t) →
      (2 * A₀ * weightGeomMean (deriv f) (x - t) (x + t)) ^ 2 ≤ 4 * A₀ ^ 2 * (p * q) →
      p ≤ 4 * A₀ ^ 2 * q := by
    intro p q hp hpG hPQ
    have h1 : p ^ 2 ≤ (2 * A₀ * weightGeomMean (deriv f) (x - t) (x + t)) ^ 2 :=
      pow_le_pow_left₀ hp.le hpG 2
    have h2 : p * p ≤ p * (4 * A₀ ^ 2 * q) := by nlinarith
    exact le_of_mul_le_mul_left h2 hp
  have hmmle : weightMean (deriv f) (x - t) x ≤ 4 * A₀ ^ 2 * weightMean (deriv f) x (x + t) :=
    hside _ _ hmm (by linarith) hprod
  have hmple : weightMean (deriv f) x (x + t) ≤ 4 * A₀ ^ 2 * weightMean (deriv f) (x - t) x :=
    hside _ _ hmp (by linarith)
      (by rw [mul_comm (weightMean (deriv f) x (x + t))]; exact hprod)
  constructor
  · rw [e1, e2]
    have := mul_le_mul_of_nonneg_left hmple ht.le
    linarith
  · rw [e1, e2]
    have := mul_le_mul_of_nonneg_left hmmle ht.le
    linarith

/-- **`SS(ℝ) ⊆ 𝒬𝒮`, quantitatively**: an `A_∞` derivative makes `f` doubling,
hence strongly quasisymmetric; this is the input `\cite{Jon}, \cite{HS}` used
at the start of the proof of the main theorem. -/
theorem ainfty_imp_quasisymmetric (f : ℝ → ℝ) (hf : StrictMono f)
    (hsurj : Function.Surjective f) (hac : LocallyAbsolutelyContinuous f)
    (hw : AInfinityWeight (deriv f)) :
    ∃ ρ : ℝ, 1 ≤ ρ ∧ Quasisymmetric f ρ := by
  obtain ⟨C₁, σ, hC₁, hσ, hσ1, hA1⟩ := hw
  obtain ⟨A₀, hA₀, hA2⟩ := a1_imp_a2 (deriv f) ⟨C₁, σ, hC₁, hσ, hσ1, hA1⟩
  have hα := ps_logDeriv_intervalIntegrable f hf C₁ σ hC₁ hσ hσ1 hA1
  refine ⟨4 * A₀ ^ 2, by nlinarith, hf, hac.1, hsurj, fun x t ht => ?_⟩
  exact ps_adjacent_image_le f hf hac hA1.1 hα A₀ hA2 x t ht

/-- **`‖μ_{e(f)}‖_∞ < 1`**: for `f ∈ SS(ℝ)` the extension is quasiconformal,
so its dilatation is uniformly bounded away from `1`. This is the `M(𝕌)` half
of the main theorem, the other half being the vanishing Carleson property. -/
theorem ss_dilatation_sup_lt_one (f : ℝ → ℝ) (hf : StronglySymmetric f) :
    ∃ k : ℝ, k < 1 ∧
      ∀ z : ℂ, 0 < z.im → ‖complexDilatation (douadyEarle f) z‖ ≤ k := by
  obtain ⟨ρ, hρ, hqs⟩ := ainfty_imp_quasisymmetric f hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1
  obtain ⟨K, hK, hbound⟩ := de_quasiconformal ρ hρ
  refine ⟨(K - 1) / (K + 1), ?_, fun z hz => hbound f hqs z hz⟩
  rw [div_lt_one (by linarith)]
  linarith

end VanishingCarleson

end
