/-
# The Forward Inequality (Section 4)

Theorem (Forward Inequality): the dilatation of `e(h)` at `z₀` is controlled
by the deviation of `h` from an arbitrary affine map `M(t) = κt + τ`,
integrated against the Poisson kernel and damped by two denominator factors.

The proof follows the paper, except for the lower bound of Step 2 on the
denominator `D = a + q b̄`: instead of Shen's bi-Lipschitz estimate it uses the
compactness of the normalized family `KImage ρ` directly (`fwd_lower_bound`).
For the normalized boundary map `g = γ ∘ h̃ ∘ γ⁻¹` one has `g = λ · σ_W ∘ g_H`
with `g_H ∈ KImage ρ`, `W = E(g_H)(0)` and `|λ| = 1`, so `|D(g)| = |D(σ_W ∘ g_H)|`,
a continuous and positive function of `g_H`.
-/
import Mathlib
import VanishingCarleson.ForwardDisc

open MeasureTheory Real Set

noncomputable section

namespace VanishingCarleson

/-! ## Increasing affine maps and their Cayley conjugates -/
/-- An increasing affine reparametrization `t ↦ a h(ct + d) + b` of an increasing
homeomorphism `h` of `ℝ` is again one. -/
private lemma fwd_affine_props {h : ℝ → ℝ} (hh : StrictMono h) (hc : Continuous h)
    (hs : Function.Surjective h) {a c : ℝ} (ha : 0 < a) (hc' : 0 < c) (b d : ℝ) :
    StrictMono (fun t => a * h (c * t + d) + b) ∧ Continuous (fun t => a * h (c * t + d) + b) ∧
      Function.Surjective (fun t => a * h (c * t + d) + b) := by
  refine ⟨fun x y hxy => ?_, by fun_prop, fun y => ?_⟩
  · have h1 : h (c * x + d) < h (c * y + d) := hh (by nlinarith)
    show a * h (c * x + d) + b < a * h (c * y + d) + b
    linarith [mul_lt_mul_of_pos_left h1 ha]
  · obtain ⟨s, hs'⟩ := hs ((y - b) / a)
    refine ⟨(s - d) / c, ?_⟩
    show a * h (c * ((s - d) / c) + d) + b = y
    rw [show c * ((s - d) / c) + d = s by field_simp; try ring, hs']
    field_simp
    try ring

/-- `t ↦ αt + β` is an increasing homeomorphism of `ℝ` for `α > 0`. -/
private lemma fwd_lin_props {α : ℝ} (hα : 0 < α) (β : ℝ) :
    StrictMono (fun t : ℝ => α * t + β) ∧ Continuous (fun t : ℝ => α * t + β) ∧
      Function.Surjective (fun t : ℝ => α * t + β) := by
  refine ⟨fun x y hxy => ?_, by fun_prop, fun y => ⟨(y - β) / α, ?_⟩⟩
  · show α * x + β < α * y + β
    linarith [mul_lt_mul_of_pos_left hxy hα]
  · show α * ((y - β) / α) + β = y
    field_simp
    try ring

/-- The point `p = (i - β)/α ∈ 𝕌` that `u ↦ αu + β` sends to `i`. -/
private def fwdP (α β : ℝ) : ℂ := (Complex.I - β) / α

private lemma fwdP_im {α : ℝ} (hα : 0 < α) (β : ℝ) : 0 < (fwdP α β).im := by
  rw [fwdP, Complex.div_ofReal_im]
  simp only [Complex.sub_im, Complex.I_im, Complex.ofReal_im, sub_zero]
  positivity

/-- The element `z ↦ conj λ(p) · σ_{γ(p)}(z)` of `G₊`, `p = fwdP α β`: the Cayley
conjugate `γ ∘ (u ↦ αu + β) ∘ γ⁻¹` of an increasing real affine map. -/
private def fwdMob (α β : ℝ) (z : ℂ) : ℂ :=
  star (lambdaFactor (fwdP α β)) * diskAut (cayley (fwdP α β)) z

private lemma fwdMob_isDiskAutPlus {α : ℝ} (hα : 0 < α) (β : ℝ) : IsDiskAutPlus (fwdMob α β) :=
  ⟨star (lambdaFactor (fwdP α β)), cayley (fwdP α β),
    by rw [norm_star]; exact lambdaFactor_norm _ (fwdP_im hα β),
    norm_cayley_lt_one (fwdP_im hα β), fun _ => rfl⟩

/-- On `ℝ`, `γ(αu + β) = M(γ(u))` for the Möbius map `M = fwdMob α β`. -/
private lemma fwd_cayley_affine {α : ℝ} (hα : 0 < α) (β u : ℝ) :
    cayley ((α * u + β : ℝ) : ℂ) = fwdMob α β (cayley (u : ℂ)) := by
  have hp := fwdP_im hα β
  have hu1 : (u : ℂ) ≠ star (fwdP α β) := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im, Complex.ofReal_im] at this
    linarith
  have hu2 : (u : ℂ) ≠ -Complex.I := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have htr := cayley_involution_transfer (fwdP α β) u hp hu1 hu2
  have hl := star_mul_self_of_norm_one (lambdaFactor_norm _ hp)
  have hsp : star (fwdP α β) = (-Complex.I - β) / α := by
    rw [fwdP, star_div₀, star_sub, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_ofReal]
  have hα' : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
  have h2 := sub_ne_zero.2 hu1
  rw [hsp] at h2
  have h1 : (α : ℂ) * u + β + Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
  have hkey : cayley ((α * u + β : ℝ) : ℂ) =
      ((u : ℂ) - fwdP α β) / ((u : ℂ) - star (fwdP α β)) := by
    rw [hsp, fwdP, cayley]
    push_cast
    rw [div_eq_div_iff h1 h2]
    field_simp
    ring
  rw [hkey, fwdMob]
  show _ = star (lambdaFactor (fwdP α β)) * diskInvolution (cayley (fwdP α β)) (cayley u)
  rw [htr, ← mul_assoc, hl, one_mul]

/-- The Möbius map `conj λ(p) · σ_{γ(p)}` fixes `1 = γ(∞)`. -/
private lemma fwd_mob_one_aux (p : ℂ) (hp : 0 < p.im) :
    star (lambdaFactor p) * diskAut (cayley p) 1 = 1 := by
  have hpI : p + Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have hsI : star p - Complex.I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.star_def] at this
    simp at this
    linarith
  have hstar : star (p + Complex.I) = star p - Complex.I := by
    rw [star_add, Complex.star_def, Complex.conj_I]
    ring
  have hnorm : ((‖p + Complex.I‖ ^ 2 : ℝ) : ℂ) = (p + Complex.I) * (star p - Complex.I) := by
    rw [Complex.sq_norm, ← hstar]
    exact (Complex.mul_conj (p + Complex.I)).symm
  have hsl : star (lambdaFactor p) = -(p + Complex.I) / (star p - Complex.I) := by
    have hreal : star ((‖p + Complex.I‖ ^ 2 : ℝ) : ℂ) = ((‖p + Complex.I‖ ^ 2 : ℝ) : ℂ) :=
      Complex.conj_ofReal _
    rw [lambdaFactor, star_div₀, star_neg, star_pow, hstar, hreal, hnorm]
    field_simp
    try ring
  have hsc : star (cayley p) = (star p + Complex.I) / (star p - Complex.I) := by
    rw [cayley, star_div₀, star_sub, star_add, Complex.star_def, Complex.conj_I]
    ring
  have e1 : 1 - cayley p = 2 * Complex.I / (p + Complex.I) := by
    rw [cayley]
    field_simp
    ring
  have e2 : 1 - star (cayley p) * 1 = -(2 * Complex.I) / (star p - Complex.I) := by
    rw [hsc]
    field_simp
    ring
  rw [hsl, diskAut, e1, e2]
  field_simp
  try ring

/-- The Cayley conjugate of `t ↦ α f(t) + β` is `fwdMob α β` applied to that of `f`. -/
private lemma fwd_cayleyConj_affine {α : ℝ} (hα : 0 < α) (β : ℝ) (f : ℝ → ℝ) (ζ : Circle) :
    ((cayleyConj (fun t => α * f t + β) ζ : Circle) : ℂ) =
      fwdMob α β ((cayleyConj f ζ : Circle) : ℂ) := by
  by_cases hζ : ζ = 1
  · subst hζ
    rw [cayleyConj_one, cayleyConj_one, Circle.coe_one]
    exact (fwd_mob_one_aux _ (fwdP_im hα β)).symm
  · simp only [cayleyConj, hζ, ↓reduceIte]
    rw [cayleyCircle_coe, cayleyCircle_coe]
    exact fwd_cayley_affine hα β _

private lemma fwd_cayleyConj_id (ζ : Circle) : cayleyConj id ζ = ζ := by
  by_cases hζ : ζ = 1
  · subst hζ
    exact cayleyConj_one id
  · simp only [cayleyConj, hζ, ↓reduceIte, id]
    exact cayleyCircle_cayleyInv_re ζ hζ


/-! ## Step 2: the denominator is bounded below on the compact family -/

/-- The denominator `D = a + q b̄` of the dilatation formula. -/
private def fwdD (f : C(Circle, ℂ)) : ℂ := momA f + momQ f * star (momB f)

private lemma fwdD_continuous : Continuous fwdD := by
  have hm : Continuous (circleMean : C(Circle, ℂ) → ℂ) := circleMean.continuous
  unfold fwdD momA momB momQ
  exact (hm.comp (continuous_id.mul continuous_const)).add
    ((hm.comp (continuous_id.mul continuous_id)).mul
      (continuous_star.comp (hm.comp (continuous_id.mul continuous_const))))

private lemma fwdD_smul {c : ℂ} (hc : ‖c‖ = 1) (f : C(Circle, ℂ)) :
    fwdD (c • f) = c * fwdD f := by
  have hcc := star_mul_self_of_norm_one hc
  have hA : momA (c • f) = c * momA f := by
    rw [momA, momA, smul_mul_assoc, map_smul, smul_eq_mul]
  have hB : momB (c • f) = c * momB f := by
    rw [momB, momB, smul_mul_assoc, map_smul, smul_eq_mul]
  have hQ : momQ (c • f) = c * c * momQ f := by
    rw [momQ, momQ, smul_mul_smul_comm, map_smul, smul_eq_mul]
  rw [fwdD, fwdD, hA, hB, hQ, star_mul]
  linear_combination (c * momQ f * star (momB f)) * hcc

/-- `σ_W ∘ k` with `W = E(k)(0)`, the normalization of `k` at the origin. -/
private def fwdT (k : C(Circle, Circle)) : C(Circle, ℂ) :=
  if hk : ‖extension k 0‖ < 1 then
    ⟨fun ζ => diskAut (extension k 0) (k ζ), continuous_diskAut_comp _ hk k k.continuous⟩
  else 0

private lemma fwdT_apply {k : C(Circle, Circle)} (hk : ‖extension k 0‖ < 1) (ζ : Circle) :
    fwdT k ζ = diskAut (extension k 0) (k ζ) := by
  simp only [fwdT, hk, ↓reduceDIte, ContinuousMap.coe_mk]

private lemma fwdT_continuousOn :
    ContinuousOn fwdT {k : C(Circle, Circle) | Function.Bijective k} := by
  apply ContinuousMap.continuousOn_of_continuousOn_uncurry
  have hlt : ∀ p ∈ {k : C(Circle, Circle) | Function.Bijective k} ×ˢ (univ : Set Circle),
      ‖extension p.1 0‖ < 1 := fun p hp =>
    extension_mem_disk _ hp.1 p.1.continuous 0 (by simp)
  have hE : ContinuousOn (fun p : C(Circle, Circle) × Circle => extension p.1 0)
      ({k : C(Circle, Circle) | Function.Bijective k} ×ˢ univ) :=
    de_continuous_at_origin.comp continuousOn_fst (fun p hp => hp.1)
  have hev : Continuous (fun p : C(Circle, Circle) × Circle => ((p.1 p.2 : Circle) : ℂ)) :=
    continuous_subtype_val.comp continuous_eval
  have hmain : ContinuousOn ((fun p : C(Circle, Circle) × Circle =>
      ((p.1 p.2 : Circle) : ℂ) - extension p.1 0) /
      (fun p : C(Circle, Circle) × Circle =>
        1 - star (extension p.1 0) * ((p.1 p.2 : Circle) : ℂ)))
      ({k : C(Circle, Circle) | Function.Bijective k} ×ˢ univ) :=
    (hev.continuousOn.sub hE).div (continuousOn_const.sub
      ((continuous_star.comp_continuousOn hE).mul hev.continuousOn))
      (fun p hp => diskAut_denom_ne_zero _ _ (hlt p hp) (Circle.norm_coe _).le)
  refine hmain.congr fun p hp => ?_
  show fwdT p.1 p.2 = _
  rw [fwdT_apply (hlt p hp)]
  rfl

/-- The functional `k ↦ |D(σ_{E(k)(0)} ∘ k)|` minimized in Step 2. -/
private def fwdΦ (k : C(Circle, Circle)) : ℝ := ‖fwdD (fwdT k)‖

private lemma fwdΦ_pos {ρ : ℝ} {k : C(Circle, Circle)} (hk : k ∈ KImage ρ) : 0 < fwdΦ k := by
  obtain ⟨hkb, hko⟩ := KImage_spec hk
  have hWlt : ‖extension k 0‖ < 1 := extension_mem_disk _ hkb k.continuous 0 (by simp)
  have hplus : IsDiskAutPlus (diskAut (extension k 0)) :=
    ⟨1, extension k 0, by simp, hWlt, fun z => by simp⟩
  have haut : IsDiskAut (diskAut (extension k 0)) := Or.inl hplus
  set ψ := diskAutToCircle _ haut
  have hψb : Function.Bijective ψ := bijective_diskAutToCircle _ hplus haut
  have hψc : Continuous ψ := continuous_diskAutToCircle _ haut
  have hψo : HasIncreasingLift ψ :=
    CircleLift.hasIncreasingLift_of_isDiskAutPlus hplus ψ (fun _ => rfl)
  have hb : Function.Bijective (ψ ∘ k) := hψb.comp hkb
  have hc : Continuous (ψ ∘ k) := hψc.comp k.continuous
  have ho : HasIncreasingLift (ψ ∘ k) := CircleLift.hasIncreasingLift_comp hψo hko
  have h0 : extension (ψ ∘ k) 0 = 0 := by
    have := extension_naturality k (diskAut (extension k 0)) id ψ id haut
      (Or.inl isDiskAutPlus_id) (fun _ => rfl) (fun _ => rfl) hkb k.continuous hψb
      Function.bijective_id 0 (by simp)
    exact this.trans (diskAut_self _ hWlt)
  have hT : fwdT k = toCM (ψ ∘ k) hc := by
    ext ζ
    rw [fwdT_apply hWlt]
    rfl
  obtain ⟨e1, -⟩ := disc_wirt_formula _ hb hc ho h0
  have hq := norm_momQ_lt_one _ hb hc
  have hr : ((1 - ‖momQ (toCM (ψ ∘ k) hc)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 (sub_pos.2 ?_).ne'
    nlinarith [norm_nonneg (momQ (toCM (ψ ∘ k) hc))]
  have hwz := wirtZ_extension_ne_zero _ hb hc ho 0 (by simp)
  rw [fwdΦ, hT, norm_pos_iff, fwdD, ← e1]
  exact mul_ne_zero hr hwz

/-- **Step 2 (compactness form)**: `|D|` is bounded below on the normalized family. -/
private lemma fwd_lower_bound (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ k ∈ KImage ρ, c ≤ fwdΦ k := by
  have hne : (KImage ρ).Nonempty :=
    ⟨_, kConj_mem_KImage _ (affine_mem_KFamily ρ hρ)⟩
  have hcont : ContinuousOn fwdΦ (KImage ρ) :=
    ((continuous_norm.comp fwdD_continuous).comp_continuousOn fwdT_continuousOn).mono
      (fun k hk => (KImage_spec hk).1)
  obtain ⟨k₀, hk₀, hmin⟩ := (compact_KFamily ρ hρ).exists_isMinOn hne hcont
  exact ⟨fwdΦ k₀, fwdΦ_pos hk₀, fun k hk => hmin hk⟩

/-! ## Steps 1a–1e: normalization and the dilatation formula -/

/-- **Step 1a**: after the affine normalization `h̃ = A ∘ h ∘ B` with `e(h̃)(i) = i`,
`|μ_{e(h)}(B i)| = |μ_{E(g)}(0)|` for `g = γ ∘ h̃ ∘ γ⁻¹`, and `E(g)(0) = 0`. -/
private lemma fwd_normalize {h : ℝ → ℝ} (hh : StrictMono h) (hc : Continuous h)
    (hs : Function.Surjective h) {a b c d : ℝ} (ha : 0 < a) (hc' : 0 < c)
    (hI : (a : ℂ) * douadyEarle h ((c : ℂ) * Complex.I + d) + b = Complex.I) :
    ‖complexDilatation (douadyEarle h) ((c : ℂ) * Complex.I + d)‖ =
        ‖complexDilatation (extension (cayleyConj (fun t => a * h (c * t + d) + b))) 0‖ ∧
      extension (cayleyConj (fun t => a * h (c * t + d) + b)) 0 = 0 := by
  obtain ⟨htm, htc, hts⟩ := fwd_affine_props hh hc hs ha hc' b d
  have hI' : (0 : ℝ) < Complex.I.im := by simp
  constructor
  · rw [← norm_complexDilatation_conformal_naturality h hh hc hs a b c d ha hc' _ hI',
      norm_complexDilatation_douadyEarle _ htm htc hts _ hI', cayley_I]
  · have e1 := douadyEarle_eq_cayley _ htm htc hts _ hI'
    rw [conformal_naturality h hh hc hs a b c d ha hc' _ hI', hI, cayley_I] at e1
    have hlt := extension_mem_disk _ (bijective_cayleyConj htm htc hts)
      (continuous_cayleyConj htm htc hts) 0 (by simp)
    have hne : extension (cayleyConj (fun t => a * h (c * t + d) + b)) 0 ≠ 1 := by
      intro h1
      rw [h1] at hlt
      simp at hlt
    rw [← cayley_cayleyInv hne, ← e1, cayley_I]

/-- **Steps 1c–1e**: `|μ_{E(g)}(0)| = |N| / |D|`. -/
private lemma fwd_mu_eq (g : Circle → Circle) (hgb : Function.Bijective g) (hgc : Continuous g)
    (hor : HasIncreasingLift g) (h0 : extension g 0 = 0) :
    ‖complexDilatation (extension g) 0‖ =
      ‖momB (toCM g hgc) + momQ (toCM g hgc) * star (momA (toCM g hgc))‖ /
        ‖fwdD (toCM g hgc)‖ := by
  obtain ⟨e1, e2⟩ := disc_wirt_formula g hgb hgc hor h0
  have hq := norm_momQ_lt_one g hgb hgc
  have hr : ((1 - ‖momQ (toCM g hgc)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    refine Complex.ofReal_ne_zero.2 (sub_pos.2 ?_).ne'
    nlinarith [norm_nonneg (momQ (toCM g hgc))]
  rw [← norm_div, fwdD, ← e1, ← e2, mul_div_mul_left _ _ hr, complexDilatation]

/-- **Step 2**: `|D(g)| ≥ c` for the normalized boundary map `g` of `h` at `z₀`,
through `g = λ · σ_W ∘ g_H` with `H = normalizeLoc h x₀ y₀ ∈ 𝒦_ρ`. -/
private lemma fwd_D_lower {ρ : ℝ} (hρ : 1 ≤ ρ) {c₀ : ℝ} (hcΦ : ∀ k ∈ KImage ρ, c₀ ≤ fwdΦ k)
    {h : ℝ → ℝ} (hqs : Quasisymmetric h ρ) (z₀ w₀ : ℂ) (hz₀ : 0 < z₀.im)
    (hw₀ : douadyEarle h z₀ = w₀)
    (hgc : Continuous (cayleyConj
      (fun t => w₀.im⁻¹ * h (z₀.im * t + z₀.re) + -(w₀.im⁻¹ * w₀.re)))) :
    c₀ ≤ ‖fwdD (toCM (cayleyConj
      (fun t => w₀.im⁻¹ * h (z₀.im * t + z₀.re) + -(w₀.im⁻¹ * w₀.re))) hgc)‖ := by
  have hmono := hqs.1
  have hv : 0 < w₀.im := hw₀ ▸ douadyEarle_im_pos h hqs.1 hqs.2.1 hqs.2.2.1 z₀ hz₀
  have hH := normalizeLoc_mem_KFamily hρ hqs z₀.re hz₀
  have hkI := kConj_mem_KImage _ hH
  have hL : 0 < h (z₀.re + z₀.im) - h (z₀.re - z₀.im) := sub_pos.2 (hmono (by linarith))
  obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = (h (z₀.re + z₀.im) - h (z₀.re - z₀.im)) / w₀.im :=
    ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (h (z₀.re - z₀.im) - w₀.re) / w₀.im := ⟨_, rfl⟩
  have hα : 0 < α := hαdef ▸ div_pos hL hv
  have hfun : (fun t => w₀.im⁻¹ * h (z₀.im * t + z₀.re) + -(w₀.im⁻¹ * w₀.re)) =
      fun t => α * normalizeLoc h z₀.re z₀.im t + β := by
    funext t
    simp only [normalizeLoc, hαdef, hβdef]
    rw [add_comm z₀.re (z₀.im * t)]
    field_simp
    ring
  have hgeq : ∀ ζ : Circle, ((cayleyConj
      (fun t => w₀.im⁻¹ * h (z₀.im * t + z₀.re) + -(w₀.im⁻¹ * w₀.re)) ζ : Circle) : ℂ) =
      fwdMob α β ((kConj _ hH ζ : Circle) : ℂ) := by
    intro ζ
    rw [hfun]
    exact fwd_cayleyConj_affine hα β _ ζ
  have hWlt : ‖extension (kConj _ hH) 0‖ < 1 :=
    extension_mem_disk _ (KImage_spec hkI).1 (kConj _ hH).continuous 0 (by simp)
  have hne : extension (kConj _ hH) 0 ≠ 1 := by
    intro h1
    rw [h1] at hWlt
    simp at hWlt
  have hP : fwdP α β = cayleyInv (extension (kConj _ hH) 0) := by
    rw [← douadyEarle_I_eq _ hH, douadyEarle_normalizeLoc hqs z₀.re hz₀, Complex.re_add_im, hw₀,
      fwdP, hαdef, hβdef]
    have hv' : (w₀.im : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
    have hL' : ((h (z₀.re + z₀.im) : ℝ) : ℂ) - ((h (z₀.re - z₀.im) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hL.ne'
    conv_rhs => rw [← Complex.re_add_im w₀]
    push_cast
    field_simp
    ring
  have hW : cayley (fwdP α β) = extension (kConj _ hH) 0 := by
    rw [hP, cayley_cayleyInv hne]
  have hnorm : ‖star (lambdaFactor (fwdP α β))‖ = 1 := by
    rw [norm_star]
    exact lambdaFactor_norm _ (fwdP_im hα β)
  have hT : toCM (cayleyConj
      (fun t => w₀.im⁻¹ * h (z₀.im * t + z₀.re) + -(w₀.im⁻¹ * w₀.re))) hgc =
      star (lambdaFactor (fwdP α β)) • fwdT (kConj _ hH) := by
    ext ζ
    rw [toCM_apply, hgeq ζ, ContinuousMap.smul_apply, smul_eq_mul, fwdT_apply hWlt, fwdMob, hW]
  rw [hT, fwdD_smul hnorm, norm_mul, hnorm, one_mul]
  exact hcΦ _ hkI

/-! ## Step 3: the numerator -/

/-- **Steps 3a–3d**: `|N| ≤ 5 ⨍ |g - m|` for `m` the Cayley conjugate of an
increasing affine map. -/
private lemma fwd_N_upper (g : Circle → Circle) (hgc : Continuous g)
    (hmean : circleMean (toCM g hgc) = 0) {α : ℝ} (hα : 0 < α) (β : ℝ) :
    ‖momB (toCM g hgc) + momQ (toCM g hgc) * star (momA (toCM g hgc))‖ ≤
      5 * ((2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖((g (Circle.exp θ) : Circle) : ℂ) -
          ((cayleyConj (fun t => α * t + β) (Circle.exp θ) : Circle) : ℂ)‖) :=
  disc_numerator_le g hgc hmean (fwdMob α β) (fwdMob_isDiskAutPlus hα β) _ (fun ζ => by
    have := fwd_cayleyConj_affine hα β id ζ
    rwa [fwd_cayleyConj_id] at this)

/-- **Step 3e, transfer**: the circle average of `|g - m|` is the `P_i`-average on `ℝ`. -/
private lemma fwd_avg_cayley (g m : Circle → Circle) (hgc : Continuous g) (hmc : Continuous m) :
    (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        ‖((g (Circle.exp θ) : Circle) : ℂ) - ((m (Circle.exp θ) : Circle) : ℂ)‖ =
      ∫ t, ‖((g (cayleyCircle t) : Circle) : ℂ) - ((m (cayleyCircle t) : Circle) : ℂ)‖ *
        poissonKernelUHP Complex.I t := by
  have hF : Continuous (fun ζ : Circle =>
      ((‖((g ζ : Circle) : ℂ) - ((m ζ : Circle) : ℂ)‖ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_subtype_val.comp hgc).sub (continuous_subtype_val.comp hmc)).norm
  have key := harmonicMeasureAvg_cayley Complex.I (by simp) _ hF
  rw [cayley_I, harmonicMeasureAvg_zero_eq, intervalIntegral.integral_ofReal] at key
  have e2 : (∫ t : ℝ, ((‖((g (cayleyCircle t) : Circle) : ℂ) -
        ((m (cayleyCircle t) : Circle) : ℂ)‖ : ℝ) : ℂ) *
        ((poissonKernelUHP Complex.I t : ℝ) : ℂ)) =
      ((∫ t, ‖((g (cayleyCircle t) : Circle) : ℂ) - ((m (cayleyCircle t) : Circle) : ℂ)‖ *
        poissonKernelUHP Complex.I t : ℝ) : ℂ) := by
    exact (integral_congr_ae (Filter.Eventually.of_forall fun t =>
      (Complex.ofReal_mul _ _).symm)).trans integral_ofReal
  rw [e2] at key
  exact_mod_cast key

/-- The integrand of the Forward Inequality. -/
private def fwdG (h : ℝ → ℝ) (z₀ w₀ : ℂ) (κ τ : ℝ) (t : ℝ) : ℝ :=
  (2 * w₀.im * |h t - (κ * t + τ)|) /
      (‖(h t : ℂ) - star w₀‖ * ‖(κ * t + τ : ℂ) - star w₀‖) *
    poissonKernelUHP z₀ t

/-- **Step 3e, pointwise**: the Cayley-difference identity after the substitution
`s = x₀ + y₀ t`. -/
private lemma fwd_pointwise (h : ℝ → ℝ) (z₀ w₀ : ℂ) (hz : 0 < z₀.im) (hw : 0 < w₀.im)
    (κ τ t : ℝ) :
    ‖cayley ((w₀.im⁻¹ * h (z₀.im * t + z₀.re) + -(w₀.im⁻¹ * w₀.re) : ℝ) : ℂ) -
        cayley ((w₀.im⁻¹ * κ * z₀.im * t + (w₀.im⁻¹ * (κ * z₀.re + τ) + -(w₀.im⁻¹ * w₀.re)) :
          ℝ) : ℂ)‖ * poissonKernelUHP Complex.I t =
      z₀.im * fwdG h z₀ w₀ κ τ (z₀.im * t + z₀.re) := by
  set s := z₀.im * t + z₀.re with hs
  set u : ℝ := w₀.im⁻¹ * h s + -(w₀.im⁻¹ * w₀.re) with hu
  set v : ℝ := w₀.im⁻¹ * κ * z₀.im * t + (w₀.im⁻¹ * (κ * z₀.re + τ) + -(w₀.im⁻¹ * w₀.re))
    with hv
  have hsI : star Complex.I = -Complex.I := Complex.conj_I
  have hsw : star w₀ = (w₀.re : ℂ) - (w₀.im : ℂ) * Complex.I := by
    conv_lhs => rw [← Complex.re_add_im w₀]
    rw [star_add, star_mul, hsI, Complex.star_def, Complex.conj_ofReal, Complex.conj_ofReal]
    ring
  have hcay : ∀ r : ℝ, cayley (r : ℂ) = ((r : ℂ) - Complex.I) / ((r : ℂ) - star Complex.I) := by
    intro r
    rw [cayley, hsI, sub_neg_eq_add]
  have hwne : w₀.im ≠ 0 := hw.ne'
  have hv' : (w₀.im : ℂ) ≠ 0 := by exact_mod_cast hwne
  have hA : ‖(u : ℂ) - star Complex.I‖ = ‖(h s : ℂ) - star w₀‖ / w₀.im := by
    have : (u : ℂ) - star Complex.I = ((w₀.im⁻¹ : ℝ) : ℂ) * ((h s : ℂ) - star w₀) := by
      rw [hsI, hsw, hu]
      push_cast
      field_simp
      ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hw.le),
      inv_mul_eq_div]
  have hB : ‖(v : ℂ) - star Complex.I‖ = ‖((κ : ℂ) * s + τ) - star w₀‖ / w₀.im := by
    have : (v : ℂ) - star Complex.I = ((w₀.im⁻¹ : ℝ) : ℂ) * (((κ : ℂ) * s + τ) - star w₀) := by
      rw [hsI, hsw, hv, hs]
      push_cast
      field_simp
      ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hw.le),
      inv_mul_eq_div]
  have hD : |u - v| = |h s - (κ * s + τ)| / w₀.im := by
    rw [show u - v = w₀.im⁻¹ * (h s - (κ * s + τ)) by rw [hu, hv, hs]; ring, abs_mul,
      abs_of_pos (inv_pos.2 hw), inv_mul_eq_div]
  have hP : poissonKernelUHP Complex.I t = z₀.im * poissonKernelUHP z₀ s := by
    simp only [poissonKernelUHP, Complex.I_re, Complex.I_im, hs]
    rw [show z₀.im * t + z₀.re - z₀.re = z₀.im * t by ring]
    field_simp
    ring
  have hA0 : ‖(h s : ℂ) - star w₀‖ ≠ 0 := by
    rw [norm_ne_zero_iff, hsw]
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  have hB0 : ‖((κ : ℂ) * s + τ) - star w₀‖ ≠ 0 := by
    rw [norm_ne_zero_iff, hsw]
    intro h0
    have := congrArg Complex.im h0
    simp at this
    linarith
  rw [hcay u, hcay v, cayley_difference_identity u v Complex.I (by simp), hA, hB, hD, hP, fwdG]
  simp only [Complex.I_im]
  field_simp
  try ring

/-- The substitution `s = x + y t`: `∫ y G(y t + x) dt = ∫ G`. -/
private lemma fwd_change_var (G : ℝ → ℝ) {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ∫ t, y * G (y * t + x) = ∫ s, G s := by
  rw [integral_const_mul]
  have h1 := Measure.integral_comp_mul_left (fun s => G (s + x)) y
  rw [h1, integral_add_right_eq_self G x, smul_eq_mul, abs_inv, abs_of_pos hy, ← mul_assoc,
    mul_inv_cancel₀ hy.ne', one_mul]

/-- **Theorem (Forward Inequality)**: let `h` be a `ρ`-quasisymmetric
increasing homeomorphism of `ℝ`, `z₀ = x₀ + iy₀ ∈ 𝕌`, `w₀ = e(h)(z₀)`. Then
for any affine map `M(t) = κt + τ` with `κ > 0`,
`|μ_{e(h)}(z₀)| ≤ C(ρ) ∫ 2v₀ |h(t) - M(t)| / (|h(t) - w̄₀| |M(t) - w̄₀|) P_{z₀}(t) dt`,
where `C(ρ)` depends only on `ρ`. -/
theorem forward_inequality (ρ : ℝ) (hρ : 1 ≤ ρ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ h : ℝ → ℝ, Quasisymmetric h ρ →
        ∀ z₀ : ℂ, 0 < z₀.im →
          ∀ κ τ : ℝ, 0 < κ →
            ‖complexDilatation (douadyEarle h) z₀‖ ≤
              C * ∫ t : ℝ,
                (2 * (douadyEarle h z₀).im * |h t - (κ * t + τ)|) /
                  (‖(h t : ℂ) - star (douadyEarle h z₀)‖ *
                    ‖(κ * t + τ : ℂ) - star (douadyEarle h z₀)‖) *
                poissonKernelUHP z₀ t := by
  obtain ⟨c₀, hc₀, hcΦ⟩ := fwd_lower_bound ρ hρ
  refine ⟨5 / c₀, by positivity, ?_⟩
  intro h hqs z₀ hz₀ κ τ hκ
  have hmono := hqs.1
  have hcont := hqs.2.1
  have hsurj := hqs.2.2.1
  obtain ⟨w₀, hw₀⟩ : ∃ w, douadyEarle h z₀ = w := ⟨_, rfl⟩
  have hv : 0 < w₀.im := hw₀ ▸ douadyEarle_im_pos h hmono hcont hsurj z₀ hz₀
  rw [hw₀]
  have ha : 0 < w₀.im⁻¹ := inv_pos.2 hv
  obtain ⟨htm, htc, hts⟩ :=
    fwd_affine_props hmono hcont hsurj ha hz₀ (-(w₀.im⁻¹ * w₀.re)) z₀.re
  have hα₂ : 0 < w₀.im⁻¹ * κ * z₀.im := by positivity
  obtain ⟨hLm, hLc, hLs⟩ :=
    fwd_lin_props hα₂ (w₀.im⁻¹ * (κ * z₀.re + τ) + -(w₀.im⁻¹ * w₀.re))
  have hgc := continuous_cayleyConj htm htc hts
  have hgb := bijective_cayleyConj htm htc hts
  have hgo := hasIncreasingLift_cayleyConj htm htc hts
  have hmc := continuous_cayleyConj hLm hLc hLs
  have hz₀eq : (z₀.im : ℂ) * Complex.I + (z₀.re : ℂ) = z₀ := by
    rw [add_comm]
    exact Complex.re_add_im z₀
  have hI : ((w₀.im⁻¹ : ℝ) : ℂ) * douadyEarle h ((z₀.im : ℂ) * Complex.I + (z₀.re : ℂ)) +
      ((-(w₀.im⁻¹ * w₀.re) : ℝ) : ℂ) = Complex.I := by
    rw [hz₀eq, hw₀]
    apply Complex.ext <;> simp [hv.ne']
  obtain ⟨hμ, h0⟩ := fwd_normalize hmono hcont hsurj ha hz₀ hI
  rw [hz₀eq] at hμ
  rw [hμ, fwd_mu_eq _ hgb hgc hgo h0]
  have hD := fwd_D_lower hρ hcΦ hqs z₀ w₀ hz₀ hw₀ hgc
  have hN := fwd_N_upper _ hgc (circleMean_eq_zero_of_extension_zero _ hgb hgc h0) hα₂
    (w₀.im⁻¹ * (κ * z₀.re + τ) + -(w₀.im⁻¹ * w₀.re))
  have hint : (2 * Real.pi)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
      ‖((cayleyConj (fun t => w₀.im⁻¹ * h (z₀.im * t + z₀.re) + -(w₀.im⁻¹ * w₀.re))
          (Circle.exp θ) : Circle) : ℂ) -
        ((cayleyConj (fun t => w₀.im⁻¹ * κ * z₀.im * t +
          (w₀.im⁻¹ * (κ * z₀.re + τ) + -(w₀.im⁻¹ * w₀.re))) (Circle.exp θ) : Circle) : ℂ)‖ =
      ∫ s, fwdG h z₀ w₀ κ τ s := by
    rw [fwd_avg_cayley _ _ hgc hmc, ← fwd_change_var (fwdG h z₀ w₀ κ τ) hz₀ z₀.re]
    congr 1
    funext t
    rw [cayleyConj_cayleyCircle_coe, cayleyConj_cayleyCircle_coe]
    exact fwd_pointwise h z₀ w₀ hz₀ hv κ τ t
  rw [hint] at hN
  calc _ ≤ (5 * ∫ s, fwdG h z₀ w₀ κ τ s) / c₀ :=
        div_le_div₀ ((norm_nonneg _).trans hN) hN hc₀ hD
    _ = 5 / c₀ * ∫ s, fwdG h z₀ w₀ κ τ s := by ring

end VanishingCarleson

end
