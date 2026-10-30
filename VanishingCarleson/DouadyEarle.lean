/-
# Quasisymmetric homeomorphisms and the Douady–Earle extension on `𝕌`

Definitions of quasisymmetry, local absolute continuity and strong symmetry,
the barycentric equation of the upper half-plane and the Douady–Earle
extension `e(h) : 𝕌 → 𝕌` it defines (§2.3 of the paper), together with

* **existence and uniqueness of the barycenter** (`barycenter_existsUnique`),
  derived from the disk theory of `DouadyEarleExt` through the Cayley
  transform: for `z, w ∈ 𝕌` the half-plane equation at `(z, w)` is the disk
  equation of the Cayley conjugate `g_h = γ ∘ h ∘ γ⁻¹` at `(γ(z), γ(w))`
  (`barycenterEq_iff_baryEq`);
* the identity `e(h) = γ⁻¹ ∘ E(g_h) ∘ γ` (`douadyEarle_eq_cayley`), through
  which the regularity of `E(g_h)` and its complex dilatation pass to `e(h)`;
* **conformal naturality** under the real affine maps of `𝕌`
  (`conformal_naturality`), the form in which the paper uses Lemma
  (Conformal Naturality).

The complex dilatation is `complexDilatation` of `DouadyEarleExt`,
`μ_F = F_z̄ / F_z` with the Wirtinger derivatives `wirtZ`, `wirtZbar`.
-/
import Mathlib
import VanishingCarleson.Cayley

open MeasureTheory Real Set

noncomputable section

namespace VanishingCarleson

/-! ## Quasisymmetric homeomorphisms of the real line -/

/-- `ρ`-quasisymmetry of an increasing homeomorphism `h : ℝ → ℝ`:
adjacent intervals of equal length have comparable images, with the
two-sided bound `ρ⁻¹ ≤ (h(x+t) - h(x)) / (h(x) - h(x-t)) ≤ ρ`. -/
def Quasisymmetric (h : ℝ → ℝ) (ρ : ℝ) : Prop :=
  StrictMono h ∧ Continuous h ∧ Function.Surjective h ∧
    ∀ x t : ℝ, 0 < t →
      h (x + t) - h x ≤ ρ * (h x - h (x - t)) ∧
      h x - h (x - t) ≤ ρ * (h (x + t) - h x)

/-- Local absolute continuity: on every compact interval, `f` is the
indefinite integral of an integrable function. -/
def LocallyAbsolutelyContinuous (f : ℝ → ℝ) : Prop :=
  Continuous f ∧
    ∀ a b : ℝ, a < b → ∃ g : ℝ → ℝ, IntervalIntegrable g volume a b ∧
      ∀ t : ℝ, t ∈ Set.Icc a b → f t = f a + ∫ s in a..t, g s

/-- Strong symmetry `SS(ℝ)`: locally absolutely continuous, `f'` an
`A_∞`-weight and `log f' ∈ VMO(ℝ)`. -/
def StronglySymmetric (f : ℝ → ℝ) : Prop :=
  StrictMono f ∧ Function.Surjective f ∧ LocallyAbsolutelyContinuous f ∧
    AInfinityWeight (deriv f) ∧ VMO (fun t => Real.log (deriv f t))

/-! ## The barycentric equation and the extension on the upper half-plane -/

/-- The barycentric equation at `z ∈ 𝕌` with candidate image `w`:
`∫ (h(t) - w)/(h(t) - w̄) P_z(t) dt = 0`. -/
def barycenterEq (h : ℝ → ℝ) (z w : ℂ) : Prop :=
  ∫ t : ℝ, (((h t : ℂ) - w) / ((h t : ℂ) - star w)) * (poissonKernelUHP z t : ℂ) = 0

/-- A real point is never the conjugate of a point of `𝕌`. -/
private theorem deAux_ofReal_sub_star_ne_zero (u : ℝ) {w : ℂ} (hw : 0 < w.im) :
    (u : ℂ) - star w ≠ 0 := by
  intro h0
  have him := congrArg Complex.im h0
  have hstar : (star w).im = -w.im := Complex.conj_im w
  simp only [Complex.sub_im, Complex.ofReal_im, hstar, Complex.zero_im] at him
  linarith

private theorem deAux_ofReal_ne_neg_I (u : ℝ) : (u : ℂ) ≠ -Complex.I := by
  intro h0
  have him := congrArg Complex.im h0
  norm_num at him

private theorem deAux_ne_neg_I {y : ℂ} (hy : 0 < y.im) : y ≠ -Complex.I := by
  rintro rfl
  norm_num at hy

private theorem deAux_ne_one {W : ℂ} (hW : ‖W‖ < 1) : W ≠ 1 := by
  rintro rfl
  rw [norm_one] at hW
  exact lt_irrefl _ hW

/-- `|conj d / d| = 1` for `d ≠ 0`. -/
private theorem deAux_norm_star_div_self {d : ℂ} (hd : d ≠ 0) : ‖star d / d‖ = 1 := by
  rw [norm_div, norm_star, div_self (norm_ne_zero_iff.mpr hd)]

/-- `γ'(z) = 2i / (z + i)²`. -/
private theorem deAux_hasDerivAt_cayley {z : ℂ} (hz : z + Complex.I ≠ 0) :
    HasDerivAt cayley (2 * Complex.I / (z + Complex.I) ^ 2) z := by
  have h1 : HasDerivAt (fun y : ℂ => y - Complex.I) 1 z := (hasDerivAt_id' z).sub_const _
  have h2 : HasDerivAt (fun y : ℂ => y + Complex.I) 1 z := (hasDerivAt_id' z).add_const _
  exact (h1.fun_div h2 hz).congr_deriv (by ring)

/-- `(γ⁻¹)'(ζ) = 2i / (1 - ζ)²`. -/
private theorem deAux_hasDerivAt_cayleyInv {ζ : ℂ} (hζ : 1 - ζ ≠ 0) :
    HasDerivAt cayleyInv (2 * Complex.I / (1 - ζ) ^ 2) ζ := by
  have h1 : HasDerivAt (fun y : ℂ => Complex.I * (1 + y)) (Complex.I * 1) ζ :=
    ((hasDerivAt_id' ζ).const_add 1).const_mul Complex.I
  have h2 : HasDerivAt (fun y : ℂ => 1 - y) (-1) ζ := (hasDerivAt_id' ζ).const_sub 1
  exact (h1.fun_div h2 hζ).congr_deriv (by ring)

/-- **The barycentric equation under the Cayley transform.**  For an
increasing homeomorphism `h` and `z, w ∈ 𝕌`, the half-plane barycentric
equation of `h` at `(z, w)` is the disk barycentric equation (3.1) of the
Cayley conjugate `g_h` at `(γ(z), γ(w))`: the integrands differ by the
unimodular factor `λ(w)` of the transfer identity (2.1), and `P_z(t) dt` is
the pull-back of the harmonic measure at `γ(z)`. -/
theorem barycenterEq_iff_baryEq (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (z w : ℂ) (hz : 0 < z.im) (hw : 0 < w.im) :
    barycenterEq h z w ↔ baryEq (cayleyConj h) (cayley z) (cayley w) := by
  have hWn : ‖cayley w‖ < 1 := norm_cayley_lt_one hw
  have hgc : Continuous (cayleyConj h) := continuous_cayleyConj hh hc hsurj
  have hden : ∀ ζ : Circle, (1 : ℂ) - star (cayley w) * (cayleyConj h ζ : ℂ) ≠ 0 := by
    intro ζ h0
    have h1 : ‖star (cayley w) * (cayleyConj h ζ : ℂ)‖ = ‖cayley w‖ := by
      rw [norm_mul, norm_star, Circle.norm_coe, mul_one]
    rw [← sub_eq_zero.mp h0, norm_one] at h1
    linarith
  set F : Circle → ℂ := fun ζ =>
    ((cayleyConj h ζ : ℂ) - cayley w) / (1 - star (cayley w) * (cayleyConj h ζ : ℂ)) with hF
  have hFc : Continuous F :=
    ((continuous_subtype_val.comp hgc).sub continuous_const).div
      (continuous_const.sub (continuous_const.mul (continuous_subtype_val.comp hgc))) hden
  have hbary : baryEq (cayleyConj h) (cayley z) (cayley w) ↔
      harmonicMeasureAvg (cayley z) F = 0 := Iff.rfl
  have hpt : ∀ t : ℝ, F (cayleyCircle t) =
      lambdaFactor w * (((h t : ℂ) - w) / ((h t : ℂ) - star w)) := by
    intro t
    rw [← cayley_involution_transfer w (h t : ℂ) hw
      (sub_ne_zero.mp (deAux_ofReal_sub_star_ne_zero (h t) hw)) (deAux_ofReal_ne_neg_I (h t)),
      hF]
    simp only [cayleyConj_cayleyCircle_coe, diskInvolution]
  have hlam : lambdaFactor w ≠ 0 := by
    intro h0
    have h1 := lambdaFactor_norm w hw
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  rw [hbary, harmonicMeasureAvg_cayley z hz F hFc]
  simp_rw [hpt, mul_assoc]
  rw [integral_const_mul, mul_eq_zero, or_iff_right hlam]
  exact Iff.rfl

/-- Douady–Earle: existence **and uniqueness** of the barycenter of a
homeomorphism of `ℝ̄` at `z ∈ 𝕌`; the solution itself lies in `𝕌`.
Proved from the disk case (`_root_.barycenter_existsUnique`) through
`barycenterEq_iff_baryEq`. -/
theorem barycenter_existsUnique (h : ℝ → ℝ)
    (hh : StrictMono h) (hc : Continuous h) (hsurj : Function.Surjective h)
    (z : ℂ) (hz : 0 < z.im) :
    ∃! w : ℂ, 0 < w.im ∧ barycenterEq h z w := by
  obtain ⟨W, ⟨hW, hWeq⟩, huniq⟩ := _root_.barycenter_existsUnique (cayleyConj h)
    (bijective_cayleyConj hh hc hsurj) (continuous_cayleyConj hh hc hsurj) (cayley z)
    (norm_cayley_lt_one hz)
  have hwim : 0 < (cayleyInv W).im := im_cayleyInv_pos hW
  refine ⟨cayleyInv W, ⟨hwim, ?_⟩, ?_⟩
  · rw [barycenterEq_iff_baryEq h hh hc hsurj z _ hz hwim, cayley_cayleyInv (deAux_ne_one hW)]
    exact hWeq
  · rintro y ⟨hy, hyeq⟩
    rw [barycenterEq_iff_baryEq h hh hc hsurj z y hz hy] at hyeq
    have hyW : cayley y = W := huniq (cayley y) ⟨norm_cayley_lt_one hy, hyeq⟩
    rw [← hyW, cayleyInv_cayley (deAux_ne_neg_I hy)]

/-- Auxiliary conditional existence: there is a point `w : ℂ` which —
whenever `h` is a homeomorphism of `ℝ̄` and `z ∈ 𝕌` — lies in `𝕌` and solves
the barycentric equation. (The uniqueness in `barycenter_existsUnique` then
makes this point *the* barycenter.) -/
private theorem douadyEarle_aux (h : ℝ → ℝ) (z : ℂ) :
    ∃ w : ℂ,
      (StrictMono h ∧ Continuous h ∧ Function.Surjective h ∧ 0 < z.im) →
        0 < w.im ∧ barycenterEq h z w := by
  by_cases hcond : StrictMono h ∧ Continuous h ∧ Function.Surjective h ∧ 0 < z.im
  · obtain ⟨w, hw⟩ :=
      (barycenter_existsUnique h hcond.1 hcond.2.1 hcond.2.2.1 z hcond.2.2.2).exists
    exact ⟨w, fun _ => hw⟩
  · exact ⟨0, fun h' => absurd h' hcond⟩

/-- The Douady–Earle barycentric extension `e(h) : 𝕌 → 𝕌`, evaluated at `z`.
For a homeomorphism `h` of `ℝ̄` and `z ∈ 𝕌` this is *the* unique barycenter;
outside that regime it is an arbitrary point. -/
def douadyEarle (h : ℝ → ℝ) (z : ℂ) : ℂ :=
  Classical.choose (douadyEarle_aux h z)

/-- The extension at `z ∈ 𝕌` of a homeomorphism of `ℝ̄` lands in `𝕌` and
satisfies the barycentric equation. -/
theorem douadyEarle_spec (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (z : ℂ) (hz : 0 < z.im) :
    0 < (douadyEarle h z).im ∧ barycenterEq h z (douadyEarle h z) :=
  Classical.choose_spec (douadyEarle_aux h z) ⟨hh, hc, hsurj, hz⟩

/-- The extension maps the upper half-plane into itself. -/
theorem douadyEarle_im_pos (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (z : ℂ) (hz : 0 < z.im) :
    0 < (douadyEarle h z).im :=
  (douadyEarle_spec h hh hc hsurj z hz).1

/-- The extension solves the barycentric equation. -/
theorem douadyEarle_eq (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (z : ℂ) (hz : 0 < z.im) :
    barycenterEq h z (douadyEarle h z) :=
  (douadyEarle_spec h hh hc hsurj z hz).2

/-- **`e(h) = γ⁻¹ ∘ E(g_h) ∘ γ`** on `𝕌` (§2.3, "Relation via the Cayley
transformation"), where `E` is the Douady–Earle extension of the disk. -/
theorem douadyEarle_eq_cayley (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (z : ℂ) (hz : 0 < z.im) :
    douadyEarle h z = cayleyInv (extension (cayleyConj h) (cayley z)) := by
  have hZ : ‖cayley z‖ < 1 := norm_cayley_lt_one hz
  have hb := bijective_cayleyConj hh hc hsurj
  have hgc := continuous_cayleyConj hh hc hsurj
  have hE := extension_mem_disk (cayleyConj h) hb hgc (cayley z) hZ
  have him := im_cayleyInv_pos hE
  refine (barycenter_existsUnique h hh hc hsurj z hz).unique
    (douadyEarle_spec h hh hc hsurj z hz) ⟨him, ?_⟩
  rw [barycenterEq_iff_baryEq h hh hc hsurj z _ hz him, cayley_cayleyInv (deAux_ne_one hE)]
  exact extension_baryEq _ hb hgc _ hZ

/-- The identity `e(h) = γ⁻¹ ∘ E(g_h) ∘ γ` holds on a neighbourhood of every
point of `𝕌`, so derivatives of `e(h)` may be computed from `E(g_h)`. -/
theorem douadyEarle_eventuallyEq_cayley (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (z : ℂ) (hz : 0 < z.im) :
    douadyEarle h =ᶠ[nhds z] fun u => cayleyInv (extension (cayleyConj h) (cayley u)) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with u hu
  exact douadyEarle_eq_cayley h hh hc hsurj u hu

/-- The disk extension `E(g_h)` is real-differentiable at `γ(z)` for `z ∈ 𝕌`. -/
private theorem deAux_differentiableAt_extension {h : ℝ → ℝ} (hh : StrictMono h)
    (hc : Continuous h) (hsurj : Function.Surjective h) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℝ (extension (cayleyConj h)) (cayley z) := by
  have han := extension_analyticOn_disk (cayleyConj h) (bijective_cayleyConj hh hc hsurj)
    (continuous_cayleyConj hh hc hsurj)
  have hmem : cayley z ∈ Metric.ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using norm_cayley_lt_one hz
  exact ((Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.mp han) _ hmem).differentiableAt

/-- The modulus of the complex dilatation of `e(h)` at `z` is that of `E(g_h)`
at `γ(z)`: post-composition with the conformal map `γ⁻¹` leaves `μ`
unchanged, and pre-composition with `γ` multiplies it by the unimodular
factor `conj γ'(z) / γ'(z)`. -/
theorem norm_complexDilatation_douadyEarle (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (z : ℂ) (hz : 0 < z.im) :
    ‖complexDilatation (douadyEarle h) z‖ =
      ‖complexDilatation (extension (cayleyConj h)) (cayley z)‖ := by
  have hZ : ‖cayley z‖ < 1 := norm_cayley_lt_one hz
  have hE := extension_mem_disk (cayleyConj h) (bijective_cayleyConj hh hc hsurj)
    (continuous_cayleyConj hh hc hsurj) (cayley z) hZ
  set E := extension (cayleyConj h)
  have hEd : DifferentiableAt ℝ E (cayley z) := deAux_differentiableAt_extension hh hc hsurj hz
  have hzI : z + Complex.I ≠ 0 := by
    rw [← sub_neg_eq_add]
    exact sub_ne_zero.mpr (deAux_ne_neg_I hz)
  have hcay := deAux_hasDerivAt_cayley hzI
  have h1E : 1 - E (cayley z) ≠ 0 := sub_ne_zero.mpr (deAux_ne_one hE).symm
  have hinv := deAux_hasDerivAt_cayleyInv h1E
  have hd : deriv cayleyInv (E (cayley z)) ≠ 0 := by
    rw [hinv.deriv]
    exact div_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (pow_ne_zero 2 h1E)
  have hcd : 2 * Complex.I / (z + Complex.I) ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (pow_ne_zero 2 hzI)
  have hμ : complexDilatation (douadyEarle h) z =
      complexDilatation (cayleyInv ∘ (E ∘ cayley)) z := by
    have heq : douadyEarle h =ᶠ[nhds z] cayleyInv ∘ (E ∘ cayley) :=
      douadyEarle_eventuallyEq_cayley h hh hc hsurj z hz
    unfold complexDilatation
    rw [wirtZ_eq_of_eventuallyEq heq, wirtZbar_eq_of_eventuallyEq heq]
  rw [hμ, complexDilatation_comp_left cayleyInv (E ∘ cayley) z
      (hEd.comp z (hcay.differentiableAt.restrictScalars ℝ)) hinv.differentiableAt hd,
    complexDilatation_comp_right E cayley z hcay.differentiableAt hEd, norm_mul, hcay.deriv,
    deAux_norm_star_div_self hcd, mul_one]

/-- `e(h)` is real-differentiable at every point of `𝕌`. -/
private theorem deAux_differentiableAt_douadyEarle {h : ℝ → ℝ} (hh : StrictMono h)
    (hc : Continuous h) (hsurj : Function.Surjective h) {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℝ (douadyEarle h) z := by
  have hZ : ‖cayley z‖ < 1 := norm_cayley_lt_one hz
  have hE := extension_mem_disk (cayleyConj h) (bijective_cayleyConj hh hc hsurj)
    (continuous_cayleyConj hh hc hsurj) (cayley z) hZ
  have hzI : z + Complex.I ≠ 0 := by
    rw [← sub_neg_eq_add]
    exact sub_ne_zero.mpr (deAux_ne_neg_I hz)
  have hcay := deAux_hasDerivAt_cayley hzI
  have hinv := deAux_hasDerivAt_cayleyInv (sub_ne_zero.mpr (deAux_ne_one hE).symm)
  have hcomp : DifferentiableAt ℝ (cayleyInv ∘ (extension (cayleyConj h) ∘ cayley)) z :=
    (hinv.differentiableAt.restrictScalars ℝ).comp z
      ((deAux_differentiableAt_extension hh hc hsurj hz).comp z
        (hcay.differentiableAt.restrictScalars ℝ))
  exact hcomp.congr_of_eventuallyEq (douadyEarle_eventuallyEq_cayley h hh hc hsurj z hz)

/-! ## Regularity of the extension on `𝕌`

These make explicit that `complexDilatation (douadyEarle h)` is the genuine
complex dilatation on `𝕌` — `e(h)` is differentiable there with `∂e ≠ 0`, so
neither `fderiv` nor the quotient takes a junk value — and that it is
continuous, hence measurable, as the definition of `M(𝕌)` requires. -/

/-- `e(h)` is orientation preserving on `𝕌`: `|∂̄e(h)| < |∂e(h)|`. -/
theorem norm_wirtZbar_lt_norm_wirtZ_douadyEarle (h : ℝ → ℝ) (hh : StrictMono h)
    (hc : Continuous h) (hsurj : Function.Surjective h) (z : ℂ) (hz : 0 < z.im) :
    ‖wirtZbar (douadyEarle h) z‖ < ‖wirtZ (douadyEarle h) z‖ := by
  have hZ : ‖cayley z‖ < 1 := norm_cayley_lt_one hz
  have hb := bijective_cayleyConj hh hc hsurj
  have hgc := continuous_cayleyConj hh hc hsurj
  set E := extension (cayleyConj h)
  have hE : ‖E (cayley z)‖ < 1 := extension_mem_disk _ hb hgc _ hZ
  have hEd : DifferentiableAt ℝ E (cayley z) := deAux_differentiableAt_extension hh hc hsurj hz
  have hzI : z + Complex.I ≠ 0 := by
    intro h0; have := congrArg Complex.im h0; simp at this; linarith
  have h1E : 1 - E (cayley z) ≠ 0 := sub_ne_zero.mpr (deAux_ne_one hE).symm
  have hcay := deAux_hasDerivAt_cayley hzI
  have hinv := deAux_hasDerivAt_cayleyInv h1E
  have heq : douadyEarle h =ᶠ[nhds z] cayleyInv ∘ (E ∘ cayley) :=
    douadyEarle_eventuallyEq_cayley h hh hc hsurj z hz
  have hEc : DifferentiableAt ℝ (E ∘ cayley) z :=
    hEd.comp z (hcay.differentiableAt.restrictScalars ℝ)
  rw [wirtZ_eq_of_eventuallyEq heq, wirtZbar_eq_of_eventuallyEq heq,
    wirtZ_comp_left _ _ z hEc hinv.differentiableAt,
    wirtZbar_comp_left _ _ z hEc hinv.differentiableAt,
    wirtZ_comp_right _ _ z hcay.differentiableAt hEd,
    wirtZbar_comp_right _ _ z hcay.differentiableAt hEd]
  have hJ := extension_jacobian_pos (cayleyConj h) hb hgc
    (hasIncreasingLift_cayleyConj hh hc hsurj) (cayley z) hZ
  have hWbar : ‖wirtZbar E (cayley z)‖ < ‖wirtZ E (cayley z)‖ := by
    simp only [wirtZbar, wirtZ, norm_div]
    exact div_lt_div_of_pos_right hJ (by norm_num)
  have c1 : 0 < ‖deriv cayleyInv (E (cayley z))‖ := by
    rw [hinv.deriv]; apply norm_pos_iff.mpr
    exact div_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (pow_ne_zero 2 h1E)
  have c2 : 0 < ‖deriv cayley z‖ := by
    rw [hcay.deriv]; apply norm_pos_iff.mpr
    exact div_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero) (pow_ne_zero 2 hzI)
  simp only [norm_mul, norm_star]
  exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_right hWbar c2) c1

/-- `e(h)` is real-differentiable on `𝕌`. -/
theorem differentiableAt_douadyEarle (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (z : ℂ) (hz : 0 < z.im) :
    DifferentiableAt ℝ (douadyEarle h) z :=
  deAux_differentiableAt_douadyEarle hh hc hsurj hz

/-- `∂e(h) ≠ 0` on `𝕌`. -/
theorem wirtZ_douadyEarle_ne_zero (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (z : ℂ) (hz : 0 < z.im) :
    wirtZ (douadyEarle h) z ≠ 0 := by
  intro h0
  have := norm_wirtZbar_lt_norm_wirtZ_douadyEarle h hh hc hsurj z hz
  rw [h0, norm_zero] at this
  exact absurd this (not_lt.mpr (norm_nonneg _))

/-- The complex dilatation of `e(h)` is continuous on `𝕌`. -/
theorem continuousOn_complexDilatation_douadyEarle (h : ℝ → ℝ) (hh : StrictMono h)
    (hc : Continuous h) (hsurj : Function.Surjective h) :
    ContinuousOn (complexDilatation (douadyEarle h)) {z : ℂ | 0 < z.im} := by
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hb := bijective_cayleyConj hh hc hsurj
  have hgc := continuous_cayleyConj hh hc hsurj
  set E := extension (cayleyConj h)
  set G : ℂ → ℂ := fun u => cayleyInv (E (cayley u)) with hG
  have hEan : ContDiffOn ℝ ⊤ E (Metric.ball (0:ℂ) 1) :=
    (extension_analyticOn_disk (cayleyConj h) hb hgc).contDiffOn
      Metric.isOpen_ball.uniqueDiffOn
  have hGcd : ContDiffOn ℝ ⊤ G {z : ℂ | 0 < z.im} := by
    intro z hz
    have hz' : 0 < z.im := hz
    have hZ : ‖cayley z‖ < 1 := norm_cayley_lt_one hz'
    have hzI : z + Complex.I ≠ 0 := by
      intro h0; have := congrArg Complex.im h0; simp at this; linarith
    have hE : ‖E (cayley z)‖ < 1 := extension_mem_disk _ hb hgc _ hZ
    have h1E : 1 - E (cayley z) ≠ 0 := sub_ne_zero.mpr (deAux_ne_one hE).symm
    have hcay : ContDiffAt ℝ ⊤ cayley z := by
      have : ContDiffAt ℂ ⊤ (fun y : ℂ => (y - Complex.I) / (y + Complex.I)) z :=
        (contDiffAt_id.sub contDiffAt_const).div (contDiffAt_id.add contDiffAt_const) hzI
      exact this.restrict_scalars ℝ
    have hinv : ContDiffAt ℝ ⊤ cayleyInv (E (cayley z)) := by
      have : ContDiffAt ℂ ⊤ (fun y : ℂ => Complex.I * (1 + y) / (1 - y)) (E (cayley z)) :=
        (contDiffAt_const.mul (contDiffAt_const.add contDiffAt_id)).div
          (contDiffAt_const.sub contDiffAt_id) h1E
      exact this.restrict_scalars ℝ
    have hEat : ContDiffAt ℝ ⊤ E (cayley z) :=
      hEan.contDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hZ))
    exact (hinv.comp z (hEat.comp z hcay)).contDiffWithinAt
  have hfd : ContinuousOn (fderiv ℝ G) {z : ℂ | 0 < z.im} :=
    hGcd.continuousOn_fderiv_of_isOpen hU (by simp)
  have hfd' : ContinuousOn (fderiv ℝ (douadyEarle h)) {z : ℂ | 0 < z.im} :=
    hfd.congr fun z hz => (douadyEarle_eventuallyEq_cayley h hh hc hsurj z hz).fderiv_eq
  have happ : ∀ v : ℂ, ContinuousOn (fun z => fderiv ℝ (douadyEarle h) z v)
      {z : ℂ | 0 < z.im} := fun v =>
    (ContinuousLinearMap.apply ℝ ℂ v).continuous.comp_continuousOn hfd'
  have hZc : ContinuousOn (wirtZ (douadyEarle h)) {z : ℂ | 0 < z.im} := by
    unfold wirtZ
    exact ((happ 1).sub (continuousOn_const.mul (happ Complex.I))).div_const _
  have hZbc : ContinuousOn (wirtZbar (douadyEarle h)) {z : ℂ | 0 < z.im} := by
    unfold wirtZbar
    exact ((happ 1).add (continuousOn_const.mul (happ Complex.I))).div_const _
  unfold complexDilatation
  exact hZbc.div hZc fun z hz => wirtZ_douadyEarle_ne_zero h hh hc hsurj z hz

/-! ## Averages over the circle -/

/-- Average over the circle: `(2π)⁻¹ ∫₀^{2π} F(e^{iφ}) dφ`.
(`Circle` and `Circle.exp` are taken from mathlib.) -/
def circleAvg (F : Circle → ℂ) : ℂ :=
  (2 * Real.pi)⁻¹ * ∫ φ in (0:ℝ)..(2 * Real.pi), F (Circle.exp φ)

/-! ## Section 3.1: conformal naturality and scale invariance -/

/-- **Lemma (Conformal Naturality)**, for the real affine automorphisms of
`𝕌`, which are the only Möbius maps the paper applies it to:
`e(A ∘ h ∘ B) = A ∘ e(h) ∘ B` for `A(w) = a w + b`, `B(z) = c z + d` with
`a, c > 0` and `b, d` real.

(Only affine maps can be used with `h : ℝ → ℝ`: a real Möbius map with a pole
on `ℝ` does not map `ℝ` to `ℝ`.) -/
theorem conformal_naturality (h : ℝ → ℝ) (hh : StrictMono h) (hc : Continuous h)
    (hsurj : Function.Surjective h) (a b c d : ℝ) (ha : 0 < a) (hc' : 0 < c)
    (z : ℂ) (hz : 0 < z.im) :
    douadyEarle (fun t => a * h (c * t + d) + b) z =
      (a : ℂ) * douadyEarle h ((c : ℂ) * z + d) + b := by
  set h' : ℝ → ℝ := fun t => a * h (c * t + d) + b with hh'def
  have hmono : StrictMono h' := by
    intro s t hst
    have h1 : h (c * s + d) < h (c * t + d) := hh (by nlinarith)
    show a * h (c * s + d) + b < a * h (c * t + d) + b
    nlinarith
  have hcont : Continuous h' :=
    (continuous_const.mul (hc.comp ((continuous_const.mul continuous_id).add
      continuous_const))).add continuous_const
  have hsurj' : Function.Surjective h' := by
    intro y
    obtain ⟨s, hs⟩ := hsurj ((y - b) / a)
    refine ⟨(s - d) / c, ?_⟩
    show a * h (c * ((s - d) / c) + d) + b = y
    rw [show c * ((s - d) / c) + d = s by field_simp; ring, hs]
    field_simp
    ring
  set Z : ℂ := (c : ℂ) * z + d with hZdef
  have hZre : Z.re = c * z.re + d := by simp [hZdef]
  have hZim : Z.im = c * z.im := by simp [hZdef]
  have hZ : 0 < Z.im := by rw [hZim]; exact mul_pos hc' hz
  obtain ⟨hwim, hweq⟩ := douadyEarle_spec h hh hc hsurj Z hZ
  set w := douadyEarle h Z
  have hw'im : 0 < ((a : ℂ) * w + b).im := by
    have e : ((a : ℂ) * w + b).im = a * w.im := by simp
    rw [e]; exact mul_pos ha hwim
  refine (barycenter_existsUnique h' hmono hcont hsurj' z hz).unique
    (douadyEarle_spec h' hmono hcont hsurj' z hz) ⟨hw'im, ?_⟩
  -- The substitution `s = c t + d`.
  set K : ℝ → ℂ := fun s => (((h s : ℂ) - w) / ((h s : ℂ) - star w)) *
    (poissonKernelUHP Z s : ℂ) with hK
  have hPreal : ∀ t : ℝ, poissonKernelUHP z t = c * poissonKernelUHP Z (c * t + d) := by
    intro t
    simp only [poissonKernelUHP, hZre, hZim]
    have hq : 0 < (t - z.re) ^ 2 + z.im ^ 2 :=
      add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hz 2)
    rw [show (c * t + d - (c * z.re + d)) ^ 2 + (c * z.im) ^ 2 =
      c ^ 2 * ((t - z.re) ^ 2 + z.im ^ 2) by ring]
    have hq' := hq.ne'
    have hc0 := hc'.ne'
    have hpi := Real.pi_ne_zero
    field_simp
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hpt : ∀ t : ℝ, (((h' t : ℂ) - ((a : ℂ) * w + b)) /
      ((h' t : ℂ) - star ((a : ℂ) * w + b))) * (poissonKernelUHP z t : ℂ) =
      (c : ℂ) * K (c * t + d) := by
    intro t
    have hne := deAux_ofReal_sub_star_ne_zero (h (c * t + d)) hwim
    have hstar : star ((a : ℂ) * w + b) = a * star w + b := by
      simp [star_add, star_mul', Complex.conj_ofReal]
    have e1 : ((h' t : ℝ) : ℂ) - ((a : ℂ) * w + b) = a * ((h (c * t + d) : ℂ) - w) := by
      simp only [hh'def]; push_cast; ring
    have e2 : ((h' t : ℝ) : ℂ) - star ((a : ℂ) * w + b) =
        a * ((h (c * t + d) : ℂ) - star w) := by
      rw [hstar]; simp only [hh'def]; push_cast; ring
    rw [e1, e2, mul_div_mul_left _ _ ha0, hPreal t]
    simp only [hK]
    push_cast
    ring
  have hint : ∫ t : ℝ, (((h' t : ℂ) - ((a : ℂ) * w + b)) /
      ((h' t : ℂ) - star ((a : ℂ) * w + b))) * (poissonKernelUHP z t : ℂ) =
      (c : ℂ) * ∫ t : ℝ, K (c * t + d) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have h1 : ∫ t : ℝ, K (c * t + d) = |c⁻¹| • ∫ s : ℝ, K (s + d) :=
    Measure.integral_comp_mul_left (fun s => K (s + d)) c
  have h2 : ∫ s : ℝ, K (s + d) = ∫ s : ℝ, K s := integral_add_right_eq_self K d
  have h3 : ∫ s : ℝ, K s = 0 := hweq
  show ∫ t : ℝ, (((h' t : ℂ) - ((a : ℂ) * w + b)) /
      ((h' t : ℂ) - star ((a : ℂ) * w + b))) * (poissonKernelUHP z t : ℂ) = 0
  rw [hint, h1, h2, h3, smul_zero, mul_zero]

/-- Conformal naturality preserves the modulus of the complex dilatation:
`|μ_{e(A ∘ h ∘ B)}(z)| = |μ_{e(h)}(B z)|`. -/
theorem norm_complexDilatation_conformal_naturality (h : ℝ → ℝ) (hh : StrictMono h)
    (hc : Continuous h) (hsurj : Function.Surjective h) (a b c d : ℝ) (ha : 0 < a)
    (hc' : 0 < c) (z : ℂ) (hz : 0 < z.im) :
    ‖complexDilatation (douadyEarle (fun t => a * h (c * t + d) + b)) z‖ =
      ‖complexDilatation (douadyEarle h) ((c : ℂ) * z + d)‖ := by
  set A : ℂ → ℂ := fun u => (a : ℂ) * u + b
  set B : ℂ → ℂ := fun u => (c : ℂ) * u + d with hB
  show ‖complexDilatation (douadyEarle (fun t => a * h (c * t + d) + b)) z‖ =
    ‖complexDilatation (douadyEarle h) (B z)‖
  have heq : douadyEarle (fun t => a * h (c * t + d) + b) =ᶠ[nhds z]
      A ∘ (douadyEarle h ∘ B) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz] with u hu
    exact conformal_naturality h hh hc hsurj a b c d ha hc' u hu
  have hμ : complexDilatation (douadyEarle (fun t => a * h (c * t + d) + b)) z =
      complexDilatation (A ∘ (douadyEarle h ∘ B)) z := by
    unfold complexDilatation
    rw [wirtZ_eq_of_eventuallyEq heq, wirtZbar_eq_of_eventuallyEq heq]
  have hZ : 0 < (B z).im := by
    have e : (B z).im = c * z.im := by simp [hB]
    rw [e]; exact mul_pos hc' hz
  have hBd : HasDerivAt B (c : ℂ) z :=
    (((hasDerivAt_id' z).const_mul (c : ℂ)).add_const (d : ℂ)).congr_deriv (mul_one _)
  have hAd : ∀ v : ℂ, HasDerivAt A (a : ℂ) v := fun v =>
    (((hasDerivAt_id' v).const_mul (a : ℂ)).add_const (b : ℂ)).congr_deriv (mul_one _)
  have hed : DifferentiableAt ℝ (douadyEarle h) (B z) :=
    deAux_differentiableAt_douadyEarle hh hc hsurj hZ
  have hd : deriv A ((douadyEarle h ∘ B) z) ≠ 0 := by
    rw [(hAd _).deriv]
    exact_mod_cast ha.ne'
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc'.ne'
  rw [hμ, complexDilatation_comp_left A (douadyEarle h ∘ B) z
      (hed.comp z (hBd.differentiableAt.restrictScalars ℝ)) (hAd _).differentiableAt hd,
    complexDilatation_comp_right (douadyEarle h) B z hBd.differentiableAt hed, norm_mul,
    hBd.deriv, deAux_norm_star_div_self hc0, mul_one]

/-- The normalized map `h_z(t) = (f(x + yt) - f(x)) / (f(x+y) - f(x))`
at `z = x + iy`. -/
def normalizedMap (f : ℝ → ℝ) (x y : ℝ) : ℝ → ℝ :=
  fun t => (f (x + y * t) - f x) / (f (x + y) - f x)

end VanishingCarleson

end
