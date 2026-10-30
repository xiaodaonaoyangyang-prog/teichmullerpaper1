/-
# Vanishing Carleson Measures for the Douady–Earle Extension of Strongly
Symmetric Homeomorphisms of the Real Line

Root module of the formalization of `theorem3_reorganized.tex`.  The main
theorem `VanishingCarleson.main_theorem` (every `f ∈ SS(ℝ)` has
`μ_{e(f)} ∈ ℳ₀(𝕌)`) is proved, and so is every declaration of the library:
nothing depends on `sorryAx` or on axioms beyond `propext`,
`Classical.choice` and `Quot.sound`.  The Douady–Earle extension of the disk
and its properties come from the library `DouadyEarleExt`.

Module layout, following the paper's sections:

* `VanishingCarleson.Basic`             — §2: interval averages, BMO/VMO,
  `A_∞`-weights and `(A1) ⇒ (A2)`, Carleson measures, the Poisson kernel
* `VanishingCarleson.Cayley`            — the Cayley transform, the Cayley
  conjugate `γ ∘ h ∘ γ⁻¹`, transfer of harmonic measure
* `VanishingCarleson.DouadyEarle`       — §2.3 and §3.1: the extension on `𝕌`,
  existence and uniqueness of the barycenter, `e(h) = γ⁻¹ ∘ E(g) ∘ γ`,
  conformal naturality, regularity of `e(h)`
* `VanishingCarleson.Compactness`       — §3.2: compactness of `𝒦_ρ`,
  continuity at the origin, compact functionals
* `VanishingCarleson.Localization`      — §3.3: localization, real-part
  localization, the quasiconformality bound `‖μ_{e(h)}‖_∞ ≤ k(ρ) < 1`
* `VanishingCarleson.ForwardDisc`       — §4 on the disk: `μ_{E(g)}(0) = N/D`
  and `|N| ≤ 5 ⨍|g - m|`
* `VanishingCarleson.ForwardInequality` — §4: the forward inequality
* `VanishingCarleson.BetaTheta`         — §5: beta-numbers, `Θ_h`, the
  pointwise bound `|μ| ≤ C Θ_h`
* `VanishingCarleson.TentEntropy`       — §§6–7: tent expansion, entropy
  inequality, John–Nirenberg
* `VanishingCarleson.ProofSteps`        — §8 and auxiliary results: the
  comparison theorem, the beta-number Carleson estimates (C), (V), `SS ⇒ QS`
* `VanishingCarleson.MainTheorem`       — §9: the `Θ_h` Carleson estimate and
  the main theorem
-/
import VanishingCarleson.Basic
import VanishingCarleson.Cayley
import VanishingCarleson.DouadyEarle
import VanishingCarleson.Compactness
import VanishingCarleson.Localization
import VanishingCarleson.ForwardDisc
import VanishingCarleson.ForwardInequality
import VanishingCarleson.BetaTheta
import VanishingCarleson.TentEntropy
import VanishingCarleson.ProofSteps
import VanishingCarleson.MainTheorem
