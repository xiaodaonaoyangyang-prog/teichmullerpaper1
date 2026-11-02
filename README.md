# Vanishing Carleson Measures — Lean 4 形式化

论文 *Vanishing Carleson Measures for the Douady–Earle Extension of Strongly
Symmetric Homeomorphisms of the Real Line*（`D:/lean/theorem3_reorganized.tex`）
的完整形式化。

## 状态（2026-09-27）

**主定理已证毕**：

```
theorem VanishingCarleson.main_theorem (f : ℝ → ℝ) (hf : StronglySymmetric f) :
    IsVanishingCarleson
        (fun x y => ‖complexDilatation (douadyEarle f) (x + y * Complex.I)‖) ∧
      (∃ k : ℝ, k < 1 ∧ ∀ z : ℂ, 0 < z.im →
        ‖complexDilatation (douadyEarle f) z‖ ≤ k) ∧
      ContinuousOn (complexDilatation (douadyEarle f)) {z : ℂ | 0 < z.im}

'VanishingCarleson.main_theorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

即对每个 `f ∈ SS(ℝ)`，`μ_{e(f)} ∈ ℳ₀(𝕌) = M(𝕌) ∩ 𝓛₀(𝕌)`：
`|μ|² dxdy/y` 是消失 Carleson 测度，`‖μ‖_∞ ≤ k < 1`（逐点一致界），且 `μ`
在 `𝕌` 上连续（从而可测）。`VanishingCarleson` 命名空间中全部公开声明都只
依赖 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorry`。

依赖库 `DouadyEarleExt`（`D:/lean/Conformally_natural_extension_of_homeomorphisms_of_the_circle`）
自身仍有 5 处 `sorry`（Proposition 3 与 `HigherDim.lean`），均不在主定理的
依赖闭包内。

## 构建

* 工具链 `leanprover/lean4:v4.36.0-rc2`；mathlib 为共享检出（tag `v4.36.0-rc2`，commit `9d581dff`）
  `D:/lean/mathlib4-v436rc2`（与 `DouadyEarleExt`、Li Zhong 项目共用同一份构建）。
* 路径依赖 `douady_earle`（Douady–Earle 圆盘扩张），它又路径依赖
  `D:/lean/lizhong_quasiconformal_teichmuller`。
* `lake build`。完整构建约 6 分钟（mathlib 与依赖已构建时）。
* 切换工具链后须在 VS Code 中执行 "Lean 4: Restart Server"：仍在旧工具链上
  运行的 Lean 服务器会改写 `.lake/config` 与共享的构建产物。
* 升级前的旧版本（v4.31、`mathlib4-master`）存档于
  `D:/lean/vanishing_carleson_archive/pre_upgrade_2026-09-27`。

## 文件结构

所有声明位于 `namespace VanishingCarleson`（避免与 `DouadyEarleExt` 的根命名空间
同名声明冲突）。导入顺序即下表顺序。

| 文件 | 论文 | 内容 |
|---|---|---|
| `Basic.lean` | §2.1–2.2 | 区间平均、BMO/VMO 与局部模、`A_∞`（(A1)，正性只要求 a.e.）、(A1) ⇒ (A2)、Carleson 盒与 (消失) Carleson 测度、Poisson 核 |
| `Cayley.lean` | §2.3 | Cayley 变换、`cayleyConj h = γ ∘ h ∘ γ⁻¹`（连续、双射、保向）、调和测度在 `γ` 下的转移、`λ(w)` 恒等式、Cayley 差商恒等式 |
| `DouadyEarle.lean` | §2.3, §3.1 | 拟对称、`SS(ℝ)`、上半平面重心方程与 `e(h)`；重心存在唯一（由圆盘情形经 Cayley 变换推出）、`e(h) = γ⁻¹ ∘ E(g_h) ∘ γ`、仿射共形自然性、`e(h)` 的可微性与 `μ` 的连续性 |
| `Compactness.lean` | §3.2 | `𝒦_ρ` 的紧性（Cayley 共轭在 `C(S¹, S¹)` 中紧）、原点处连续性、紧泛函推论 |
| `Localization.lean` | §3.3 | 局部化、实部局部化、拟共形界 `‖μ_{e(h)}‖_∞ ≤ k(ρ) < 1` |
| `ForwardDisc.lean` | §4（圆盘部分） | `(1-|q|²)E_Z(0) = D`、`μ_{E(g)}(0) = N/D`、`|N| ≤ 5⨍|g-m|` |
| `ForwardInequality.lean` | §4 | 前向不等式 |
| `BetaTheta.lean` | §5 | β 数、`Θ_h`、`L²` 投影、分母下界、`|μ| ≤ C Θ_h` |
| `TentEntropy.lean` | §§6–7 | 帐篷展开、熵不等式、John–Nirenberg、`E_h` 的两个界 |
| `ProofSteps.lean` | §§2–9 辅助、§8 | 比较定理、主不等式、(C) `isCarlesonFn_betaPt`、(V) `isVanishingCarleson_betaPt`、`SS ⇒ QS`（`ρ = 4A₀²`）、BMO 尺度不变性 |
| `MainTheorem.lean` | §9 | `Θ_h` Carleson 估计、主定理 |

`DouadyEarleExt/ImplicitZero.lean`（在依赖库中）证明圆盘重心方程在原点的
隐函数微分 `hasImplicitDerivAtZero`，是 `μ_{E(g)}(0) = N/D` 的输入。

## 论文 ↔ Lean 对照表

| 论文 | Lean 声明 | 文件 |
|---|---|---|
| Thm. 1 (`thm:main`) | `main_theorem` | MainTheorem |
| (A1) ⇒ (A2) | `a1_imp_a2` | Basic |
| `SS(ℝ)` ⇒ `ρ`-拟对称 | `ainfty_imp_quasisymmetric`, `ss_imp_quasisymmetric` | ProofSteps, MainTheorem |
| 重心存在唯一、`e(h) = γ⁻¹∘e(g)∘γ` (§2.3) | `barycenter_existsUnique`, `barycenterEq_iff_baryEq`, `douadyEarle_eq_cayley` | DouadyEarle |
| Lem. Conformal Naturality (`lem:conf-nat`) | `conformal_naturality`, `norm_complexDilatation_conformal_naturality` | DouadyEarle |
| Lem. Scale Invariance of BMO (`lem:bmo-scale`) | `bmo_norm_scale_invariance` | ProofSteps |
| Lem. Compactness (`lem:compactness`) | `compact_KFamily` | Compactness |
| Lem. Continuity at origin (`lem:de-cont`) | `de_continuous_at_origin` | Compactness |
| Cor. Compact functionals | `compact_functionals` | Compactness |
| Lem. DE Localization (`lem:de-loc`) | `de_localization` | Localization |
| Cor. Real-part localization (`cor:real-loc`) | `real_part_localization` | Localization |
| 拟共形界 `‖μ‖_∞ ≤ k(ρ) < 1` | `de_quasiconformal` | Localization |
| Thm. Forward Inequality (`thm:forward`) | `forward_inequality`（圆盘部分：`disc_wirt_formula`, `disc_numerator_le`） | ForwardInequality, ForwardDisc |
| Lem. `lem:affine-norm`, `lem:beta-basic` | `beta_attained`, `continuous_betaPt`, `continuous_eps` | BetaTheta, TentEntropy |
| Lem. `lem:denom` | `denominator_lower_bounds` | BetaTheta |
| Lem. `lem:affine-growth`, `lem:L2-L1-comparison`, `lem:delta-beta-new` | `affine_growth`, `l2_l1_comparison`, `telescoping_decomposition` | BetaTheta |
| Prop. `prop:forward-to-theta` | `forward_to_theta` | BetaTheta |
| Lem. `lem:tent`, `lem:tent2` | `tent_expansion`, `tent_squared` | TentEntropy |
| Lem. `lem:entropy`, Cor. `cor:eps-carleson` | `entropy_inequality`, `eps_carleson_bound`, `eps_carleson_lintegral` | TentEntropy |
| Lem. `lem:E-bounds` | `entropy_bound_ainfty`, `entropy_bound_bmo` | TentEntropy |
| Thm. Comparison (`thm:compare`) | `compare_beta_eps` | ProofSteps |
| Thm. `thm:beta-carleson` | `beta_carleson_master`, `beta_carleson_uniform`, `beta_carleson_vanishing` | ProofSteps, MainTheorem |
| Thm. `thm:theta-new` | `theta_carleson` | MainTheorem |

## 与论文的偏离（已同步写回 tex）

1. **共形自然性**只对 `𝕌` 的实仿射自同构陈述与使用（论文也只用到仿射情形）。
2. **前向不等式 Step 2**（分母下界）：不用族 `A_ρ` 与 [Sh, Prop 4.1(3)] 的
   双曲双 Lipschitz 性质，而是对紧族 `𝒦_ρ` 上的连续正泛函
   `(1 - |⟨g²⟩|²)|∂_Z e(g)(0)|` 取最小值。
3. **`‖μ_{e(h)}‖_∞ ≤ k(ρ) < 1`** 同样由紧性证明（`μ_{e(g)}(0)` 关于 `g` 连续且
   逐点 `< 1`），不引用 [DE] 的拟共形常数。
4. **`𝒦_ρ` 的紧性**表述为 Cayley 共轭在 `C(S¹, S¹)` 中紧，等价于 `ℝ̄` 上球面度量
   的一致收敛紧性。
5. **`A_∞`** 以 (A1) 定义（正性 a.e.），(A1) ⇒ (A2) 与 `log w ∈ L¹_loc` 在本项目
   中证明；`SS ⇒ QS` 以显式常数 `ρ = 4A₀²` 证明。
6. 论文中的若干小漏洞已补：`ρ`-拟对称未定义、紧性 Step 3/Step 5、`lem:denom`
   中 `C₀(ρ)` 可为 `0`、`lem:E-bounds(b)` 中 `η = 0`、`prop:forward-to-theta`
   隐用 `v ≤ C L`、`lem:bmo-scale` 缺假设。

## 形式化约定

1. **复伸缩商** `complexDilatation`（来自 `DouadyEarleExt`）经 `fderiv ℝ` 定义；
   `e(h)` 在 `𝕌` 上可微且 `∂e(h) ≠ 0`（`differentiableAt_douadyEarle`,
   `wirtZ_douadyEarle_ne_zero`），故主定理中的 `μ` 是真正的伸缩商。
2. **Carleson 测度** `IsCarlesonFn` / `IsVanishingCarleson` 用 `ℝ≥0∞` 值盒积分
   `carlesonBoxLIntegral` 陈述：发散积分取 `∞`，不会被垃圾值 `0` 冒充。
3. `BMO` / `VMO` / `WeightA1` 作为独立定义不含 `L¹_loc` 假设（Bochner 积分对
   不可积函数取 `0`），故单独看比论文弱；但在 `StronglySymmetric` 中，单调性
   保证 `deriv f` 局部可积，(A1) 保证 `log deriv f` 局部可积，两者与论文一致
   ——而且假设变弱只会使主定理更强。
4. `≍_ρ` 一律展开为"存在仅依赖于 `ρ` 的常数"的量词形式，常数在映射之前量化
   （`∃ C, ∀ h, …`）。
