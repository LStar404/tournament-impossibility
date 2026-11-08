# 竞赛图极值生成函数的非代数性

> 状态：2026-11-08。14 个模块整体验证通过，A、E、M 三个生成函数的形式化都已完成。
> 验证记录见 `verification/result.json`；范围边界（两项外部前提）见下文。

证明来源：刘星辰，`tournament-paths-research-notes` 的
[非代数性论文附录 A](https://github.com/LStar404/tournament-paths-research-notes/blob/b8cc8eb251c0c85ba9d177ec9e9ba612c11ca582/docs/nonalgebra_zh.md)。
本目录是独立的 Lean 4 工程，不修改原论文或同步参考文件。

## 准确范围

主对象是 `A(z) = ∑_{n≥1} 2^(n−1) P(n) / n! · z^n`。
`TournamentSequence.lean` 将 P(n) 定义为全体 n 阶竞赛图上、满足相邻有向边条件的顶点排列数的最大值。
它还证明有限编码覆盖所有竞赛图；计数不除以二。

`Main.lean` 中的主结论是 `extremal_generating_function_transcendental`，
使用 Mathlib 的标准谓词 `Transcendental (Polynomial ℂ)`。
其前置定理 `extremal_generating_function_nonalgebraic` 排除一个非零有限二维系数数组给出的多项式关系，
允许任意复数系数。因此所排除的是非零的复系数二元多项式方程，而不只是有理函数公式。
通常将这称为在 ℂ(z) 上超越：多项式关系与有理函数关系可通过清分母互相转换。
本工程采用 ℂ[X] 上的标准表述，没有另建 ℂ(z) 到 Laurent 级数域的嵌入。

三个生成函数的主结论都保留同样两个**显式外部前提**：

- `ExtremalAsymptotic`：归一化极值序列趋于 `cosh(1)/cos(1)`，对应原论文引用的图论渐近定理。
- `FourExponentialIndependence`：`exp(1), exp(-1), exp(i), exp(-i)` 在代数数系数下线性无关，
  对应 Lindemann–Weierstrass 定理的有限特例。

这里没有把这两个前提声明成公理，也没有在本工程中重新证明它们。
所以本工程是**以两项外部定理为前提的形式化证明**，不是从 Lean 基础公理直接推出全部图论和超越数论结果的无前提工程。
条件 R 不参与这里的证明；本工程不声称证明自然边界、非 D-finite 或一般闭式不存在。

## 模块

| 文件 | 内容 |
|---|---|
| `TournamentSequence.lean` | 竞赛图、哈密顿路计数、最大值和有理归一化系数 |
| `Constant.lean` | 从明确的有限线性无关性输入推出极限常数超越 |
| `Abel.lean` | 系数数列收敛推出 `(1-r)∑a_n r^n` 的 Abel 极限 |
| `Descent.lean` | 有理系数形式幂级数的复系数关系降到有理系数 |
| `Evaluation.lean` | 绝对收敛下的 Cauchy 乘积及形式关系求值 |
| `StandardAlgebraicity.lean` | 从 Mathlib 标准代数性谓词转成有限系数关系 |
| `Radial.lean` | 去掉公共端点因子，再对多项式关系取极限 |
| `Normalization.lean` | 多项式归一化 `(1-z)^d` 保留代数性 |
| `Application.lean` | 极值序列的 Abel 极限及超越边界值 |
| `Main.lean` | 一般非代数性判据及实际极值序列应用 |
| `WeightedAbel.lean` | 非零常数缩放及变量缩放下的关系转移，处理 E |
| `Corollaries.lean` | E 的实际系数 P(n)/n!、精确缩放恒等式及其非代数性 |
| `QuadraticAbel.lean` | 二次权 Abel 极限：`(1-r)^3 ∑ n^2 c_n r^n → 2L`，不假设单调性或收敛速度 |
| `Remainder.lean` | 余项 M：系数 `m_n = n^2 a_n − 2·1_{2∣n}·a_{n/2}`、`m_n/n^2 → L`、三阶径向极限与非代数性 |

三个生成函数 A、E、M 的非代数性都在本工程中给出形式化证明。
`WeightedAbel.lean` 的文件名来自开发阶段；其交付范围以文件内实际定理为准。

## 复现

标准环境使用 Lean 4.35.0，mathlib 固定到 `lakefile.toml` 中的 commit：

```text
lake update
lake exe cache get
lake build
```

本机验证为避免下载，复用已安装的同版本 Lean 和只读 mathlib 编译缓存：

```text
python verify.py
```

`check.py` 通过环境变量 `LEAN_BIN` 与 `MATHLIB_PACKAGES` 定位 Lean 与 mathlib；
未设置时回退到 `PATH` 上的 `lean` 与本地 `.lake/packages`。它只在本目录写入新模块与日志。

`verification/result.json` 记录实际执行结果、源文件 SHA-256 和公理依赖报告。
判定通过必须编译成功，且报告中不得出现 `sorryAx`。
常规 Lean 公理 `propext`、`Classical.choice`、`Quot.sound` 不属于未完成证明占位符。
外部前提在定理类型中，不能仅看公理列表而忽略它们。

## 视频状态

用户已取消视频制作。此工程及交付包不包含视频成果。
