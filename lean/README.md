# 竞赛图极值生成函数的非代数性

> 状态：2026-11-08 23:11 UTC。构建记录覆盖的 120 个模块全部验证通过，A、E、M 三个生成函数的形式化都已完成。
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

验证脚本按本地依赖顺序逐模块编译并记录源码哈希、公理审计及退出码：

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

## 数字表示扩展（2026-11-08）

- `QRegular.lean` 使用标准 q-kernel 在复数域上张成有限维空间的定义，而非把待证结论放进定义。
  它证明 q^e 子序列具有有限矩阵幂表示。
- `MatrixPowerSeries.lean` 通过 det(I−XM) 和伴随矩阵证明矩阵幂输出的生成函数满足非零多项式关系。
- `QRegularApplications.lean` 证明有理序列 a_n/n^k 若趋于超越数则非 q-regular，
  并连接真实 `normalizedCoefficient` 和 `halfScaleRemainder`。只对 q^e 子序列缩放矩阵；
  不假设除以 n^k 保持 q-regular。这两个实际结论保留渐近与有限指数线性无关性两项显式输入。
- `PathCountGrowth.lean` 证明真实 P(n) 无统一指数上界，再排除固定数字连续线性递归与连续线性输出；
  此结论只需 `ExtremalAsymptotic`，不需超越性输入。

论文 A.5 的完整强结论现已形式化，见下节。P 的数字模型定理与 q-kernel 定义之间的一般等价关系未形式化。
R、自然边界、非 D-finite 等仍不在 Lean 覆盖内。不得把这些边界改写成上游数学断言不成立。


## A.5 完整有理极限（续做）

`QRegularRationalLimit.lean` 中的 `NonAlgebraicity.qRegular_scaled_limit_rational` 对所有整数 q≥2、自然数 k、有理值序列 a，
从标准 q-kernel 的复数线性张成有限维以及 a_n/n^k→L，推出存在 r∈ℚ 使 r=L。
本定理没有图论渐近、Lindemann–Weierstrass 或极限超越性的额外假设。

- `MatrixPowerSeries.matrix_output_series_linear_relation` 从伴随矩阵抽出显式线性关系 Q·B=P，Q≠0。
- `RationalLinearDescent` 用 ℚ-线性对偶逐系数降域，保留非零分母，未把线性关系弱化为一般代数关系。
- `RationalRadial` 同时消去分子分母在端点的公共根，按分母次数严格递降，证明有限极限为有理数。
- `RationalSeriesLimit` 形式化多项式关系的绝对收敛求值并结合 Abel 极限。
- `QRegularRationalLimit` 连接标准 q-kernel、几何子序列与矩阵缩放，完成任意 k 的强版 A.5。

此前较弱的超越极限排除端点保留，作为 A.6 的直接应用链；更强结论并非由排除超越数偷换而来。

## 上游引理的新增覆盖与边界

另有一组已验证的上游引理：有限有序消去、颜色词的最短交换与零菱形竞赛图修复、实际竞赛图矩阵的向量弱主序、所有非负整数次幂的Frobenius范数比较，以及全一向量源能量级数的收敛与比较。级数结果的范围是 $q\ge0$ 且 $q(n-1)^2<1$，包括 $n>0$ 时的 $q=1/n^2$，不以可求和性作为额外假设。进一步，已证明实际矩阵的预解式恒等式 $(B\mathbf{1})^{\mathsf T}(I+qB^2)^{-1}(B\mathbf{1})=\sum_{r\ge0}q^r\lVert B^{r+1}\mathbf{1}\rVert^2$ 及其与传递竞赛图的比较；参数限于上述实数范围，双边逆与级数收敛均在证明中建立。此外，真实有序反对称块矩阵的六阶矩多项式、三角循环计数与源能量缺陷之间的恒等式，以及相对于全局传递竞赛图的六阶缺陷公式均已形式化。实际哈密顿路计数的精确偶子集卷积公式S1及零菱形情形的两永久式平均现已证明，均直接使用本仓库的计数定义，不假设卷积或主子式恒等式。实际SCC的有序块重构也已证明，从而消除了六阶小块推论的额外结构与计数前提：若实际竞赛图的顶点数为 $n\ge4$，无标号四顶点菱形数为 $D>0$，且 $24D\le n^2$，则 $6n^2D\le\lVert T_n^3\rVert_F^2-\lVert S^3\rVert_F^2$，其中 $S$ 是原图的反对称符号矩阵，$T_n$ 是传递竞赛图的符号矩阵。这个有限小缺陷定理不涉及大缺陷范围，也不完成条件R。扩大的复谱域及导数比较、实际渐近恢复链与条件R仍未形式化。

关键端点见 `ZeroDiamondRepair`、`VectorMajorizationEndpoint`、`ReferenceMomentEndpoint` 、`OnesEnergyEndpoint` 、`SourceResolventEndpoint`、`OrdinalGlobalSixthDeficit` 、`ActualPathConvolution`、`DiamondFreePathAverage` 和 `ActualSmallDiamondSixth`。源代码、公理报告及 SHA-256 对应关系见 `verification/result.json`；模块数量记录一次构建快照，不代表条件 R 已完成。

### 零 diamond 有限核行列式补证（2026-11-08）

`DiamondFreeKernelDeterminant` 已验证实际零 diamond 竞赛图在任意特征零域中的完整有限恒等式
`det(I + z S) = ((1 + z)^n + (1 - z)^n) / 2`，以及归一化负号版本。
它不预设主子式或谱公式；证明使用实际符号切换与传递竞赛图重编号。
117 模块 `verify.py` 和聚合 `lake build` 均实际通过，端点仅使用标准逻辑公理。
实参数 `z/n` 对应双曲余弦，代入虚参数才对应余弦。该有限结果不等于复圆盘一致渐近、源项导数控制或完整 R。
论文 PDF 仍是上一轮 116 模块叙述快照；本轮新增形式化的精确范围以此处和该模块 scope 为准。

### 复核一致极限与实际二次核（2026-11-08 23:11 UTC）

新增三个模块已通过全量120模块验证和聚合lake构建（9167 jobs）。
实际零diamond竞赛图族的归一化虚参数行列式在任意复紧集上一致收敛于cos；避开cos零点的紧集上标量倒数一致收敛于sec。
二次矩阵核 `I+(w/n)^2 S^2` 的精确因式分解、沿收敛参数序列的行列式极限cos²，以及极限cos非零处最终真正双侧可逆，均已形式化。
这些结论是定性收敛，不包括O(1/n)速率、增长维度的矩阵逆算子范数、源项、导数控制或完整R。PDF仍是116模块快照。
