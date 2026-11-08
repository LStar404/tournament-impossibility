# 竞赛图哈密顿路极值序列的不可能性结果

这里是《哈密顿路极值序列的非代数性与公式限制》这一部分的独立仓库：论文与配套 Lean 4 形式化。
原先它作为子目录放在研究笔记仓库里，现在单独成库，便于单独引用与审阅。

## 内容

- `paper/` —— 论文的中文与英文两个版本：
  - 中文：`nonalgebra_zh.md`、`nonalgebra_zh.tex`、`nonalgebra_zh.pdf`
  - 英文：`nonalgebra_en.tex`、`nonalgebra_en.pdf`
  两份 PDF 都由 `.github/workflows/paper-rebuild.yml` 从对应 `.tex` 用 tectonic 编译（推改源文件或手动触发）。
  正文与数学统一使用 STIX Two，带标题块、页眉与页码。
- `lean/` —— 论文附录 A 的形式化。三个生成函数 A、E、M 都被证明没有非零的复系数多项式关系，
  结论用 Mathlib 的标准谓词 `Transcendental (Polynomial ℂ)` 表述。14 个模块，
  `lean/verification/result.json` 记录逐模块结果、源文件 SHA-256 与公理依赖。
- `historical/formula-restrictions/` —— 同一主题的早期版本（中英文稿与 PDF），保留作历史对照，
  不代表当前结论，也未随本次署名与排版变更重编。

## 边界

两项外部前提写在定理类型里，没有声明成公理，也没有在本仓库中重新证明：

1. 归一化极值序列趋于 `cosh(1)/cos(1)`，来自论文引用的图论渐近定理。
2. `exp(1), exp(-1), exp(i), exp(-i)` 在代数数系数下线性无关，即 Lindemann–Weierstrass 的有限特例。

条件 R、单位圆是自然边界、非 D-finite、非 P-recursive、伸缩关系与数字模型限制等结论未形式化。
生成函数非代数不等于没有闭式，也不等于计算困难。

## 复现

```text
cd lean
python verify.py
```

Lean 4.35.0，mathlib 版本固定在 `lean/lakefile.toml`；环境变量 `LEAN_BIN` 与 `MATHLIB_PACKAGES`
可指向已有安装，未设置时回退到 `PATH` 上的 `lean` 与本地 `.lake/packages`。
详细说明见 `lean/README.md`。
