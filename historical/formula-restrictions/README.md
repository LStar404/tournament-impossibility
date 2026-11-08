# 竞赛图中哈密顿路最大数的公式限制

Restrictions on formulas for tournament Hamiltonian path maxima

刘星辰 / Xingchen Liu；叶祥宇 / Xiangyu Ye。个人研究者 / Independent Researchers。

2026-11-02，研究稿 v0.1。联系邮箱：lxc-em5158@outlook.com。

## 从哪里读起

建议先读 `manuscript_zh.md` 或 `impossibility_zh.pdf` 的正文四节。正文解释问题、结论及其含义；附录A–E保存准确的假设和完整证明。英文版采用相同结构。

这是一篇单独的新研究稿，没有替换此前的常数界论文，也没有自动上传到 GitHub 或 Zenodo。

## 文件

- `manuscript_zh.md`、`manuscript_en.md`：中英文可编辑正文，是本包的内容源。
- `impossibility_zh.pdf`、`impossibility_en.pdf`：适合阅读的排版版本。
- `manuscript_zh.tex`、`manuscript_en.tex`：可编辑的 XeLaTeX 源文件。
- `references.bib`：四条参考文献。
- `mathematical_review.md`、`reference_verification.md`：本次内部检查的范围和结果。
- `typesetting_record.json`、`chinese_typesetting_revision.json`、`delivery_qa.json`、`SHA256SUMS.txt`：排版、交付检查和文件校验记录。

## 结论的范围

正文无条件于极值图分类的结论是：三个特定生成函数 A、E、M 均非代数。这部分使用 Divoux–Wang 的已有渐近定理。

更强的自然边界、线性递推、伸缩和数字模型排除结论，对实际 P(n) 的应用均需要条件R。本文准确陈述该条件，但没有证明实际序列满足它。本文没有证明“一般闭式不存在”，也没有证明NP困难性或一般算法下界。

## 排版说明

中文版已按反馈重写措辞并重做版式：正文使用思源宋体，标题使用思源黑体，西文使用 Times New Roman，公式为可放大阅读的矢量字形。英文版保留此前已检查的排版。两版均有可选择的正文文字，完整公式保留在 Markdown 和 LaTeX 源文件中。本机没有 TeX 编译器，因此所附 PDF 不是由 XeLaTeX 编译而来，也未声称 LaTeX 源文件已在本机编译通过。

编译 LaTeX 源文件可使用 XeLaTeX；中文文件使用 SimSun，正文使用 Times New Roman，其他系统可将字体配置替换为当地可用字体。参考文献已写在正文末尾，单独的 BibTeX 文件便于迁移至投稿模板。

## 状态与许可

AI 工具参与整理、翻译、排版和内部核对。这些检查不等同于外部同行评审、全面新颖性检索或本稿的形式化验证。

© 2026 刘星辰、叶祥宇 / Xingchen Liu and Xiangyu Ye。稿件和源文件采用 [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) 许可。

## English reading guide

Read the four main sections first. They explain what is excluded, what requires Hypothesis R, and what is not resolved. Appendices A–E retain the precise statements and full proofs. The non-algebraicity results for A, E, and M use the known leading asymptotic; the stronger consequences for the actual sequence remain conditional on R. No general impossibility of closed forms or computational-hardness result is claimed.

The editable Markdown files are the content sources. The PDFs were rendered locally; the exported XeLaTeX sources have not been compiled in this environment. This is a separate local draft, with no automatic public publication.
