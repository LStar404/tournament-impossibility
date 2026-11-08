"""Restyle the paper source into a proper article layout.

The source shipped in the repository was a flat `ctexart` document: Latin set in
TeX Gyre Termes while mathematics stayed in Computer Modern, no title block, no
running head and manually numbered sections. This script replaces the preamble,
builds a real title block and switches the numbered headings to automatic
numbering. It is idempotent and leaves the body text untouched.
"""
import io
import re
import sys

path = sys.argv[1] if len(sys.argv) > 1 else 'paper/nonalgebra_zh.tex'
text = io.open(path, encoding='utf-8', newline='').read()
text = text.replace('\r\n', '\n')

OLD_PREAMBLE = r"""\documentclass[UTF8,11pt,fontset=fandol]{ctexart}
\usepackage[a4paper,margin=25mm]{geometry}
\usepackage{amsmath,amssymb,booktabs,longtable,array,hyperref}
\usepackage{fontspec}
\setmainfont{TeX Gyre Termes}
\linespread{1.3}
\setlength{\parskip}{4pt}
\hypersetup{colorlinks=true,linkcolor=black,urlcolor=blue}
\begin{document}
"""

NEW_PREAMBLE = r"""\documentclass[UTF8,11pt,fontset=fandol]{ctexart}
\usepackage[a4paper,margin=25mm]{geometry}
\usepackage{amsmath,booktabs,longtable,array,hyperref,fancyhdr}
\usepackage{fontspec}
\usepackage{unicode-math}
\setmainfont{STIXTwoText}[Extension=.otf,
  UprightFont=*-Regular, BoldFont=*-Bold,
  ItalicFont=*-Italic, BoldItalicFont=*-BoldItalic]
\setmathfont{STIXTwoMath-Regular.otf}
\linespread{1.3}
\setlength{\parskip}{4pt}
\hypersetup{colorlinks=true,linkcolor=black,urlcolor=blue}
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\small 刘星辰}
\fancyhead[R]{\small 2026.11}
\fancyfoot[C]{\small\thepage}
\renewcommand{\headrulewidth}{0.4pt}
\begin{document}
"""

OLD_TITLE = "\\begin{center}{\\LARGE\\bfseries 哈密顿路极值序列的非代数性与公式限制}\\end{center}\n刘星辰\n\n个人研究者\n\nlxc-em5158@outlook.com\n\n2026年11月3日 · 整理版 v0.2.0\n"

NEW_TITLE = r"""\begin{center}
{\LARGE\bfseries 哈密顿路极值序列的非代数性与公式限制\par}
\vspace{1.2em}
{\large 刘星辰\par}
\vspace{0.5em}
{\normalsize 个人研究者\par}
{\normalsize \texttt{lxc-em5158@outlook.com}\par}
\vspace{0.5em}
{\small 2026年11月3日 · 整理版 v0.2.0\par}
\end{center}
\vspace{1em}
"""

changed = False
if OLD_PREAMBLE in text:
    text = text.replace(OLD_PREAMBLE, NEW_PREAMBLE)
    changed = True
if OLD_TITLE in text:
    text = text.replace(OLD_TITLE, NEW_TITLE)
    changed = True

text, n = re.subn(r'\\section\*\{\s*(\d+)\.\s*([^}]*)\}', r'\\section{\2}', text)

io.open(path, 'w', encoding='utf-8', newline='\n').write(text)
print('preamble/title replaced:', changed, 'numbered sections converted:', n)
