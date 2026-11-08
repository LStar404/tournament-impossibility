"""Render a paper .tex file as Markdown for reading on GitHub.

Handles the subset used by paper/nonalgebra_en.tex: the centred title block,
\\section headings, display maths written as \\[...\\], and the inline markup
commands \\textbf, \\emph, \\texttt, \\path and \\url. Both current papers
use this subset; arbitrary TeX tables are not supported.
"""
import io
import re
import sys

INLINE = [
    (r'\\path\{([^{}]*)\}', r'`\1`'),
    (r'\\url\{([^{}]*)\}', r'<\1>'),
    (r'\\texttt\{([^{}]*)\}', r'`\1`'),
    (r'\\textbf\{([^{}]*)\}', r'**\1**'),
    (r'\\emph\{([^{}]*)\}', r'*\1*'),
]


def apply_inline(text):
    for pattern, repl in INLINE:
        text = re.sub(pattern, repl, text)
    return text


def strip_wrappers(text):
    text = text.replace('\\par', '')
    text = re.sub(r'\\(LARGE|large|normalsize|small|bfseries)\s*', '', text)
    text = re.sub(r'\\vspace\{[^}]*\}', '', text)
    return text.replace('{', '').replace('}', '')


def main():
    src, dst = sys.argv[1], sys.argv[2]
    tex = io.open(src, encoding='utf-8').read()
    body = tex.split('\\begin{document}', 1)[1].split('\\end{document}', 1)[0]

    head = ''
    match = re.search(r'\\begin\{center\}(.*?)\\end\{center\}', body, re.S)
    if match:
        block = strip_wrappers(apply_inline(match.group(1)))
        lines = [ln.strip() for ln in block.splitlines() if ln.strip()]
        title = lines[0].replace('\\ ', ' ').strip()
        rest = [ln.replace('\\ ', ' ').strip() for ln in lines[1:]]
        head = '# ' + title + '\n\n' + '\n\n'.join(rest) + '\n\n'
        body = body.replace(match.group(0), '', 1)

    body = apply_inline(body)
    body = body.replace('\\begingroup\\small', '').replace('\\endgroup', '')
    body = body.replace('\\noindent ', '')
    body = body.replace('\\[', '$$').replace('\\]', '$$')
    body = re.sub(r'\\section\*?\{([^}]*)\}', r'## \1', body)
    body = body.replace('\\qed', '').replace('$\\square$', '')
    body = re.sub(r'\\vspace\{[^}]*\}', '', body)
    body = body.replace('\\ ', ' ')
    body = re.sub(r'\n{3,}', '\n\n', body)

    rendered = head + body.strip() + '\n'
    rendered = '\n'.join(line.rstrip() for line in rendered.splitlines()) + '\n'
    io.open(dst, 'w', encoding='utf-8', newline='\n').write(rendered)
    print('wrote', dst)


if __name__ == '__main__':
    main()
