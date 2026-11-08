# Revision v0.4.0: scope and validation

Base: main at `cac0b601798d09d49233a8bc9d868c46491f5517`.
Branch: `revision/rigorous-scope-qregular-20261108`.

## Mathematical changes

- A.5 proves that a rational-valued complex q-regular sequence whose scaled powers-of-q subsequence converges has a rational limit. The proof includes rational-function descent; it does not assume rational representation matrices.
- A.6 applies this to a_n and m_n with d=0 and d=2. P(n) is excluded separately by factorial growth. None requires R, but the cited extremal asymptotic remains an external input.
- Natural-boundary, non-P-recursiveness and contraction applications retain R. Mixed derivative-contraction identities are necessary, not sufficient.
- A rounded-integer sequence shows that the leading asymptotic and integrality do not imply a natural boundary.
- Research-notes snapshot c049e04062ed122c71f519857d54366d07b7019b contains a route to actual R. The F/J-to-R analytic step gives C=L, r0=4. The upstream path-recovery, uniform-tail, zero-diamond-window and depth-induction chain has not been completely independently reverified in this revision. The manuscript neither denies the route nor declares the whole chain certified.

## Checks actually performed

- Independent mathematical reviews of A.5 and its applications agree; full proof is in the manuscript and `independent_qregular_check.md`.
- Exhaustive enumeration of all tournaments n=1,...,6 gives P(n)=1,1,3,5,15,45. The half-scale reconstruction identity was checked with exact rational arithmetic at those indices.
- Appendix E differential-binary identity checked with exact rational arithmetic for n=1,...,4096.
- The test script is `review/check_identities.py`. Finite tests are not substitutes for the proofs.
- All 14 current Lean module SHA-256 values match the existing `lean/verification/result.json`. No Lean source was modified. **Lean was not rerun for this revision.** A.5/A.6 and Appendices B--E remain outside that formalization.
- New references [5] and [6] were checked against arXiv:math/0501379 and the official Journal of Integer Sequences page for Article 13.2.10.
- Python helper syntax checked. `git diff --check` passed.
- Removed existing duplicate amsthm imports in the English source and made Markdown export strip trailing whitespace. The existing GitHub Actions workflow was left unchanged because its proposed edit was blocked by the connector security review. No workflow permissions were added or changed.

## PDF build

Both native TeX sources compiled directly with XeLaTeX (TeX Live 2024), including the Chinese ctex source; no substitute article-class source was used for the delivered files. Missing local dependencies were supplied from official CTAN/TeX Live distributions (ctex, xeCJK, zhnumber, STIX Two, Fandol). English: 12 pages; Chinese: 11 pages. Both final logs had no overfull boxes, missing characters or warnings. Every page was rendered and visually checked as a contact sheet; the English reference page was additionally inspected at higher resolution. Local line-break support uses xurl/path and emergency stretch.

On a complete TeX Live 2024 installation with these packages and fonts, run `xelatex -interaction=nonstopmode -halt-on-error nonalgebra_en.tex` and the analogous Chinese command from `paper/`.

## Remaining verification boundary

The manuscript still requires full independent verification or self-contained incorporation of the upstream research-note inputs before its R-based applications can be presented as independently certified unconditional results. The current revision makes no novelty-priority claim for the general q-regular limit observation.
