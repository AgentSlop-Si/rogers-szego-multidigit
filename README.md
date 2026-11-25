# Paper 9: Multi-Digit Base-p Squarefreeness and Christoffel-Darboux Kernel Nonvanishing for Rogers-Szego Polynomials at Prime-Power Roots of Unity

## Files
- `main.tex` — Submission-ready `amsart` LaTeX manuscript (Part II sequel to [rogers-szego-discriminants](https://github.com/AgentSlop-Si/rogers-szego-discriminants)).
- `references.bib` — Clean BibTeX bibliography.
- `verify_rogers_szego_multidigit.py` — Standalone Python 3 (stdlib only) exact verifier checking: (1) the exact shifted continuant, determinant, $g_m^0(0) = (-1)^u Q_u$, and Chebyshev shifted-derivative $(g_m^U)'$ identities over $\mathbb{Q}(q)[X]$ (plus the $p=3, m=3$ negative control $P_3'(0)$ valuation $2 \ne 1$); (2) the sparse-suffix carry lemma across multi-digit suffixes with up to $4$ middle digits (including $n=14{,}751$ and $n=4{,}917$) and out-of-scope odd-middle negative controls ($m=819$ and $m=273$); (3) the four-parity endpoint carry lemma exhaustively across all $147{,}153$ pairs at $m=543$ and multi-digit fixtures for $p=3,5,7$; (4) the adjacent cap $R_k(h) - W(\lfloor h/2\rfloor) \le L/(2p)$ with unique equality at $h=L$, parity-compensated $g'$ convolution scores, $k=3$ boundary/annulus margins, and $k\ge 4$ negative margin $p-\lambda$; (5) arbitrary-prefix level-one outer disk caps and 30-digit annulus margins; and (6) direct finite-field good-reduction squarefreeness and neighbor-coprimality certificates for $P_n$ and $H_n$ at $n=10, 20, 171, 543, 549$.
- `RogersSzegoMultidigit.lean` — Zero-dependency Lean 4 formal verifier (core `Init` only, verified in Lean 4.36.0 with zero `sorry`, zero custom axioms, and zero `native_decide`) symbolically proving the geometric legality bound $n < 3p^r \le p^{r+1}$, the annulus dominance inequality $M+\rho < D/2$, boundary-gap positivity for $j\ge 2$, bottom-$p$ ($j=1$), and adjacent $k=3, j=2$, the exact $k\ge 4$ separate-margin deficit $\lambda > p$, the high-order carry bracket negativity in bottom-$p$ derivative selection, and consecutive-neighbor coprimality propagation; plus pure-kernel verifications of the sparse carry lemma ($m=171, 57$), the unique adjacent-cap equality ($p=3,5$), the four-parity endpoint lemma ($m=57$), both negative controls, and a direct $\mathbb{F}_{109}[X]$ good-reduction squarefreeness & coprimality proof at $n=20$ ($p=3, r=2, s=3$).

## How to Compile PDF
1. Upload `main.tex` and `references.bib` to Overleaf (or compile locally with `latexmk -pdf main.tex`).

## Suggested Submission Metadata
- **arXiv primary / secondary:** `math.NT` (Number Theory) / `math.CA` (Classical Analysis and ODEs), `math.CO` (Combinatorics)
- **MSC 2020:** Primary `33D45`, `11S05`; Secondary `11R18`, `11C08`, `42C05`
- **Target journals (zero-fee):** *Journal of Number Theory*, *Journal of Approximation Theory*, *Ramanujan Journal*.

## Verify Computations and Lean Proofs
```bash
python3 verify_rogers_szego_multidigit.py
lean RogersSzegoMultidigit.lean
```
