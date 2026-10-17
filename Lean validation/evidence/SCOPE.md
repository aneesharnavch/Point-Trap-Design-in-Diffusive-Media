# Formalization scope: the three Time Traps papers

Confirmed against `../README.md` on 13 September 2026. This formalization
concerns only **Time Traps**. The active goal covers **every analytically proved
result across its three current papers**, including the historical appendices
and the foundations needed to justify the stated interpretations. Other research projects in the workspace
are outside this scope.

| Paper | Authoritative LaTeX source | Role |
|---|---|---|
| 21-page primary preprint | `../preprint/main.tex` | Current submission version; primary statements of the three central theorem families |
| 33-page longer paper | `../paper/local-time-traps-final-paper.tex` | Additional theorem variants, equality classifications, and consequences |
| 198-page expanded companion | `../paper/expanded/local-time-traps-expanded-final.tex` and its included chapters | Detailed supporting derivations and the five audited extensions |

Page counts identify the versions described in the project index; they are
not counts of independent mathematical claims. Repeated formulations of a
result share a formal target. The compiled Lean proofs certify mathematical
statements, not publication priority.

## Result map

| Result | Preprint reference | Longer-paper reference | Ledger |
|---|---|---|---|
| Arbitrary-medium minimax and every optimizer | `thm:medium` | `thm:medium-main` | I01–I08 |
| Homogeneous optimum and uniqueness | `eq:homogeneous-optimum` | `cor:medium-homogeneous` | I09 |
| Graph edge barriers, ordinary and passive tip | `lem:edge` | `lem:graph-edge` | G03–G04 |
| Graph mass–resistance bounds | `thm:graph` | `thm:graph-mass-resistance` | G05 |
| Complete graph equality and strength allocation | `eq:graph-strengths` | `thm:graph-equality` | G06 |
| Exact graph deficit | `eq:graph-deficit` | `thm:graph-deficit` | G07 |
| Prescribed-strength spectral optimum | `thm:spectral` | `thm:spectral-prescribed` | E01–E06 |
| Joint spectral allocation and periodic optimum | Following `thm:spectral` | `thm:spectral-budget`, `cor:spectral-exner` | E07–E08 |
| Medium comparison and robustness | Appendix A | `thm:medium-ordering` | X01 |
| Reactive endpoints, comparison, homogeneous formula | Appendix A | `thm:medium-endpoints`, `cor:medium-endpoint-ordering`, `cor:medium-endpoints-homogeneous` | X02 |
| Majorization, splitting, inverse cell design | Appendix B | `thm:spectral-majorization`, `thm:spectral-inverse` | X03 |
| Robin spectral placement | Appendix B | `thm:spectral-robin` | X04 |
| Variable-profile graph bound and equality | Not stated in the primary preprint | `thm:graph-variable`; expanded chapter 11, `thm:exp-x12-local`, `thm:exp-x12-global` | X05 |
| Joint graph geometry and reactivity | Not separately stated | `cor:graph-geometry` | X06 |
| Exact spectral deficit | Not separately stated | `eq:spectral-deficit` | X07 |
| Spectral limiting consequences | Not separately stated | `eq:spectral-constant-check`, `eq:spectral-large-N`, `eq:spectral-strong` | X08 |

The expanded companion's chapter 11 also supplies the Robin theorem
`thm:exp-x16`, majorization theorem `thm:exp-x19-majorization`, splitting
proposition `prop:exp-x19-split`, and inverse theorem `thm:exp-x19-inverse`.
These are supporting versions of X03–X05, not extra completed results.

Analytic well-posedness, source-coordinate changes, Rayleigh-quotient
identification, and the stochastic local-time interpretation remain required
dependencies. The expanded companion's historical stationary-average results
are also in the verification scope; their earlier status or lack of novelty
does not exclude them. They remain identified as background rather than new
contributions. Their exact design, deficit, stability, reversible-medium,
and perturbation targets are H01–H05 in `TARGETS.md`.

## Proof method

The requested proofs are analytical, geometric, or exact calculational
arguments. Lean checks those arguments and their quantified assumptions.
Integral identities, continuity, monotonicity, compactness, exact algebra,
and inequalities are admissible methods. Numerical searches, simulation,
finite-grid sampling, and approximate numerical certificates do not replace
any theorem. Proof-producing symbolic algebra tactics operate on exact
expressions; they are not numerical evidence for the paper's claims.

The educational toolbox and foundational facts must be linked to checked
Mathlib results or project proofs when used. Purely numerical experiments
and plots are not mathematical proof targets. Analytically established
identities discussed alongside computations remain in scope.

See `TARGETS.md` for actual implementation status. A checked supporting lemma
does not mark an entire paper or theorem family complete.
