# IRIS papers: pollutant sequestration in porous material

Updated 12 October 2026. Status: PLAN ONLY. This revision replaces the
microfluidic biosensor application and the earlier title-page/contents
outline. It specifies two research reading versions, their application study,
software, figures, evidence, and final impact statements. No new pollutant
simulations, formal proofs, external reviews, or device-performance results
are reported by this plan.

The current manuscript remains publication/iris/iris-paper-draft.tex.
The requested deliverables are an approximately 8-page synopsis and a
15–19-page detailed paper, targeting 18 pages including references. They
present the same work. The detailed version is written first; the synopsis
uses the same theorem statements, notation, result records, and figure data.

## 1. The application and the research question

Study activated-carbon sequestration of a hydrophobic organic contaminant,
initially a PCB congener with sufficient published parameter data, inside
water-saturated porous sediment. The primary design is a finite number of
carbon-rich treatment bands, with a fixed total mass of the same carbon.
Choose band depths and allocate carbon among them.

The engineering question is:

> Can the same carbon dose lower the time required to sequester contaminant
> from the least favorable starting location, and reduce the pollutant that
> remains available for release, by changing where the carbon is placed?

The initial simulation is a contained, stagnant sediment-core model. This
gives the reflecting boundaries used by the existing interval theorem.
A subsequent sediment–water exchange model evaluates release to overlying
water under the boundary conditions of the selected published benchmark.
Those boundary conditions are an application extension; a reflecting-domain
optimality theorem does not automatically optimize escaped mass.

Adsorption transfers contaminant to carbon. It does not destroy it.
The paper must distinguish reduced dissolved/native-labile concentration,
carbon-bound mass, desorption, and pollutant exported from the domain.
Regeneration, recovery, disposal, toxicity reduction, and ecological effects
are separate questions.

This is a design study for an experimentally calibratable core or treatment
layer. Optimal treatment-band depths in a model are not yet a demonstrated
field installation method. Record accessible depths and disturbance
constraints; do not assume that arbitrary placement in natural sediment is
costless or practical.

## 2. Published systems to reproduce

Bibliographic identities below were checked on 12 October 2026. Full model
and parameter reproduction remains planned. These are relevant literature
anchors, not an assertion that one is the current best-performing system.

| Role | Published work | Use |
|---|---|---|
| Closest stagnant-contact model | Choi, Cho, Werner and Luthy (2014), In Situ Sequestration of Hydrophobic Organic Contaminants in Sediments under Stagnant Contact with Activated Carbon. 2. Mass Transfer Modeling. DOI: https://doi.org/10.1021/es404209v | Recover transport and adsorption mechanisms, geometry, carbon dose, and reported validation curves |
| Sediment–water release benchmark | Qiu et al. (2023), Model of Activated Carbon Dose and Sediment–Water Diffusion Fluxes of Hydrophobic Organic Chemicals: Implications for Sediment Remediation. DOI: https://doi.org/10.1021/acsestwater.2c00587 | Reproduce dose-versus-flux calculations before introducing spatial redesign |
| Practical treatment context | Wikström et al. (2024), Thin-layer capping with granular activated carbon and calcium-silicate to remediate organic and metal polluted harbor sediment – A mesocosm study. DOI: https://doi.org/10.1016/j.scitotenv.2024.174263 | Record treatment geometry, operating conditions and endpoints; do not attribute mixed-amendment effects to carbon alone |
| Earlier PCB transport reference | Modeling Polychlorinated Biphenyl Mass Transfer after Amendment of Contaminated Sediment with Activated Carbon (2006). DOI: https://doi.org/10.1021/es052215k | Check mass-transfer mechanisms and parameter conventions |

Select one contaminant/carbon/sediment parameter set from a reproducible
source. Record every parameter's units, measurement or fit status, source
page/table, uncertainty, and transformations. Do not splice unrelated
pollutants and carbon types into a supposedly published device.

First reproduce the original baseline using its original physics. Next
identify an admissible treatment-band redesign or use the theorem as an
initialization in that physical model. If published data or code cannot be
recovered, the result remains a transparent model benchmark. Describe a
successful comparison by the specific reproduced design and metric; use
"state of the art" only after a current, documented comparison supports it.

## 3. Physical model and its exact mathematical connection

Use a slab coordinate x in [0,L], interpreted as depth. Work per unit
cross-sectional area.

| Symbol | Physical meaning | Units in SI |
|---|---|---|
| c(x,t) | Dissolved pollutant concentration in porewater | kg pollutant / m^3 water |
| theta(x) | Water-filled porosity | dimensionless |
| D_p(x) | Effective pore diffusivity under the declared convention | m^2/s |
| a(x)=theta(x) D_p(x) | Bulk diffusive transport coefficient | m^2/s |
| rho_b(x) | Dry sediment bulk density | kg dry sediment / m^3 bulk |
| K_d(x) | Linear native-sediment distribution coefficient | m^3 water / kg dry sediment |
| rho(x)=theta(x)+rho_b(x)K_d(x) | Equilibrium storage coefficient | dimensionless |
| m_j | Activated carbon in band j per cross-sectional area | kg carbon / m^2 |
| k_a | Effective dilute adsorption coefficient for that carbon | m^3 water / (kg carbon s) |
| kappa_j=k_a m_j | Point-sink strength in the dilute irreversible limit | m/s |

The native-sediment sorption reduction assumes fast local linear equilibrium.
If the chosen published model instead has slow desorption, retain an explicit
native-sediment reservoir and calibrate its transfer rates. Avoid including
the same storage twice through both rho and an additional reservoir.

The point model is

$$
\rho(x)\partial_t c
=\partial_x(a(x)\partial_x c)
-\sum_{j=1}^{N}\kappa_j c(x_j,t)\delta_{x_j},
\qquad a c_x(0,t)=a c_x(L,t)=0.
$$

For first irreversible sequestration in this reduced reversible-diffusion
model, the expected time u solves

$$
-(a u')'+\sum_j\kappa_j u(x_j)\delta_{x_j}=\rho,
\qquad (a u')(0)=(a u')(L)=0.
$$

Thus the existing minimax theorem applies to M=max u under the stated
positive-coefficient, finite-trap, reflecting-boundary assumptions. Here rho
is storage/speed density, not the initial pollutant concentration. Specify
c(x,0) separately. The source-mass coordinate used by the proof is

$$
S=\int_0^L\rho\,dx,\quad
Z(x)=S^{-1}\int_0^x\rho(y)\,dy,\quad
\Omega(z)=\frac{S^2}{a(X(z))\rho(X(z))}.
$$

With identical carbon and constant k_a,

$$
\sum_jm_j=M_C,\qquad K=\sum_j\kappa_j=k_a M_C.
$$

This is the conditional link from a reactivity budget to a real material
budget. If accessibility, carbon chemistry or local k_a varies, fixed carbon
mass no longer implies fixed K. Retain the physical mass constraint and state
which exact theorem assumptions have changed.

For finite bands of widths w_j, use carbon density
mu(x)=sum_j (m_j/w_j) 1_{band j}(x). The linear reaction density is
r(x)=k_a mu(x), so integral over band j of r equals kappa_j.
Then independently solve

$$
\rho c_t=(a c_x)_x-r(x)c.
$$

The application extension introduces carbon-bound pollutant b(x,t):

$$
\rho c_t=(a c_x)_x-\partial_t b,\qquad
\partial_t b=k_a\mu c
\left(1-\frac{b}{\mu Q_{\max}}\right)-k_{\rm des}b
$$

on carbon-bearing regions. Q_max is capacity per unit carbon mass.
This is a candidate kinetic model; reproduce the selected source's kinetics
instead if different. The point theorem describes the dilute, unsaturated,
negligible-desorption limit. Finite capacity, native desorption, weak
advection, and sediment–water exchange are evaluated as extensions.

## 4. Design competitors and fair comparisons

Hold sediment, initial contamination, carbon chemistry, total dose, treatment
duration and boundary conditions fixed within each comparison.

| Comparator | Purpose |
|---|---|
| Untreated core | Treatment-effect control; not the principal optimization comparison |
| Equal-depth bands with equal dose | Principal simple layout baseline |
| Equal-source-mass bands | Tests the value of the coordinate change alone |
| Published cap or amendment layout | External reference, after baseline reproduction |
| Direct physical-PDE optimization | Strong competitor with the same admissible positions, widths, dose limits and numerical budget |
| Theorem reconstruction | Tests the reduced design method |
| Theorem initialization plus physical refinement | Measures benefit after finite-band and kinetic effects are restored |
| Uniformly mixed carbon | Distributed-treatment reference with its distinct installation assumptions |

Uniform mixing can outperform finitely many reactive bands. In the ideal
homogeneous setting, a uniformly distributed sink achieves the reaction
floor S/K, whereas finite point arrays retain a diffusion penalty.
The numerical study must allow that outcome. Claim an improvement within the
stated placement class, not superiority to every distributed treatment.
If practical mixing/disturbance costs are unavailable, do not invent a cost
advantage for bands.

Impose nonoverlapping bands, minimum separation, accessible depths, maximum
local carbon loading, and fixed total mass. If the reconstructed unconstrained
solution violates those constraints, identify it as an analytical reference
and run constrained physical refinement; projection alone does not preserve
the theorem's optimality guarantee.

Do not promise a percentage gain in advance. Existing 2.86% interval and
7.96% spectral examples remain mathematical controls, not PCB-remediation
results. The best new outcome could be a better treatment layout, a material
saving for a fixed target, or fewer PDE solves to reach the same performance.

## 5. Metrics and success criteria

### Main-paper metrics

1. Worst-start expected sequestration time M for the applicable linear
   reflecting model.
2. Fraction of initial pollutant bound to carbon by a declared time:
   F_AC(T)=integral b(x,T) dx / M_initial.
3. Carbon dose required to reach the same declared sequestration or
   concentration target.
4. For the open-boundary benchmark, cumulative pollutant export to overlying
   water and its reduction relative to the matched layout.

Report both absolute quantities with units and relative changes. Distinguish
optimization at fixed material from dose minimization at fixed performance.
Check monotonicity in dose before applying bisection to a dose target.

### Supplementary metrics

- Porewater concentration profiles, peak concentration, and native-labile stock.
- Average first-capture time under an explicit starting distribution.
- t50 and t90 for sequestration of the initial mass, with unattainable
  thresholds reported as such when capacity is insufficient.
- Carbon loading and utilization by band.
- Principal decay rate, restricted to the linear model; do not infer it
  from nonlinear saturation runs.
- Release/rebound during a clean-water exchange or desorption challenge.
- Total mass closure: dissolved + native-sorbed + carbon-bound + exported.
- Performance under coefficient uncertainty, depth errors and dose errors.
- Point-to-band and 1D-to-2D discrepancies.
- Mesh and time convergence, linear/nonlinear residuals and conservation errors.
- Runtime, PDE solve count, memory, optimizer failures, and best feasible costs.

For deterministic PDE results, use mesh/time refinement and independent
solvers to assess numerical error. For sampled uncertain media or stochastic
trajectories, report sampling uncertainty separately. A sampling interval does
not include discretization or model error.

Preregister a target of less than 0.2% change in headline metrics over the
final refinement, with a stricter tolerance when a claimed advantage is
small. An optimization gain must remain larger than its estimated numerical
uncertainty. Such estimates are not rigorous enclosures. Reproduction of a
published curve uses an explicit tolerance justified by data precision.

## 6. Proposed implementation

New package root: applications/porous_remediation/.
All paths below are proposed. Existing numerical and formal evidence remains
in its recorded locations.

~~~text
applications/porous_remediation/
  README.md
  pyproject.toml
  configs/
    analytical_controls.yaml
    sediment_core.yaml
    published_stagnant_contact.yaml
    published_water_exchange.yaml
    robustness.yaml
    remobilization_conjecture.yaml
  sources/
    literature.csv
    parameter_provenance.csv
    baseline_reproduction.md
  src/porous_remediation/
    models/
      medium.py                 # Porosity, diffusivity, storage, units
      sorption.py               # Native and carbon sorption, capacity, desorption
      carbon_budget.py          # Mass-to-reactivity mapping
      treatment_bands.py        # Band geometry and installation constraints
      boundaries.py             # Closed core and sediment–water exchange
    solvers/
      balanced_cells.py         # Source coordinate, barriers and scalar root
      physical_flux.py          # Independent physical-coordinate reference
      finite_volume_1d.py       # Conservative finite-band transport
      finite_element_2d.py      # Independent transverse/heterogeneity checks
      transient_sorption.py     # Carbon-bound mass and kinetics
      spectrum.py               # Linear eigenvalue/transfer comparisons
      discounted_capture.py     # Independent-clock capture objective
    optimization/
      theorem_design.py
      equal_band_baselines.py
      published_layout.py
      uniform_amendment.py
      direct_pde_search.py
      constrained_refinement.py
      minimum_dose.py
    experiments/
      reproduce_controls.py
      reproduce_literature.py
      compare_layouts.py
      convergence.py
      finite_capacity.py
      rebound_and_export.py
      uncertainty.py
      search_conjecture.py
    evidence/
      metrics.py
      claim_ledger.py
      provenance.py
      lean_crosswalk.py
      export_tables.py
    figures/
      physical_model.py
      source_cells.py
      treatment_profiles.py
      performance.py
      convergence.py
      conjecture.py
  tests/
    test_units.py
    test_budget.py
    test_exact_controls.py
    test_mass_conservation.py
    test_limit_models.py
    test_solver_agreement.py
  results/
    raw/
    tables/
    figures/
    manifests/
    failures/
~~~

Use pinned NumPy, SciPy, Matplotlib, scikit-fem and pytest dependencies.
No simulation package installation or execution is part of this planning
revision. Published-model requirements may justify an additional dependency.

Reuse the existing validated formulas and controls, but keep independent
physical-solver paths separate from the balanced-cell evaluator. In
particular, verification/generalized/verify_generalized.py targets a
stationary-mean objective; it cannot simply be renamed a minimax solver.

Each run stores model/objective identifiers, units, coefficient fields,
initial conditions, boundary conditions, carbon mass and capacities, all
constraints, seed, solver tolerances, mesh/time settings, source hashes,
optimizer budget, measured runtime and status. All plots read result records.
Keep failed, infeasible and timed-out runs.

## 7. Execution order and proposed campaign

| Stage | Work | Exit condition |
|---|---|---|
| A. Source and calibration | Recover one coherent published parameter set and baseline | Units and source provenance complete; baseline reproduced |
| B. Exact controls | Reproduce current interval, graph and spectral controls | Original objectives and residuals recovered |
| C. Finite bands | Conservative 1D implementation, dose mapping, independent backward/forward checks | Correct budgets, positivity, mass conservation, thin-band agreement |
| D. Layout comparison | Equal bands, mass-coordinate baseline, theorem design and direct PDE optimizer | Matched constraints and evaluation budgets; uncertainty below claimed effects |
| E. Physical extensions | Finite capacity, desorption, water exchange and selected 2D cases | Headline conclusions checked under the declared extensions |
| F. Conjecture | Reproduce existing exploratory checks; adversarial search | Reproducible supporting evidence or retained counterexample |
| G. Papers | Generate tables/figures, update exact claim crosswalk, draft detailed paper then synopsis | Claims match records; final-size layout and page count checked |

Initial numerical scope: 6 coefficient profiles x 4 trap counts (1,2,4,8)
x 3 dose regimes = 72 linear configurations. A profile with discontinuous
layers must be identified as an extension of a theorem stated for continuous
coefficients, or replaced by a documented smooth transition.

Choose 12 representative configurations for detailed finite-width,
capacity and sediment–water exchange tests. Use three meshes for those cases;
select a smaller subset for independent 2D verification. Define uncertainty
samples and fabrication perturbations before inspecting their performance.
These counts are planning targets, not completed experiments.

A failed published reproduction blocks a claim about improving that
published system, but does not prevent a clearly labeled synthetic study.
Absence of a performance gain is a reportable result, not grounds to change
the baseline or discard a medium.

## 8. Future conjecture with an environmental interpretation

Retain the existing homogeneous worst-start discounted-capture conjecture.
Change its application interpretation from target degradation to capture
before a hypothetical independent remobilization/disturbance clock.

Let T_R ~ Exp(s), independent of the modeled diffusion and first-capture
time tau. Then

$$
\Pr_x(\tau<T_R)=\mathbb E_x[e^{-s\tau}].
$$

This is a deadline abstraction, not a weather model or the probability of
actual export through a sediment boundary. Mobilization can depend on flow,
position, sorption state and correlated weather; those mechanisms require
their own model.

For homogeneous a=D, rho=1, reflecting endpoints and total strength K,
define eta_s=L sqrt(s/D)/(2N). The conjecture is

$$
\sup_{\substack{0<x_1<\cdots<x_N<L\\
 \kappa_j>0,\ \sum_j\kappa_j=K}}
\inf_{x\in[0,L]}\mathbb E_x[e^{-s\tau}]
=
\left[\cosh\eta_s+
\frac{2N\sqrt{Ds}}{K}\sinh\eta_s\right]^{-1}
\quad(s>0).
$$

The right side is established for the equal-strength, equal-midpoint array.
Its worst-start optimality over all admissible arrays remains unresolved in
the project record. Existing notes report exploratory N=2,3 searches; their
results need regeneration as structured records before publication.

If true, one homogeneous arrangement would maximize the worst-start
probability of sequestration before every independent exponential deadline.
This does not establish optimality at every fixed time, for heterogeneous
sediment, for saturation, or for actual storm-driven contaminant export.
Declaring degradation of the pollutant a competing failure would be the wrong
environmental interpretation.

Test N in {1,2,3,4,6,8}, with dimensionless KL/D and sL^2/D each spanning
0.01,0.1,1,10,100. This gives 150 proposed parameter combinations. Search
clustered/near-boundary arrays and unequal strengths, locate all candidate
starting-position minima, and use independent Green/resolvent and PDE
calculations. Recheck close competitors with high precision. Use stable
logarithmic evaluation for tiny probabilities.

The missing proof step concerns comparison with arbitrary asymmetric
one-trap arches; the symmetric hyperbolic cell cost and its convexity are
not by themselves a proof for all arrays. Record new statements as conjecture,
numerical evidence, or proved lemma according to their actual status.

## 9. Paper structure and page budgets

Begin with title and byline, a concise abstract, then Introduction and
objective. No separate cover page or table of contents. Merge the old
"Innovation" and scattered applications paragraphs into the introduction.
Use "Model ingredients and notation" for the accessible mathematical
dictionary. Introduce the pollutant application there and return to it
throughout the proofs, examples and discussion.

Working title: Point-Trap Design in Porous Media: Minimax Capture,
Graph Bounds, and Pollutant Sequestration.

| Material | Synopsis pages | Detailed pages |
|---|---:|---:|
| Title/byline, abstract, introduction/objective | 1.00 | 1.25 |
| Model ingredients and notation | 0.60 | 0.90 |
| Mathematical model and source coordinate | 0.70 | 1.35 |
| Interval minimax derivation and reconstruction | 1.40 | 3.40 |
| Graph torsion, weighted means and deficit | 0.65 | 2.00 |
| Spectral form, phase argument and consequences | 0.75 | 3.00 |
| Pollutant application, methods and results | 1.20 | 2.60 |
| Lean and computational validation | 0.55 | 1.00 |
| Impact, limits and conjecture | 0.35 | 0.90 |
| References | 0.80 | 1.60 |
| Total | 8.00 | 18.00 |

These budgets include local figures and tables. The detailed paper retains
major proof steps for its selected claims. The synopsis gives accurate
statements and proof ideas linked to the detailed version. Extended kinetic
derivations, long parameter sweeps and source inventories belong in the
supplement. If the major proofs do not fit at readable size, reduce peripheral
extensions before shrinking fonts or compressing equations.

### Formula and proof coverage

- Derive the weak equation and jump convention; explain the local-time
  normalization and the distinction between first capture and reversible
  adsorption.
- Derive source coordinates, absorption shares, transformed flux, unique
  balanced centers and local barriers. Keep the arbitrary-competitor cases,
  including a trap outside its induced source-mass cell.
- State and prove the scalar root, fixed-partition attainment, compactness/
  strict splitting, minimax formula, and optimizer reconstruction.
- Explain weighted arithmetic–harmonic means and their equality conditions.
  Use Hölder precisely in the homogeneous endpoint-cell calculation;
  distinguish it from Cauchy–Schwarz in the graph aggregation and Jensen in
  spectral allocation.
- Retain graph J_e, Neumann-tip factor four, edge barriers, equality strengths,
  and the exact three-term deficit. The saved AMC label identifies Theorem
  4.5 as the three-term nonnegative metric-graph deficit identity.
- Retain the quadratic form Q_{x,kappa}[phi], Neumann operator H_{x,kappa},
  Rayleigh principle, positivity, phase evolution, sharp one-jump inequality,
  prescribed-strength root, cosine construction, and equality converse.
- The saved AMC auxiliary file maps equations 69–74 to the spectral master
  inequality, prescribed root/value, cell lengths, sites, and cosine profile.
  Equation 77 maps to the one-spectral-trap example. These belong in the
  spectral material, not the interval reconstruction section. Track source
  labels because the auxiliary file may reflect an earlier compilation.
- Explain P(d;k) acting on (phi,phi') and J(kappa) as the derivative jump
  matrix. Keep it distinct from the graph edge cost J_e.
- Retain h(beta), the positive splitting derivative, zeta tan(zeta), the
  strict K/L comparison, and the asymptotic expansion. Attribute the
  equal-strength/free-budget consequences according to the corrected
  Kurasov–Serio comparison.

## 10. Figures integrated into the argument

Use the user's preferred existing assets after checking their mathematical
objective and source data. Each substantial mathematical subsection gets a
relevant panel or small diagram where useful. Major sections have multiple
visual anchors through panels, not an obligation to create multiple
full-width floats. No end-of-paper atlas or adjacent unexplained image run.
Introduce each figure before it and interpret it immediately afterward.

| Location | Visuals | Source or status |
|---|---|---|
| Introduction and notation | Sediment core, carbon bands, dissolved/native/carbon-bound pollutant; notation key | New application schematic |
| Model | Physical depth to source coordinate; storage and diffusivity profiles | Retain f03-source-coordinate, adapt labels truthfully |
| Interval derivation | Balanced rises, arbitrary competitor, monotone budget root and reconstruction | Retain f05-balanced-rises and f09-budget-root; concise reconstruction panel |
| Partition search | Reduced partition landscape, candidate versus theorem distinction | Retain f12-partition-landscape with explicit objective and instance |
| Graph argument | Metric graph, reflecting tips, equality geometries, three deficit terms | Retain preferred graph-model/equality figures; clarify abstract graph versus calibrated pore network |
| Spectral argument | Sharp phase jump, prescribed root and unequal cell lengths; propagation/jump diagram | Retain preferred phase-jump/root figures |
| Analytical controls | Recorded heterogeneous one-trap comparison and matched spectral comparison | Retain f16 and f31 with original mathematical scope |
| Application results | Carbon layouts beside concentration profiles; sequestration versus time; dose–target tradeoff | New simulation outputs, only after execution |
| Validation | Independent solver convergence and compact formal/computational evidence map | New finite-band/2D evidence plus honestly labeled archived checks |
| Final conjecture | Sequestration-before-clock probability and strongest challenger gap | New conjecture sweep after execution |

The existing verification/results/two_trap_landscape is a stationary-mean
landscape: verify_local_time_traps.py plots mean_lifetime minus the optimum.
Retain it as a companion mean-objective diagnostic, or regenerate a minimax
landscape. Never label the current image a worst-start optimization result.
The existing Monte Carlo convergence figure also concerns a mean/finite-time
target and must keep that scope.

Target roughly 12–14 compact figures in the detailed version and 6–8 in the
synopsis, combining closely related panels without making labels unreadable.
Use final-size axis/legend text around 9–10 pt or larger, adequate line
weights, consistent units, and restrained captions. No multi-panel figure
may substitute for explaining the equations. Remove redundant panels before
reducing readability to meet the page budget.

Supplement figures: full parameter grids; carbon utilization by band;
finite-width convergence; capacity and desorption/rebound; cumulative export;
uncertainty/fabrication errors; runtime/PDE-call tradeoffs; all conjecture
search gaps. Supplement tables: parameter provenance, per-case outcomes,
constraint violations, solver errors, failures and code/formal mappings.

## 11. Validation and attribution

Retain the recorded evidence, with its actual scope:

| Evidence | Recorded value | Interpretation |
|---|---|---|
| Randomized homogeneous interval tests | 5,000 designs; largest residual about 1.34e-14 | Mean/energy/deficit and boundary checks |
| Generalized companion suite | 2,400 tests; largest deficit-identity residual about 3.61e-16 | Heterogeneous stationary-mean theory |
| Companion FEM check | Maximum recorded relative discrepancy about 1.43e-8 | Independent recorded mean-objective examples |
| Graph identity | Residual about 2.57e-16 | Recorded graph fixture |
| Spectral comparison | Independent difference about 2.22e-16 | Recorded prescribed-strength instance |
| October 1 Lean evidence | 2,282 modules; 10,543 named theorems; 17,355 audited declarations | Recorded dependency build and transitive axiom audit |

Relevant files:

- publication/amc-amo/shared/paper-claim-crosswalk.md
- publication/amc-amo/results/significance.json
- verification/results/verification_summary.json
- verification/generalized/results/verification_summary.json
- execution/2026-10-01/runs/lean-current-3/verification/result.json
- publication/2026-09-15-priority-revision/revision/attribution-and-scope.md

The allowed foundational axioms in the recorded audit are propext,
Classical.choice and Quot.sound. Module counts describe the development,
not independent discoveries or validation of a new environmental simulation.
New solver/chemistry/model-reduction claims require their own checks.
Python results are not automatically extracted from Lean.

Acknowledgements may credit verified upstream contributions, such as Rémy
Degenne (Inria researcher and Mathlib maintainer; integration and mean
inequalities), Patrick Massot (Université Paris-Saclay professor; interval
integration), and Lean developers Leonardo de Moura and Sebastian Ullrich.
Preserve complete module author credits in the supplement. These contributors
are not documented personal reviewers or endorsers of this project.

## 12. Planned impact statements and final narrative

Current supportable contribution paragraph:

> The work gives an exact finite-budget reduction of heterogeneous
> point-trap design to balanced source-mass cells and a scalar budget root.
> Its graph bounds identify reaction, profile and geometry contributions to
> excess lifetime, while the prescribed-strength phase construction addresses
> a separate long-time objective. These results provide design rules and
> analytical benchmarks for localized sequestration in diffusion-dominated
> porous media.

Application paragraph before new simulations:

> We propose using the construction to position carbon-rich treatment bands
> in contaminated porous sediment. At a fixed dose of the same carbon, the
> study will compare sequestration time, contaminant availability, carbon
> utilization and release to overlying water against matched layouts.
> Finite adsorption capacity and desorption will determine how far the
> idealized placement advantage persists.

After execution, replace the proposal with the exact reproduced benchmark,
contaminant, carbon, geometry, dose, metric, uncertainty and measured result.
Do not copy the old 2.86% or 7.96% into this environmental claim.

Close with: specific mathematical contribution; measured environmental
result if available; formal and computational validation; then the
independent-remobilization-clock conjecture and its conditional implication.
Place credits in acknowledgements and source notes. Avoid presenting
credentials as evidence of personal review.

## 13. Submission-format note

This plan follows the user's requested reading structure: title and byline,
no contents, synopsis about 8 pages and detailed paper 15–19 pages.
Portal submission limits and anonymity requirements must be checked
separately before producing a submission-specific copy; an old local
blueprint is not proof of current official requirements.

Official reference links retained for that later check:

- https://irisnationalfair.org/guidelines.html
- https://register.irisnationalfair.org/examples/research-paper
- https://sspcdn.blob.core.windows.net/files/Documents/SEP/ISEF/2027/Rules/Book.pdf
