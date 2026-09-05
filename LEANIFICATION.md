# Leanification Handoff

## Scope

- Root manuscript: `StateDep_MOR.tex`.
- Recursive active input closure: `StateDep_MOR.tex` and `Appendices.tex`.
- Active formal environments: 25.
- Count: 3 assumptions, 5 definitions, 2 remarks, 1 fact, 4
  propositions, 9 lemmas, and 1 theorem.
- Excluded: `prop:smw-resting-state` / `prop:resting-state`, whose entire
  environment is inside the TeX `comment` block at `StateDep_MOR.tex:1351`.
- Also not counted: the percent-commented historical lemma start at
  `StateDep_MOR.tex:1141`.

`StateDepMOR/PaperStatements.lean` is the statement ledger. A
`...Statement` definition only states a proposition; it is not a proof.
The table below names a concrete theorem when one currently exists.

## Source-Fidelity Closure (2026-09-02)

The four source-closure issues from the dedicated fidelity audit have been
repaired under the authorization in `major_issues_v2.tex` and the user's
authorization for directly similar notation, exposition, convention, and
proof-justification repairs:

1. The SMW proof now covers the strengthened
   `0 < L_alpha <= 1` premise. At `L_alpha = 1`, zero-queue derivatives
   vanish at a regular interior time, while SMW flow balance and the uniform
   Hall cut gap force their aggregate derivative to be positive. Thus the
   regular boundary case is impossible.
2. In achievability, `T` is exclusively the fixed target horizon in
   `gamma_AB,T`; `H >= T` is the observation horizon sent to infinity.
   Local data on an `H`-horizon path are restricted and translated to a
   length-`T` FSP. No horizon-invariance assertion is used. The explicit cut
   proof now calculates `gamma_CB` directly.
3. The source states the triangular, initial-state-uniform Poisson-FSP upper
   bound with its compactness and closed-limit hypotheses. It also spells out
   the geometric-block proof for the uniform return expectation and orders
   the limits as `K -> infinity`, then `H -> infinity`, then `rho downarrow 0`
   with `delta = rho/3` and `epsilon = 2 rho/3`.
4. Every active physical system-size index in `StateDep_MOR.tex` and
   `Appendices.tex` is now literally `K`; the rendering-only `N -> K` macro
   was removed. The stopping-time recursion and all `K^2` random-walk
   calculations now use that same bound index.

No Lean definition, statement, or proof was edited in this source-only pass.
The boundary contradiction and fixed-target-horizon localization were already
present in the proved Lean modules; the TeX proof now reads back to those
constructions. Under the user's unconditional audit requirement, the final
audit made only the English-comment substitutions `admit` to `support` in
`AchievabilityReturnFailure.lean` and `AchievabilityFinal.lean`, so the
unconditional forbidden-token scan has no lexical false positives. Every
individual change and its preservation argument is recorded in the dated
section of `SOURCE_REPAIRS.md`.

## Verification Snapshot

Source-closure verification on 2026-09-02:

- `latexmk -g -pdf -interaction=nonstopmode -halt-on-error
  StateDep_MOR.tex` succeeds and produces `StateDep_MOR.pdf` (57 pages).
- The final log has no undefined reference or citation warning. Existing
  overfull/underfull box, font, and included-PDF-version warnings are nonfatal.
- Searches find no active `\N` or `\mathbb N` system-size index and no obsolete
  `gammaAB_technical` or `variational_problem_original` label in the TeX input
  closure.
- The unconditional Lean scan finds no `axiom`, `opaque`, `sorry`, or `admit`.

Lean export audit on 2026-09-02:

- `lake build` succeeds for the current tree (8,780 jobs), including
  `AchievabilityStatement.lean`, `TightConverseProof.lean`,
  `MainAssembly.lean`, `Main.lean`, and the root `StateDepMOR.lean` library.
- A separate direct-elaboration sweep passes all 76 Lean source files,
  including modules outside the root import closure.
- A `#print axioms` audit of all 20 active-claim proof exports and the two
  exact calendar-law bridge exports reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The chronological calendar-law path is split across
  `AchievabilityCalendarBridge.lean`, `AchievabilityCalendarGrid.lean`,
  `AchievabilityCalendarPMF.lean`, `AchievabilityCalendarLaw.lean`,
  `AchievabilityKernelSemigroup.lean`, `AchievabilityBlockEvents.lean`,
  `AchievabilityAssembly.lean`, and finally `AchievabilityStatement.lean`.
  `StateDepMOR.Main` imports `MainAssembly.lean` directly; there is no
  `FinalTheorems.lean` module in the current tree.
- The accidentally appended duplicate calendar-law block was removed; its
  canonical proof is owned by the three split calendar modules named above.
- The dedicated read-only auditor independently compared every active TeX
  environment with its Lean readback and returned **25/25 pass**: no dropped
  quantifier, weakened conclusion, altered topology, changed time scale,
  hidden semantic interface, or undocumented manuscript repair.

Status terms below:

- `Encoded`: a definition or assumption has a concrete typed encoding.
- `Proved`: the named concrete theorem is in a successfully checked module.

## Coverage: 25 Active Environments

| # | Kind and source label | Lean statement or encoding | Concrete theorem and module | Status |
|---:|---|---|---|---|
| 1 | Assumption `asm:connectivity` | `ConnectivityAssumption`, `Network.IsConnected` | `Network.lean` | Encoded |
| 2 | Proposition `prop:NT-is-necessary` | `AmpleFlexibilityNecessaryStatement` | `ampleFlexibilityNecessaryStatement_proved`, `AmpleFlexibility.lean` | Proved |
| 3 | Assumption `asm:non_trivial` | `LimitedFlexibilityAssumption`, `Network.HasLimitedFlexibility` | `Network.lean` | Encoded |
| 4 | Assumption `asm:strict_hall` | `CompleteResourcePoolingAssumption`, `Network.HasCRP` | `Network.lean` | Encoded |
| 5 | Proposition `prop:hall_is_necessary` | `HallNecessaryStatement` | `hallNecessaryStatement_proved`, `HallNecessary.lean` | Proved |
| 6 | Fact `fact:sample_path_ldp` | `SamplePathLDPStatement`, `PoissonSamplePath.ConcreteSamplePathLDPStatement` | `PoissonUpperFinal.concreteSamplePathLDPStatement`, `PoissonSamplePathLDP.lean` | Proved |
| 7 | Definition, SMW | `SMWDefinition`, `Network.IsSMWPolicy` | `Network.smwPolicy_isSMW`, `Policy.lean` | Encoded; canonical policy proved correct |
| 8 | Remark `rem:SMW-converges-to-w` | `SMWConvergesToWRemarkStatement` | `Network.smwConvergesToWRemark_proved`, `SMWConvergenceProof.lean` | Proved |
| 9 | Theorem `thm:main_tight`; alias `thm:main` | `MainTightStatement` | `PaperStatements.mainTightStatement`, `MainAssembly.lean` | Proved |
| 10 | Definition `defn:state_independent` | `FixedGraphStateIndependentPolicy`; concrete `epochLaw`, `transitionPMF`, and `wasteIndicator` | `StateIndependentPrimitives.lean`, `StateIndependentChain.lean` | Encoded with normalized concrete chain |
| 11 | Proposition `prop:state_ind_no_exp` | `StateIndependentNoExponentStatement` | `stateIndependentNoExponent`, `StateIndependentChain.lean` | Proved |
| 12 | Definition `def:FSP` | `FluidModelSolutionDefinition`, `Network.FluidModelSolution` | `FluidModel.lean` | Encoded |
| 13 | Lemma `lem:fms-existence` | `FluidModelExistenceAndConsistencyStatement` | `Network.calendarPoissonExecutionFrom_fluidModelExistenceAndConsistency`, `FluidExistenceProof.lean` | Proved for the concrete calendar Poisson execution |
| 14 | Definition, Fluid limits | `FluidLimitDefinition`, `FluidModelSolution.IsFluidLimit` | `FluidModel.lean`, `FluidConsistency.lean` | Encoded |
| 15 | Definition `defn:lyap_func` | `LyapunovDefinitionStatement`, `Lyapunov.LAlpha`, `Lyapunov.LAlphaAmbient` | `lyapunovDefinitionStatement_proved`, `VerifiedStatements.lean` | Proved |
| 16 | Lemma `lem:key_property_lyap`; alias `lem:lyap-properties` | `KeyLyapunovPropertiesStatement` | `keyLyapunovPropertiesStatement_proved`, `VerifiedStatements.lean` | Proved |
| 17 | Proposition `prop:tight_converse`; alias `prop:sufficient-conditions` | `TightConverseStatement` | `PaperStatements.tightConverseStatement`, `TightConverseProof.lean` | Proved |
| 18 | Lemma `lem:lyapunov_derivative`; alias `lem:smw-steepest` | `Network.LyapunovDerivativeStatement` | `Network.lyapunovDerivativeStatement_proved`, `FluidSMWProofs.lean` | Proved |
| 19 | Lemma `lem:lyapunov_derivative_fluid`; alias `lem:smw-negative-drift` | `Network.SMWNegativeDriftStatement` | `Network.smwNegativeDriftStatement_proved`, `SMWNegativeDriftProofs.lean` | Proved |
| 20 | Lemma `lem:explicit_gamma`; alias `lem:explicit-exponent` | `ExplicitGammaEqualityStatement`, `ExplicitGammaOptimizerStatement` | `explicitGammaEqualityStatement`, `GammaLowerBound.lean`; `explicitGammaOptimizerStatement`, `GammaOptimizer.lean` | Proved |
| 21 | Remark `rem:critical-subset` | `CriticalSubsetRemarkStatement` | `Network.criticalSubsetRemarkStatement_proved`, `CriticalSubsetProof.lean` | Proved |
| 22 | Lemma `lem:point_wise_converse`; alias `lem:converse` | `PointwiseConverseStatement` | `Network.pointwiseConverseStatement`, `ConverseProofs.lean` | Proved |
| 23 | Lemma `lem:tech_lems` | `TechnicalLyapunovLemmaStatement` | `technicalLyapunovLemmaStatement_proved`, `VerifiedStatements.lean` | Proved |
| 24 | Lemma `lem:lower_bound_vj` | `AchievabilityBoundStatement` | `PaperStatements.Network.achievabilityBoundStatement_proved`, `AchievabilityStatement.lean` | Proved |
| 25 | Lemma `lem:fluid_resting_point` | `FluidRestingPointStatement` | `Network.fluidRestingPointStatement`, `FluidRestingProof.lean` | Proved |

## Export Chain And Remaining Verification

1. `PaperStatements.Network.achievabilityBoundStatement_proved` has the exact
   repaired fixed-horizon, non-idling `AchievabilityBoundStatement` type.
2. `PaperStatements.tightConverseStatement` applies that export together with
   `Network.fluidRestingPointStatement` to produce the repaired Proposition 4.
3. `PaperStatements.mainTightStatement` applies the same two unconditional
   components to produce the main theorem, including the quantified
   near-supremum conclusion rather than an unsupported maximizer.
4. `StateDepMOR/Main.lean` imports `MainAssembly.lean`, so the configured root
   names the final main-theorem export directly.
5. The current tree passes both `lake build` and direct elaboration of every
   Lean source file.
6. The independent TeX-to-Lean statement audit passes all 25 active
   environments.

## Source Repair Policy

`SOURCE_REPAIRS.md` is the authoritative ledger. Every manuscript change
must record:

1. the defective source location and claim;
2. the exact replacement;
3. why the replacement preserves the intended result.

Repairs authorized by `major_issues_v2.tex`, including Proposition 3 Part
1, may be made directly. Similar minor notation, convention, exposition,
and proof-justification repairs are allowed. A repair may correct a false
premise, malformed scope, or unsupported auxiliary assertion, but may not
silently weaken the intended conclusion. The repaired TeX and Lean
readback must be checked independently for statement fidelity.

Important applied repairs include the minimum-recurrent-class loss
convention, the ambient extension of `L_alpha`, the repaired Proposition 3
policy scopes, boundary-inclusive negative drift, local forward
directional steepest descent, the non-idling hypothesis in achievability,
and fixed-horizon `gamma_AB,T` without unsupported cross-horizon
invariance. See `SOURCE_REPAIRS.md` for exact changes and preservation
arguments.

## Audit Commands

Run every Lean source, not only the configured import closure:

```bash
lake build
for f in StateDepMOR/*.lean StateDepMOR.lean; do
  lake env lean "$f" || exit 1
done
```

Build the manuscript and inspect its active environment count:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error StateDep_MOR.tex
rg -n '\\begin\{(asm|defn|rem|fact|prop|lem|thm)\}' \
  StateDep_MOR.tex Appendices.tex
```

Scan for forbidden declarations and placeholders:

```bash
rg -n '^[[:space:]]*(axiom|opaque)[[:space:]]|\bsorry\b|\badmit\b' \
  --glob '*.lean' StateDepMOR StateDepMOR.lean
```

For every final paper-facing theorem, add a `#print axioms` command to a
temporary audit file importing its defining module. Example:

```lean
import StateDepMOR.FluidRestingProof
#print axioms StateDepMOR.Network.fluidRestingPointStatement
```

Only standard foundational dependencies such as `propext`,
`Classical.choice`, and `Quot.sound` are acceptable. The final gate is an
independent TeX-to-Lean statement readback for all 25 rows.

## Coverage Ambiguity

The raw TeX search reports 27 environment starts. Exactly two are inactive:
the percent-commented historical lemma and the proposition wholly inside
the TeX `comment` block, giving 25 active environments. No other recursive
input or active formal environment was found. Every active assumption or
definition has a concrete encoding, and every active fact, remark,
proposition, lemma, and theorem has a concrete unconditional export listed
above. The 25-row inventory is independently statement-audited and all of its
proof exports are covered by the clean axiom inventory described above.
