# SAT Solver

## Abstract

This repository is a self-contained study of how the search strategy of a Boolean satisfiability (SAT) solver changes what it
is able to prove, implemented entirely in OCaml over a single shared formula representation. Three solvers are built on that
core: an exhaustive enumeration baseline, a resolution-free recursive DPLL search with unit propagation and pure-literal
elimination, and a conflict-driven clause-learning solver (CDCL) built on a trail with watched literals, first-UIP conflict
analysis, and VSIDS branch selection. The solvers are not merely juxtaposed; the baseline serves as a semantic oracle, and
every search-based solver is validated against it by property-based testing. The study closes with a scaling benchmark whose
methods and raw results are reported in Section 7.

## 1. Introduction

Conjunctive normal form satisfiability is the canonical NP-complete decision problem: given a conjunction of disjunctions over
Boolean variables, decide whether some assignment of truth values satisfies all of them. Its appeal as a teaching object is
unusual, the same problem simultaneously admits a trivial exhaustive solution and requires a genuinely non-trivial engine to
approach even modest instances. That gap is what this repository isolates.

The contribution of the present work is an executable comparison of three points on that spectrum, written against one fixed
data model so that differences in behaviour can be attributed to search strategy rather than to incidental representation. The
repository provides a minimal semantic core (formula model, satisfiability predicate, DIMACS reader); an exhaustive baseline
that doubles as a ground-truth oracle; a DPLL search whose branching and simplification rules are individually observable; a
CDCL engine whose learned clauses, backjump targets, and branch scores are all derived from first principles rather than
delegated to a library; and a property-based evaluation harness that ties the three implementations together, plus a benchmark
generator with reproducible instances. Section 2 fixes the formal problem and the encoding conventions the code implements,
Section 3 the architecture, Section 4 the methodology with one subsection per solver, and Sections 5 to 7 the tooling, the
evaluation design, and the measured results.

## 2. Problem Statement and Encoding Conventions

A **literal** is a non-zero integer (`lib/cnf.ml:1`): the integer `v` denotes the positive variable `x_v`, and `-v` its
negation. Variables are numbered `1` to `n`, `n` being the count declared by the input. A **clause** is a list of literals
disjunctively connected; a **formula** is a list of clauses conjunctively connected.

A **total assignment** is a list of literals, at most one polarity per variable, read as "these variables are true", with the
implicit assumption that the negation of any unlisted variable is false. A clause is satisfied when one of its literals occurs
in the assignment, and a formula is satisfied when all of its clauses are (`lib/cnf.ml:12`, `lib/cnf.ml:15`). Two boundary
cases follow directly and are exercised throughout the suite: the empty clause is unsatisfiable, and the empty formula is
satisfied by every assignment, including the empty one. Three further conventions are observable in solver results rather than
merely in the data model:

- **Zero is not a literal.** In the DIMACS stream `0` terminates a clause. The test suite
  additionally fixes the convention that a `0` appearing inside a clause makes that clause, and
  hence the formula, unsatisfiable.
- **Out-of-range literals are dead.** A literal whose variable exceeds the declared `n` can never be
  true, because no assignment any solver produces mentions it. DPLL removes such literals up front
  (`lib/dpll.ml:5`) and CDCL reuses that same restriction, so a clause left empty by the restriction
  is correctly reported as a conflict.
- **Every solver terminates with a verification.** All three report a model only after
  `Cnf.satisfies` accepts it, and report UNSAT only after the search space is exhausted or a
  level-zero conflict is derived. The satisfiability predicate is thus both the specification and a
  runtime guard.

The decision space over `n` variables has `2^n` elements; the rest of this report is an account of three ways of not visiting all of it.

## 3. System Architecture

The build produces one library, one executable, and one test binary. `lib/dune` declares a single library named
`sat_solver_lib`; because it does not disable wrapping, every module is reached through the `Sat_solver_lib` namespace, which
both `bin/main.ml` and `test/test_sat_solver.ml` open.

| Module | Role | Exposed interface |
| --- | --- | --- |
| `Cnf` | Formula model and satisfiability | `literal`, `clause`, `formula`, `satisfies`, `has_empty_clause`, `clause_satisfied`, `num_clauses` |
| `Dimacs` | Input parsing | `parse_file`, `Parse_error` |
| `Assignment` | Fixed-size tri-state value array | `create`, `value_of`, `set`, `unset`, `is_fully_assigned` |
| `Bruteforce` | Exhaustive baseline and oracle | `all_assignments`, `solve` |
| `Dpll` | Recursive DPLL search | `restrict`, `simplify`, `unit_propagate`, `find_unit_clause`, `find_pure_literal`, `solve` |
| `Trail` | Assignment stack with reasons and levels | `push_decision`, `push_propagated`, `value`, `undo_to_level`, `entry_of` |
| `Watch_list` | Clause database with two watches per clause | `add`, `watched_by`, `watched`, `move_watch`, `to_clause` |
| `Conflict_analysis` | Resolution and first-UIP derivation | `resolve`, `analyze` |
| `Vsids` | Variable activity heuristic | `bump`, `decay_all`, `best_unassigned` |
| `Cdcl` | Clause-learning solver | `inspect`, `propagate`, `normalize_clause`, `solve` |

Dependencies flow strictly downward. `Cnf` and `Dimacs` are leaves; `Bruteforce` and `Dpll` depend only on `Cnf`; `Cdcl`
depends on `Cnf`, on `Dpll` for restriction, and on the four infrastructure modules `Trail`, `Watch_list`,
`Conflict_analysis`, and `Vsids`, which are connected to each other only through `Trail` and `Cnf`.

Two representation strategies coexist. The baseline and DPLL are pure: formulas and assignments are immutable values, and a
search step consumes one and returns another. The CDCL engine is incremental: a single `solve` call drives one long-lived
mutable object, with the trail as a stack plus an array index, all clauses in one growable array, and heuristic scores in a
float array. `Assignment` is a third, smaller abstraction, a tri-state array with an `is_fully_assigned` query, from the
encoding stage of development; the CDCL engine does not consult it, and the trail's `entry_of` plays the role of its
`value_of`.

## 4. Methodology

### 4.1 Exhaustive enumeration

`Bruteforce.all_assignments` (`lib/bruteforce.ml:3`) constructs the space of total assignments by recursion: the base case is
the single empty assignment, and each step duplicates the smaller space with `n` prepended positively and negatively. `solve`
(`lib/bruteforce.ml:9`) returns the first assignment accepted by `Cnf.satisfies`, or `Unsat` if the enumeration is exhausted.

The method is deliberately unsophisticated, which is exactly its value: being a direct transcription of the definition of
satisfiability, it needs no invariant and no correctness argument beyond `Cnf.satisfies` itself, which makes it the natural
differential oracle for the other two solvers. Its cost profile is also the quantitative baseline for the report, the candidate
list is materialised in full before a single clause is examined, so one `solve` call on `n` variables costs `O(2^n · n)` time
and memory, independent of the formula.

### 4.2 DPLL

The DPLL search (`lib/dpll.ml:44`) carries the state pair *(assignment, residual formula)* and reduces the formula rather than
reasoning about the original one. Each node is processed in a fixed order:

1. **Restriction.** Literals outside `1..n` are dropped once, before the search (`lib/dpll.ml:5`).
2. **Unit propagation.** `unit_propagate` (`lib/dpll.ml:20`) alternates two steps: `simplify` removes
   clauses already satisfied by the assignment and strips the assigned literals from the rest, then
   `find_unit_clause` looks for a clause of length one. A unit clause `(l)` forces `l`, which is
   prepended to the assignment and the loop repeats, so propagation runs to a fixpoint before any
   decision is taken.
3. **Termination tests.** An empty clause in the residual formula refutes the branch; an empty
   formula closes the branch, and the current assignment is complete.
4. **Pure literal.** `find_pure_literal` (`lib/dpll.ml:27`) scans the residual literals for one whose
   complement does not occur and assigns it, removing an arbitrary number of clauses without branching.
5. **Branching.** `pick_variable` selects the lowest unassigned variable in `1..n`. The search
   recurses on `+v` and, only on failure, on `-v`; failure is the absence of a result, so backtracking
   is implicit in the OCaml call stack rather than managed by an explicit trail.

`solve` (`lib/dpll.ml:62`) does not return the first `Some` it receives. It re-checks the recovered assignment against the
*original*, unrestricted formula before declaring satisfiability, so the reported model is verified independently of the
simplifier.

### 4.3 CDCL

The clause-learning solver is composed of four cooperating structures and one control loop:

```
imply units of the input at level 0
loop:
  propagate the pending queue   -> conflict?  learn, backjump, re-propagate
  pick a variable by activity   -> none left?  verify the model, return Sat
  push it as a decision and continue
```

**The trail** (`lib/trail.ml:3`) stores an entry per assigned variable holding the literal, the decision level at which it was
assigned, a monotone position counter, and a *reason*: a decision, or a clause from which the literal was propagated. The
position counter makes the trail totally ordered, and that order is the backbone of conflict analysis. Reads are constant
time: `value l` answers `Some true` if the stored literal is `l`, `Some false` if it is `-l`, and `None` if the variable is
unassigned. `undo_to_level` (`lib/trail.ml:44`) partitions the stack by level, clears the array slots of the dropped entries,
and restores the level counter, so backtracking is a single non-recursive operation with no reallocation of the trail itself.

**Watched literals** (`lib/watch_list.ml`). Every clause is stored exactly once in a growable array, with two literals per
clause marked as watches in mutable fields. A bucket array of size `2n+1` indexed by `lit + n` (`lib/watch_list.ml:16`) maps a
literal to the clauses watching it, so a clause is examined only when one of its two watched literals becomes false. Unit
clauses use `w2 = 0` as a sentinel meaning "one watch only" (`lib/watch_list.ml:31`), and `move_watch` relocates a single
watch in constant time, updating the clause record and both bucket lists.

**Propagation** (`lib/cdcl.ml:30`). The queue holds literals pending assignment, seeded with level-zero units and with
decisions as they are made. For each dequeued literal `p` the falsified literal is `-p`, and every clause watching `-p` is
classified by `inspect` (`lib/cdcl.ml:5`) into exactly one of four outcomes:

| Outcome | Condition | Action |
| --- | --- | --- |
| `Skipped` | the other watch is true | nothing; the clause is satisfied |
| `Rewatched` | the other watch is false but some other literal is not false | move that watch onto the live literal |
| `Implies other` | the other watch is unassigned and no alternative exists | push `other` with this clause as reason, enqueue it |
| `Falsified` | no literal in the clause can be true | record this clause as the conflict |

The first three cases are local and enqueue nothing unless a new literal was implied; the fourth stops the sweep, so
propagation halts at the first conflict. That `Rewatched` and `Implies` are distinguished is what allows a watch to move
*before* an implication is committed.

**Conflict analysis** (`lib/conflict_analysis.ml`). Given the falsified clause, `first_uip` (`lib/conflict_analysis.ml:23`)
repeatedly resolves: it collects the literals of the working clause sitting at the current decision level, and while more than
one remains, takes the one with the greatest trail position, the most recently assigned, hence the one whose reason is
available, and resolves it away against that reason clause. A current-level literal without a reason would be a decision,
which the code signals as an error, since a decision cannot be resolved. The loop stops when at most one current-level literal
survives; that literal is negated in the working clause, so the clause returned is the negation of the first unique
implication point and is a non-tautological consequence of the original formula.

`analyze` then orders the learned clause and computes the backjump target: the clause is sorted by *descending* decision
level, and the backjump level is the maximum level among its literals below the current one, `0` when the learned clause is a
unit. Because the highest-level literal sorts first and `Watch_list.add` designates the first two literals of its input as the
watches, the asserting literal is always watched in the learned clause, and the backjump is sound by construction: after
`undo_to_level backjump_level` the asserting literal is unassigned and every other literal of the learned clause is true, so
re-propagating it is forced. The engine relies on exactly this when it inspects the learned clause for unassigned literals,
pushes the unique one if it is unit, and resumes the loop with the fresh propagation queue.

**Branch selection** (`lib/vsids.ml`). Variables carry a float activity, incremented by `1/0.95` for every literal appearing
in a learned clause and multiplied by `0.95` after each conflict, so recent conflicts dominate older ones geometrically.
`best_unassigned` returns the unassigned variable of maximum activity by linear scan, and the engine always decides the
positive polarity of it. The heuristic therefore selects *where* to branch but not *which way*; and since nothing in the
pipeline consults a random source, a given input produces exactly the same search, the same learned clauses, and the same
model on every run.

**Control flow.** Unit clauses in the input are asserted at level zero before the loop begins (`lib/cdcl.ml:69`), because they
are logically forced. A conflict detected while the level is zero is a refutation of the original formula and ends the search
immediately (`lib/cdcl.ml:91`); every other conflict produces a learned clause, a bump-and-decay cycle on the activities, and
a backjump. When propagation drains its queue and no unassigned variable remains, the trail is read out as a model and handed
to `Cnf.satisfies` against the original formula before being reported as `Sat` (`lib/cdcl.ml:115`).

## 5. Implementation and Tooling

**Build.** `dune-project` declares a single package built by dune 3.24; `lib/dune` declares the library,
`bin/dune` an executable published as `sat-solver`, and `test/dune` a test stanza depending on `sat_solver_lib`
and `qcheck`, with `fixtures` added as a source dependency so the DIMACS fixture is staged beside the test binary. The toolchain used for the measurements in Section 7 is OCaml 5.2.0, dune 3.24.2, and QCheck
0.91; the library itself has no third-party dependencies.

**Input.** `Dimacs.parse_file` (`lib/dimacs.ml:10`) is a single line-oriented pass. Empty lines and lines beginning with `c`
are skipped; a line beginning with `p` is matched against `p cnf <n> <m>` and anything else raises `Parse_error`; every other
line is split on spaces and its tokens folded into an accumulating clause, which is flushed into the formula each time a `0`
is seen. Because the flush is triggered by the terminator rather than by the line break, clauses may span any number of lines,
and the `m` of the header does not bound parsing.

**Benchmark harness.** `bin/main.ml` builds its instances programmatically so the experiment is reproducible without external
data. `unsat_formula n` (`bin/main.ml:3`) emits, for each variable pair `(2k+1, 2k+2)`, the four clauses that together forbid
all four value combinations of the pair; the result is unsatisfiable for any `n >= 2` and contains `2n` clauses. `sat_formula
n` (`bin/main.ml:8`) emits three of those four clauses per pair, leaving exactly one of the two polarities free per pair. The
harness measures each solve with `Sys.time`, which reports processor time at microsecond precision on this platform, and
prints the result with `%.6f`; for the satisfiable case it also prints the recovered model together with an independent
re-verification against the input.

## 6. Evaluation Methodology

Correctness evidence is gathered in four tiers, ordered so that each tier constrains the assumptions of the next.

**Tier 1: structural tests.** The incremental machinery is tested directly against the invariants the rest of the engine
relies on: that `undo_to_level` clears both the stack and the index array; that a watch move updates the clause record,
deregisters the old bucket, and registers the new one; that conflict analysis reduces a three-level trail to a unit asserting
clause with backjump level zero; and that the DIMACS reader recovers the declared variable count and the exact clause
structure of the fixture.

**Tier 2: property-based differential testing.** QCheck generates random formulas over small variable ranges with literals
drawn from a signed range, discarding those containing `0`, and checks the properties that must hold for any correct solver.
The central one is *differential agreement*: DPLL and CDCL must return the same satisfiability verdict as the exhaustive
oracle for the same input, over 100 generated instances per run. Two further properties are model validity (every `Sat` answer
satisfies the original formula) and propagation soundness (unit propagation never assigns a variable twice); two more target
the core module directly (empty-clause detection, and the clause-count identity). Shrinking is available, so a failing
instance is reduced automatically to a minimal counterexample.

**Tier 3: fixed instances.** Instances chosen for structure rather than randomness: the three-pigeons-into-two-holes
encoding, unsatisfiable and a standing test of heuristic quality; a conflict at decision level zero; and a family of
degenerate inputs, zero variables with a literal, an empty clause among non-empty ones, the empty formula, and a formula
containing `0`, where the dead-literal and zero conventions must be honoured, and where the agreement of all three
solvers is itself the assertion.

**Tier 4: scaling benchmark.** The generated families of Section 5, solved with CDCL over a range of sizes, with the
satisfiable case re-verified. Individual solves complete in microseconds, which is measurable at the microsecond precision the
harness reports but leaves a single sample exposed to noise; the benchmark is therefore repeated and reported as a range, and
cross-checked at the process level against a trivial OCaml native binary, the difference bounding the solving cost from above.

## 7. Results

### 7.1 Test suite

A full `dune runtest` run reports `success (ran 16 tests)`, 610 generated cases, six property-based properties at 100 cases
each plus ten single-case tests, all passing, in 2.37 s and 2.67 s across two consecutive runs.

| Property-based test | Cases | Result |
| --- | ---: | --- |
| formula with `[]` clause is detected | 100 | pass |
| `num_clauses` matches `List.length` | 100 | pass |
| `unit_propagate` assigns each variable once | 100 | pass |
| DPLL agrees with brute force on small formulas | 100 | pass |
| CDCL agrees with brute force on small formulas | 100 | pass |
| CDCL's model satisfies every clause | 100 | pass |

The ten single-case tests cover the DIMACS fixture; `Unsat` for a contradictory pair; the dead-literal and `0`-in-clause
conventions; a CDCL conflict at level zero; the degenerate-input family of Tier 3, cross-checked against DPLL; the pigeonhole
refutation; trail undo; the asserting-clause analysis; and watch registration, movement, and clause readback.

The two differential properties are the load-bearing results: over the 100 generated instances of each run, DPLL and CDCL never
disagreed with exhaustive enumeration on satisfiability, and no model returned by CDCL failed independent verification. The
pigeonhole instance is refuted by both search solvers, and the level-zero conflict terminates the CDCL search as required.

### 7.2 Benchmark

The harness output, in full:

```
n= 4  result=UNSAT  time=0.000011s
n= 8  result=UNSAT  time=0.000005s
n=12  result=UNSAT  time=0.000008s
n=16  result=UNSAT  time=0.000009s
n=20  result=UNSAT  time=0.000010s
n=24  result=UNSAT  time=0.000012s

n=12  result=SAT  time=0.000020s
model=-3 4 -7 8 -11 12 1 -2 5 -6 9 -10
verified=true
```

Every instance is decided correctly, and the satisfiable instance yields a complete model over all twelve variables, printed
in trail order rather than variable order, which the harness's independent check confirms. Repeated executions return the
identical verdict and model; only the timing digits vary. Because a single measurement at this scale is noise-sensitive, the
harness was run eight times per size:

| Instance | min | max | mean |
| --- | ---: | ---: | ---: |
| UNSAT `n = 4` | 8 µs | 18 µs | 11.4 µs |
| UNSAT `n = 8` | 5 µs | 15 µs | 7.6 µs |
| UNSAT `n = 12` | 7 µs | 15 µs | 10.0 µs |
| UNSAT `n = 16` | 9 µs | 14 µs | 10.6 µs |
| UNSAT `n = 20` | 10 µs | 16 µs | 12.1 µs |
| UNSAT `n = 24` | 12 µs | 22 µs | 15.9 µs |
| SAT `n = 12` | 18 µs | 104 µs | 40.9 µs |

The means of the six unsatisfiable sizes sum to 67.6 µs and the satisfiable instance averages 40.9 µs, so about 109 µs of
solver time elapse per benchmark run. That figure is cross-checked against the process level: the whole benchmark was executed
2000 times and compared against 2000 executions of a trivial OCaml native binary.

| Measurement | Runs | Total wall time | Per execution |
| --- | ---: | ---: | ---: |
| Benchmark binary (7 CDCL solves) | 2000 | 1814 ms, 1839 ms | 907 µs, 919 µs |
| Empty OCaml native binary | 2000 | 1305 ms, 1331 ms | 652 µs, 665 µs |
| Difference, process level | 2000 | — | ≈ 255 µs |

The two agree in order of magnitude and bracket the truth: the ≈109 µs of directly timed solving is the tighter figure, and the
≈255 µs process-level residual is an upper bound, because subtracting an empty binary does not remove the costs the benchmark
binary alone pays, linking the solver library, first-touch page faults on a larger heap, and initial allocator and
garbage-collector setup.

### 7.3 Discussion

The per-instance figures are the informative ones, and the contrast they draw is sharp. Six unsatisfiable instances of
increasing size, the largest over 24 variables, are refuted in 8 to 16 microseconds each. The exhaustive baseline, given the
same largest instance, would have to construct and test `2^24 ≈ 1.68 × 10^7` candidate assignments before returning the same
verdict. The separation between the two is not a constant factor: it is the entire point of the progression the repository
documents, since each stage removes a structurally different part of the search space, enumeration by propagation,
propagation by the pure-literal rule, and chronological backtracking by clause learning that forbids whole subtrees at once.

The measurements also characterise the benchmark itself, which bounds what can be concluded from them. The means are not
monotone across the small sizes, `n = 8` is faster than `n = 4`, because the family is a disjoint union of structurally
identical per-pair contradictions, so a solve is dominated by fixed per-instance costs: the clause store, the `2n+1` watch
buckets, and the activity array; the slope from `n = 12` to `n = 24`, 10.0 to 15.9 µs, is the linear term. The satisfiable
instance costs roughly four times an unsatisfiable one of the same size, because it must decide all twelve variables and
drive the trail to a complete assignment rather than refute each pair in isolation. Since no pair interacts with any other,
no conflict ever requires a learned clause, so the curve measures the fixed cost of running the engine, not the value of
what it learned.

## 8. Conclusion

Three solvers, one formula model, one suite. The exhaustive baseline supplies both a performance reference and a semantic
oracle; DPLL shows what a search with sound simplification and implicit backtracking achieves unaided; CDCL shows the effect
of turning each conflict into a permanent, level-indexed constraint and a non-chronological backjump. The shared verification
path makes the comparison honest: no solver is trusted on its own report, and every model is checked against the input
formula by the predicate that defines the problem.

## Appendix: Reproduction

```sh
dune build                              # build library, executable and tests
dune runtest                            # 16 QCheck tests, 610 generated cases
dune exec ./bin/main.exe                # scaling benchmark and verified model
```

The test suite is staged with `test/fixtures/small.cnf` as a source-tree dependency and must be invoked through dune, since
the fixture path is resolved relative to the test binary's working directory, and QCheck prints a random seed per run,
so a failing property is reproducible.
