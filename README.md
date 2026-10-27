# High-chromatic tournament parts

Lean 4 formalization of the construction in **“High-chromatic tournament parts
without a complete pair of cyclic triangles”**, by Guantao Chen, Hein van der
Holst, and Shengze Wang, from the manuscript supplied with this project.

The main result is a **relative formal proof**: it proves the construction and
its chromatic and forbidden-pair properties from two explicit mathematical
inputs, `ErdosInput` and `OctahedralTucker`. It does not prove those inputs.
There are no project declarations of `axiom` and no `sorry` placeholders.
That fact does **not** make the main theorem unconditional: its hypotheses
remain visible arguments of the theorem.

## Main results

All declarations are in the namespace `TournamentParts`.

```lean
#check TournamentParts.main
#check TournamentParts.main_chromaticNumber
#check TournamentParts.not_finitePartsConjecture
```

For every `d : Nat`, including zero, `main` supplies a finite tournament on

```lean
Sum (Binary (Fin N)) (Fin N)
```

whose two summands form a disjoint partition. Both parts have chromatic number
at least `d`, and no cyclic triangle in one part is complete to a cyclic
triangle in the other in either direction. Internally, the construction uses
`D = max d 4`.

`main_chromaticNumber` states the bounds using `tournamentChromaticNumber`,
the least number of transitive color classes. `main` instead uses
`ChromaticAtLeast`, the equivalent assertion that no coloring with fewer
than `d` colors exists. Their equivalence is proved in `Interpretation.lean`.

`not_finitePartsConjecture` refutes the prescribed-parts conjecture for arbitrary
finite vertex types `X` and `Y`, with the partition represented by `Sum X Y`.
These partitioned counterexamples also contradict the manuscript's conjecture
about arbitrary disjoint subsets of a tournament. The project does not encode
a separate ambient vertex set containing additional unused vertices.

## Exact external inputs

### Octahedral Tucker's lemma

`OctahedralTucker` is the following proposition, expressed using finite partial
sign vectors and integer labels:

- For every `N >= 2`, let `label` be an antipodal integer labeling of sign
  vectors of length `N`.
- On every nonzero sign vector its value is one of
  `±1, ..., ±(N - 1)`.
- Then there are nonzero comparable sign vectors `s <= t` with
  `label s = -label t`.

The source definition is in `TournamentParts/Tucker.lean`. A partial sign is
`Option Bool`: `none` is zero, and `some false` / `some true` are negative /
positive. `SignExtends s t` means that all nonzero coordinates of `s` are
retained in `t`. Labels are defined also at the zero vector; antipodality
forces that unused label to be zero. This is a harmless total-function encoding
of the usual statement on nonzero vectors.

The project **proves the paper's application of Tucker's lemma**. In particular,
it constructs antipodally compatible completions, proves their adjacency,
constructs the two-case labeling, checks its range and antipodality, and rules
out the complementary pair supplied by Tucker.

The resulting theorem is
`binary_not_colorable_of_smallBipartite`: if `2 <= g <= N` and every induced
subgraph on fewer than `g` vertices is bipartite, then the binary function graph
has no proper coloring with `k <= g` colors. This is the coloring formulation
of the lower bound `chi(B(G)) >= g + 1` under those hypotheses.

### Erdős graph-existence input

`ErdosInput`, defined in `TournamentParts/Main.lean`, states exactly:

```lean
∀ D : ℕ, 4 ≤ D →
  ∃ N : ℕ, ∃ G : SimpleGraph (Fin N),
    2 * D + 1 ≤ N ∧
    TriangleFree G ∧
    (¬ ∃ c : Fin N → Fin (2 * D), GProper G c) ∧
    SmallBipartite G (2 * D + 1)
```

Here `SmallBipartite G g` means that each vertex set of cardinality less than
`g` admits a proper Boolean coloring of its induced graph. The coloring is
represented by a function on the whole vertex type, with correctness required
only on the selected set.

The classical Erdős theorem with girth greater than `2 * D` and chromatic
number greater than `2 * D` supplies this package mathematically: small induced
subgraphs are forests, hence bipartite; triangles are excluded; and the
chromatic condition implies the vertex-count bound. **Neither Erdős's theorem
nor this reduction from girth to the packaged properties is formalized here.**
The package is assumed explicitly, rather than silently identified with a
library theorem about girth.

## Correspondence with the manuscript

| Source file | Mathematical content |
| --- | --- |
| `Core.lean` | Simple graphs, Boolean binary functions, binary function graph, tournament axioms, cyclic triangles, graph and tournament colorings. |
| `Binary.lean` | Complement adjacency; an explicit six-coloring from a triangle of binary functions; the triangle-free lemma when the base graph has no six-coloring. |
| `Backedge.lean` | Backedge orientation and its tournament axioms; every cyclic triangle contains a graph edge; graph colorings give tournament colorings; a tournament coloring of a triangle-free backedge graph refines to a graph coloring with twice as many colors. |
| `Construction.lean` | The tournament on the disjoint sum; cross arcs read Boolean signs; common sign classes of adjacent functions contain no opposite-part cyclic triangle; exclusion of complete pairs in both directions. |
| `Tucker.lean` | The combinatorial proof of the binary graph's chromatic lower bound from the explicit Tucker input and `SmallBipartite`. |
| `Interpretation.lean` | No monochromatic cyclic triangles is equivalent to transitive color classes; finite colorability; the minimum chromatic number and its lower-bound characterization; restriction along injective vertex maps. |
| `Main.lean` | Assembly of the construction for every natural-number threshold; numerical chromatic statement; refutation of the prescribed-parts conjecture. |

`false` represents `-1`, and `true` represents `+1`. Adjacency of binary
functions is written directly as the impossibility of a graph edge having both
endpoints in either common sign class; this is exactly independence of both
classes. The graph itself is mathlib's `SimpleGraph`.

A tournament is represented by its arc relation and the irreflexivity,
asymmetry, and completeness laws. Cyclic triangles are ordered triples of
arcs; their vertices are automatically distinct by those laws. `CompleteTo`
requires all nine cross arcs. The disjoint-sum representation enforces the
partition without separate membership or disjointness hypotheses.

The absence-of-complete-pairs theorem,
`construction_no_complete_pair`, is unconditional in the base graph and
independent of Tucker and Erdős. Those two inputs are needed to obtain the
arbitrarily large chromatic bounds.

## Deliberate scope boundaries

- The Borsuk–Ulam / geometric alternative proof is not formalized.
- No numerical girth or odd-girth API is introduced. The bridge from odd girth
  to `SmallBipartite`, and the existence of a finite odd cycle in a nonbipartite
  finite graph, remain outside this development.
- The triangle-free factor-two case of the backedge inequality is proved.
  The general upper bound `chi(G) <= omega(G) * chi(T)` is not formalized.
- The Kneser/star proposition inside the manuscript's commented-out block,
  background survey results, and historical conjecture equivalences are not
  formalized.
- The result is existential and uses classical choice; this project is not an
  executable algorithm for efficiently producing the counterexamples.

## Toolchain and build

The portable project pins:

- Lean `4.26.0` (`leanprover/lean4:v4.26.0`).
- mathlib commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

From the project directory, with Lean/Elan and Git installed:

```text
lake update
lake exe cache get
lake build
```

The first two commands fetch the pinned dependencies and their compiled cache.
The final command checks the project. The toolchain file selects the stated
Lean version automatically. Dependency retrieval requires internet access;
a previously populated dependency/cache directory can be reused offline.

To inspect a theorem's type and its kernel-level dependencies, create a local
Lean file containing, for example:

```lean
import TournamentParts

#check TournamentParts.main_chromaticNumber
#print axioms TournamentParts.main_chromaticNumber
#print axioms TournamentParts.not_finitePartsConjecture
#print axioms TournamentParts.construction_no_complete_pair
```

Then run `lake env lean YourCheck.lean`. Ordinary foundational dependencies such
as `Classical.choice`, `propext`, and `Quot.sound` are compatible with this
classical development. The `#print axioms` command does not replace inspection
of theorem parameters: `ErdosInput` and `OctahedralTucker` are hypotheses, so
proving the application does not prove either background principle.

