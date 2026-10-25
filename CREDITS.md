# References and credits

[Back to the library overview](README.md).

## References

- The fixed-vector construction generalizes Mathlib's `Representation.invariants`,
  formalized by Antoine Labelle, and reuses its intertwining-map API by Stepan Nesterov
  and Edison Xie and its `LinearMap.codRestrict` API in a file by Mario Carneiro.
  Left exactness uses `LinearMap.exact_iff` from Mathlib's exactness API by Antoine
  Chambert-Loir, together with its kernel and range membership APIs.

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3, discussion
  of automorphisms of `G`-sets, motivates the centralizer identification for
  permutation actions. The categorical theorem generalizes this setting;
  it is not attributed to May as a statement for arbitrary categories.
  The construction reuses Mathlib's bundled `Action`, `ρAut`, `mkIso`,
  forgetful `mapAut`, and stock `CategoryTheory.Aut.mulEquivPerm`, together
  with its subgroup equivalence transports.

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 3, §4,
  first lemma, p. 24, for the transitive-action normalizer quotient.
  The parameterization uses inverse right translation for ordinary composition.
  Mathlib's bundled action automorphisms, right normalizer action on cosets,
  coset-to-orbit map and finite-normal endomorphism construction provide the
  existing interfaces; no replacement equivariant-permutation structure is used.

- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 4, §5,
  first theorem, printed page 37, for the finite-index free-group rank formula.
  The free-group modules reuse Mathlib's free bases and Nielsen–Schreier theorem,
  formalized by David Wärn, Eric Wieser and Joachim Breitner, and its group rank
  and Schreier finite-generation API, formalized by Thomas Browning.
- J. P. May, *A Concise Course in Algebraic Topology*, Chapter 4, Problem 1,
  p. 38, for the two-generator free-group application. The character construction
  uses Mathlib's quotient-group and prime-cardinality equivalences; the explicit
  spanning argument uses its Schreier generators for a right transversal.
- J. S. Milne, *Abelian Varieties*, version 2.0 (2008), I.10, Remark 10.7,
  for the complex-torus torsion application. The quotient-kernel comparison uses
  Mathlib's first isomorphism theorem, kernel/range identities and subgroup/quotient
  equivalence transports. Joël Riou's Snake-lemma formalization supplied the
  scalar comparison's original homological proof and positive-sign equation.
- Van Dantzig's compact-open subgroup theorem, used in Neukirch, Schmidt,
  and Wingberg, *Cohomology of Number Fields*, corrected second edition,
  Chapter I, §1, Proposition (1.1.9), for the identity-component discussion.
- The coset-map universal property reuses Mathlib's coset and orbit–stabilizer
  constructions by Chris Hughes, Thomas Browning and Yury Kudryashov, and its
  equivariant-map API by Kenny Lau and Antoine Chambert-Loir. Its clients use
  Yaël Dillies's option actions and Kenny Lau's one-point action instances.
  The existence criterion for maps between cosets combines this universal property
  with Mathlib's conjugated-stabilizer formula.
  Maps between nested coset spaces reuse `Subgroup.quotientMapOfLE` and generalize
  the finite-coset morphism in `Mathlib.CategoryTheory.Action.Concrete`.
- The invariant-relation correspondence reuses Antoine Chambert-Loir's Mathlib
  block classification `MulAction.block_stabilizerOrderIso` and the partition
  API `Setoid.mkClasses` / `Setoid.Partition.orderIso`, in a Mathlib file by
  Amelia Livingston, Bryan Gin-ge Chen, Patrick Massot, Wen Yang and Johan Commelin.
  The block classification cites Helmut Wielandt, *Finite Permutation Groups*,
  translated by R. Bercov, Academic Press, 1964, Theorem 7.5; this bibliographic
  reference is taken from Mathlib.
- The product-coset orbit equivalence reuses Mathlib's double-coset quotient,
  left-coset and orbit quotient APIs, and componentwise product action; the
  [module references](GroupTheory/GroupAction/DoubleCoset.lean) credit their authors.
- Mathlib's `OpenSubgroup` and `MulAction.stabilizer` supply the algebraic interface;
  its compact-neighborhood and clopen-basis results supply the topological inputs.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, electronic version 2.3, Chapter I, §1, (1.1.9)(i) and its
  preceding paragraph. The continuous universal property here is an
  interpretation that does not require the source's local compactness assumption.
- Mathlib's `Subgroup.connectedComponentOfOne`, `QuotientGroup.lift` and
  closed-normal quotient topology supply the component and quotient APIs.
- Mathlib's clopen basis for compact Hausdorff totally disconnected spaces
  and open-quotient basis transport supply the generic open-quotient proof.
- Neukirch, Schmidt and Wingberg, *Cohomology of Number Fields*, corrected
  second edition, Chapter I, §1, remarks following Theorem (1.1.11), motivate
  the compact totally disconnected character case; the open-kernel API applies
  more generally. Mathlib's `NonarchimedeanGroup`, locally constant functions
  and quotient-group interfaces supply the reusable proof ingredients.

- Formal Frontier Agents, *Continuous Group Cohomology*, compact/discrete
  continuous-map discreteness and compact-group factorization formalizations.
  The proofs use Mathlib's compact-open subbasic sets, compactness of fibers,
  clopen identity neighborhoods and continuous quotient elimination.
- Mathlib's canonical arbitrary-subgroup left-coset quotient and coinduced topology,
  `eq_class_eq_leftCoset`, `preimage_mk_one`, `IsOpen.smul`, `IsClosed.smul`,
  finite-T1 discreteness, compact-discrete finiteness and the finite-index API
  supply the subgroup arguments. The statements generalize the hypotheses of
  `QuotientGroup.discreteTopology_iff`, `QuotientGroup.t1Space_iff`,
  `Subgroup.quotient_finite_of_isOpen`, `Subgroup.isClosed_of_isOpen` and
  `Subgroup.isOpen_of_isClosed_of_finiteIndex`. No new quotient or action
  construction is introduced.
- Mathlib's Grothendieck completion and universal-property formalization by
  Alex J. Best and Yaël Dillies supplies the carrier, additive group, generator
  and additive lift. The ring structures and multiplicative lifts compose the
  biadditive extension and generator-extensionality APIs with Mathlib's bundled
  multiplication in `Mathlib.Algebra.Ring.Basic`, by
  Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov and
  Neil Strickland.
- Mathlib's finite-supported product neighborhoods, finite intersections of
  open subgroups and products of open quotient maps supply the finite-coordinate
  extension. The cylinder argument uses Monica Omar's product-membership API,
  in particular `Submonoid.pi_mem_of_mulSingle_mem_aux`.

**Credit and license.** Formal Frontier AI agents developed the Lean proofs and
clients. The continuous sections API builds on Mathlib's sections definitions.
The compact-open subgroup result is the classical van Dantzig theorem, used as
a prerequisite in Neukirch, Schmidt, and Wingberg's *Cohomology of Number
Fields*, Chapter I, §1. Its translation-stabilizer argument independently
assembles Mathlib's compact-neighborhood, clopen-basis and subgroup APIs.
The generic open-quotient proof was first formalized in Formal Frontier's
Profinite Groups library and uses Mathlib's clopen and basis APIs.
The compact/discrete continuous-map and factorization proofs were first formalized
by Formal Frontier Agents in the Continuous Group Cohomology library; their
proofs and public declarations are preserved here, using Mathlib's compact-open
and clopen-neighborhood APIs.
The identity-component quotient API interprets Neukirch--Schmidt--Wingberg's
totally disconnected quotient and reuses Mathlib's component and quotient APIs.
The open-kernel and finite-image arguments generalize their character case
using Mathlib's nonarchimedean, locally constant and quotient APIs; this does
not assert a comparison with all abstract characters.
The rational-circle inclusion and torsion-value lift follow the Formal Frontier
Supernatural Numbers formalization of circle-valued characters.
Formal Frontier Agents supplied the FG scalar mathematical argument and
determinant-route advice. This work is credited to **Authors: Formal Frontier Agents**
and licensed under [Apache-2.0](LICENSE).
