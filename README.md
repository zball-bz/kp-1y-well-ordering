# 1-Y well-ordering in KPω + "an uncountable ordinal exists" — Lean formalization

This repository is a complete Lean 4 formalization of the main theorem of
[*A Short Proof of 1-Y Well-Ordering in KP with ω₁*](docs/1Y-Well-Ordering-KP-Simplified.pdf)
(text: [`paper.txt`](paper.txt); shared by its author test_alpha0, all rights reserved to the author — see
[License](#license)). The theorem is proved **inside the object theory**: the final
result is a Hilbert-style derivation, in the pure ∈ language, from the axioms of KPω.

```lean
-- KP1Y/OneYMainTheorem.lean
theorem KP1Y.OneYTheorem.theorem1_derivable : KP1Y.Derives mainSentence
-- 'KP1Y.OneYTheorem.theorem1_derivable' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## What is proved

`KP1Y.theory` (`KP1Y/Axioms.lean`) is exactly KPω: Extensionality, Empty Set, Pairing, Union,
Infinity, Δ₀-Separation, Δ₀-Collection and the full set-induction scheme. `KP1Y.Derives` is
derivability in the Hilbert calculus of the bundled first-order logic library.

`mainSentence` (`KP1Y/OneYTheoremSentence.lean`) is a closed pure-∈ sentence. `mainSentence_iff`
proves that in every model of KPω it means exactly `MainSemantic`:

* the auxiliary sets (ω, the legal expressions E, arithmetic tables, the expansion graph
  E × ω → E, …) exist, defined by explicit formulas; and for every such choice,
* for every uncountable ordinal ν (no set function maps ω onto ν):
  * there are an ordinal χ ≤ ν and a set function μ : E → χ with μ(∅) = 0 and
    μ(E_N(s)) < μ(s) for every nonempty s ∈ E and every N ∈ ω of the model;
  * ≺ (t ≺ s iff t ≠ s and t = E_N(s) for some N) is well-founded on E, and every set-coded
    expansion trajectory reaches ∅;
  * lexicographic order (a proper prefix is smaller) well-orders each Desc(s) and the standard part
    G = descendants of the seeds (1, m), m ≥ 2. No well-ordering of all of E is claimed (E itself is
    not well-ordered lexicographically: (1,2) > (1,1,2) > (1,1,1,2) > …).

E is the set of internal finite sequences of positive naturals beginning with 1, plus ∅; E_N is the
inherited-ancestry 1-Y expansion with N extra copies (E_0 deletes the last entry, E_N(∅) = ∅). All
lengths and N range over the model's own ω; nothing assumes ω is standard or that membership is
well-founded in the metatheory.

Equivalently: KPω + "an uncountable ordinal exists" proves that the standard part of 1-Y is
well-ordered lexicographically, and in fact gives an ordinal-valued ranking of all legal expressions.

## How the proof is organized

The proof follows the paper. All finite combinatorics of the 1-Y algorithm is re-proved inside
arbitrary KPω models (no host-Lean theorem is used as an object axiom). Main stages:

| Paper | Content | Key modules |
|---|---|---|
| §2, Lemma 4 | the single relation table R with reflection clause FR | `Reflection*.lean` |
| §3, Lemmas 5–6, Cor. 7 | satisfaction, Skolem closure, elementary heights, reflection (7)/(8), initial representations | `Satisfaction*`, `Skolem*`, `ReflectionHeight*`, … |
| §1, Lemma 3 | finite copying descent: block splicing by reflection for all internal N | `OneYCopySeams*`, `OneYCopyDescent` |
| Lemma 3 (cited [1]) | canonical reconstruction: re-extracting E_N(s) recovers the copied tower | `OneYTowerCanon*`, `OneYLower*`, `OneYTerminal*`, `OneYCanonHelper*`, `OneYCanonicalExpansion` |
| §4 | the rank μ, its descent | `OneYMinimumRank`, `OneYRankDescent` |
| §4 | removing V = L: construct μ in L, transfer the actual set | `Constructible*`, `OneYInnerAbsoluteness*`, `OneYRankTransfer` |
| §4 | well-foundedness, termination, lexicographic facts, seeds | `OneYWellFounded`, `OneYWellOrdering`, `OneYExpansionOrder*`, `OneYSeeds` |
| — | closed sentence and derivation | `OneYTheorem*`, `OneYMainAssembly*`, `OneYMainTheorem` |

566 modules, about 89,000 lines. The finite 1-Y algorithm and its host-Lean proofs were taken from
[Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) as a
blueprint and ported to the object theory.

## Building and checking

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain `leanprover/lean4:v4.33.1`
is pinned in `lean-toolchain`), git, Python 3.

```bash
scripts/fetch-yesmetazfc.sh        # fetch the pinned first-order logic / set theory library (see below)
lake build                         # builds YesMetaZFC (as needed) and all KP1Y modules
python3 audit.py                   # #print axioms on the 4,216 declarations listed in Audit.lean
```

`audit.py` fails unless every listed declaration depends only on `propext`, `Classical.choice`
and `Quot.sound` (Lean's own axioms; they are metatheory, not axioms of the object theory).
`./check-module.sh KP1Y/Name.lean [--emit]` checks a single module and
`python3 verify-local-stage.py --root KP1Y` re-checks the whole import closure with
`autoImplicit=false`, reusing results by source fingerprint.

## Dependency: YesMetaZFC

The first-order syntax, Hilbert calculus, completeness theorem and set-theoretic structures come from
YesMetaZFC as pinned in
[EgoFakeFantasy/BMS-Well-Ordering-Lean@bae7e3d](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean/tree/bae7e3d741f24a56d80da9b99c1345562cd10c2d)
(crediting [lanxinge/YesMetaZFC](https://github.com/lanxinge/YesMetaZFC)). That snapshot contains no
license file, so it is **not** included here; `scripts/fetch-yesmetazfc.sh` clones the pinned commit
into `third_party/YesMetaZFC` and applies the one local change recorded in
[`third_party-provenance.json`](third_party-provenance.json): in
`YesMetaZFC/SetTheory/Notation/Surface.lean`, `by native_decide` is replaced by the kernel-checked
`by decide_cbv`. The script verifies the SHA-256 of that file before and after the change.

## Verification records and trust base

* [`tracker/FINAL-VERIFICATION.md`](tracker/FINAL-VERIFICATION.md): final check — a cold re-check of
  all 567 modules (`final-cold-stage.log`) and the axiom audit (`final-audit.log`,
  `audit-results.json`).
* [`tracker/FINAL-STATEMENT-REVIEW.md`](tracker/FINAL-STATEMENT-REVIEW.md): human review that the
  Lean sentence and the Lean algorithm match Theorem 1 and the original 1-Y algorithm.
* [`tracker/review/COPY-TOWER-FIDELITY.md`](tracker/review/COPY-TOWER-FIDELITY.md): independent
  review of the copy construction, with a differential test against the original JavaScript engine
  (`tracker/review/kpsim.py`; 223,952 cases, 0 mismatches).

What the machine check does **not** cover: that `MainSemantic` and the Lean definitions of the
algorithm faithfully express the paper's Theorem 1 (this is the human review above), and the
correctness of the YesMetaZFC logic library itself beyond Lean's kernel check.

Most project-management documents (`tracker/`, `GOAL.md`, `STATUS.md`, …) are in Chinese; they record
the task plan, per-stage evidence and hand-off notes of the development.

## License

The formalization, scripts and documentation in this repository are released under the
[MIT License](LICENSE), with the exceptions below (details in [`NOTICE`](NOTICE)):

* **The paper is not covered.** `docs/1Y-Well-Ordering-KP-Simplified.pdf` and `paper.txt` were shared
  by their author, test_alpha0 (the actual prover), in a public instant-messaging group without any explicit
  license. They are included only as the reference for the formalized statement; all rights belong
  to the original author, test_alpha0.
* **Ported material keeps its attribution.** The 1-Y algorithm and the structure of the finite proofs
  were ported, with modifications, from
  [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean), which is
  licensed under Apache-2.0 ([copy](LICENSES/Apache-2.0.txt)); its terms continue to apply to the
  derived portions.
* **YesMetaZFC is not included** and is not covered; the pinned upstream snapshot has no license file.
