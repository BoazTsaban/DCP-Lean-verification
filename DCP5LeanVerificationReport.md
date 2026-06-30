# DCP5 Lean Verification Report

Date: 2026-06-21

Source paper: `DCP5.tex`

Lean artifact: `DCP5Verification.lean`

Lean version used: Lean 4.31.0

## Scope

The workspace does not contain a Lean/mathlib project, and core Lean does not
include braid groups or even the usual algebraic hierarchy.  I therefore made a
self-contained Lean verification kernel for the local logical, group-theoretic,
combinatorial, and integer-arithmetic parts of the proof.  Braid-theoretic and
algorithmic results that are explicitly cited in the paper are treated as
external black boxes in this report, after checking the cited sources as far as
available.

No Lean `axiom`, `constant`, `sorry`, or `admit` is used.  The external results
are not declared as Lean axioms; they are recorded here as reference-checked
black boxes, and the Lean theorems take their consequences as ordinary
hypotheses when needed.

This is not yet a complete formalization of braid groups in Lean.  A literal
end-to-end Lean proof would require a mathlib-scale development of braid
groups, parabolic subgroups, centralizers, deletion maps, and pairwise crossing
homomorphisms.  The present verification proves everything in the paper that is
not either cited braid theory/algorithmics or standard braid geometry.

## Lean-Certified Claims

Command run:

```sh
lean DCP5Verification.lean
```

Result: the file compiles.  The only emitted message is Lean's toolchain
warning that it could not query the latest release and used the installed
version `leanprover/lean4:v4.31.0`.

Placeholder scan run:

```sh
rg -n "sorry|admit|axiom|constant|by_contra" DCP5Verification.lean
```

Result: no matches.

The following local proof obligations are Lean-certified.

1. `membership_iff_double_coset_with_trivial_right`

   This proves the logical core of the first theorem: membership in a subgroup
   predicate `H` is equivalent to membership in the double coset
   `H * 1 * {1}`.  Thus a DCP algorithm for `(H,{1})` would decide the
   occurrence problem for `H`.

2. `detector_pair_for_proper_partitions`

   This proves the abstract combinatorial content of Lemma 4.2.  For two proper
   equivalence relations and a surjective relabeling, there exists a pair
   separated by the first partition whose images are separated by the second.
   The Lean theorem is slightly stronger than the paper's finite-strand
   statement: it does not use finiteness.

3. `accepted_central_exponent_gives_witness`

   This proves the positive branch of the final correction step.  If
   `x = z^k a0`, `y = z^l b0`, `g' = x g y`, the `z^m` are central and additive,
   and `k+l=0`, then `g'` has an actual double-coset witness in `A g B`.

4. `central_exponent_test_accepts`

   This proves the arithmetic identity used after Main Lemma 4.3:
   from `k=p`, `l=-q`, and `p=q`, it follows that `k+l=0`.

5. `failed_central_exponent_test_rules_out_witness`

   This proves the negative branch once the completeness implication has been
   established by the Main Lemma: if every genuine witness forces `k+l=0`, then
   `k+l != 0` rules out membership.

6. `central_exponent_correction_decides_membership`

   This combines the previous two branches into the exact decision step used in
   Theorem 4.1.

7. `conjugation_fixes_commuting_element`

   This proves the basic group calculation used when translating the
   simultaneous conjugacy equations into centralizer conditions.

8. `central_power_from_crossing_detector`

   This proves the final integer step in Main Lemma 4.3: if a crossing-number
   argument gives `2*k*p = 0` and `p != 0`, then `k=0`.

## Reference-Checked Black Boxes

The following are the proof-level external results used by `DCP5.tex`.

| Paper use | Black-box statement used | Reference check | Status |
|---|---|---|---|
| Theorem 2.2, unsolvability for arbitrary finitely generated subgroups | For `n >= 5`, some finitely generated subgroup of `B_n` has unsolvable occurrence problem. | The local file `CitedPapers/Makanina.pdf` was checked.  Theorem 1 states that for `n+1 >= 5` there exists a finitely generated subgroup `H` of the braid group `B_{n+1}` such that the particular occurrence problem for `B_{n+1}` with subgroup `H` is unsolvable.  Theorem 2 states that the general occurrence problem for `B_{n+1}` with `n+1 >= 5` is unsolvable. | Full text checked.  The translated proof has an apparent typo in the sentence before Theorem 2, saying "likewise solvable"; this contradicts Theorem 1, Theorem 2, and the preceding Mikhailova argument, so it should be read as "likewise unsolvable." |
| Theorem 4.1, running SCP/MSCP | The simultaneous/multiple simultaneous conjugacy problem in braid groups is solvable in finite time; in positive instances a conjugator can be found. | The Lee--Lee PDF text says they develop an algorithm for MSCP in braid groups and, after Theorems 2 and 3, "we can solve any MSCP in finite time." | Verified against accessible PDF text. |
| Theorem 4.1, search SCP strengthening | Decision and search SCP are effectively solvable in braid groups/Garside groups. | The KTV arXiv source says the paper solves SCP in Artin braid groups and more generally Garside groups, and states a deterministic effective solution to decision and search SCP. | Verified against arXiv source.  This can be cited as a stronger modern replacement for the enumeration fallback if desired. |
| Theorem 4.1, centralizers effectively finitely generated | Centralizers of parabolic subgroups of `B_n` are finitely generated and effectively described. | The GKLT arXiv source states that it characterizes centralizers for all parabolic subgroups and includes the corollary that such centralizers are finitely generated. | Verified against arXiv source.  The paper also cites Gurzo, Fenn--Rolfsen--Zhu, and Paris as supporting historical/special-case sources. |
| Theorem 2.7 / Theorem 4.1, double centralizer | `C_{B_n}(C_{B_n}(H)) = Z(B_n) * H = <Delta_n^2> * H` for parabolic `H`. | GKLT source states this in the introduction and proves it in the general parabolic case. | Verified against arXiv source. |
| Word problem / conjugacy context | Braid groups have solvable word and conjugacy problems. | Garside's official DOI record is `10.1093/qmath/20.1.235`, Quarterly Journal of Mathematics 20 (1969), 235-254. | Bibliographic record verified.  For the proof as now written, this is only needed for the enumeration fallback if the chosen SCP algorithm is decision-only. |
| Ajbal--Godelle remark | Analogous double centralizer results in broader Artin--Tits settings. | This is a contextual remark, not used in any proof. | No proof dependency. |

Sources checked:

- GKLT arXiv page: <https://arxiv.org/abs/1310.0936>
- KTV arXiv page: <https://arxiv.org/abs/1403.4622>
- Lee--Lee DOI: <https://doi.org/10.1007/3-540-46035-7_2>
- Makanina local PDF: `CitedPapers/Makanina.pdf`; DOI record: <https://doi.org/10.1007/BF01142508>
- Garside DOI: <https://doi.org/10.1093/qmath/20.1.235>

## Proof Audit by Paper Section

### Section 2: General DCP and Unsolvability

The first theorem is correct as a reduction.  The only nontrivial outside input
is Makanina's unsolvability theorem, now checked directly from
`CitedPapers/Makanina.pdf`.  The reduction itself is Lean-certified by
`membership_iff_double_coset_with_trivial_right`.

No extra subgroup-closure assumptions are needed for the formal equivalence:
if `x` is in `H * 1 * {1}`, then the right witness must be `1`, and the product
reduces to an element of `H`; conversely, any `x in H` gives the witness
`x * 1 * 1`.

### Section 3: Decomposition in `Z(B_n) * H`

The proof is mathematically sound, but it relies on standard braid geometry not
formalized in the Lean kernel:

- deleting all but two selected strands is effective on braid words;
- for two strands from distinct blocks of a standard parabolic subgroup, the
  image of every element of that subgroup is the identity in `B_2`;
- the image of `Delta_n^{2q}` under this deletion is `Delta_2^{2q}`; and
- `B_2` is infinite cyclic generated by `sigma_1`, so `sigma_1^{2q}` determines
  `q`.

These facts are standard and the argument is complete at the mathematical
paper level.  A literal Lean proof would need a braid deletion map and the
identification `B_2 ~= Z`.

The corollary for conjugate parabolics is a formal conjugation argument plus
centrality of `Delta_n^2`; no issue was found.

### Section 4: Reduction to SCP

The simultaneous conjugacy system is set up correctly.

If `g' = a g b` with `a in A`, then `a` fixes each generator of `C(A)` by
conjugation and sends each `g d_j g^{-1}` to `g' d_j (g')^{-1}`; hence `a` is a
solution of the displayed SCP system.  Therefore a negative SCP answer implies
negative DCP.

If the SCP is positive and gives a solution `x`, then:

- the first equations give `x in C(C(A))`;
- the second equations give `y = g^{-1} x^{-1} g' in C(C(B))`;
- GKLT gives `x in <Delta_n^2> A` and `y in <Delta_n^2> B`;
- the decomposition theorem gives unique integers `k,l` and elements
  `a0 in A`, `b0 in B`;
- the Lean theorem `accepted_central_exponent_gives_witness` proves that
  `k+l=0` gives an actual DCP witness;
- the positive-instance completeness proof reduces to Main Lemma 4.3, and the
  final arithmetic is Lean-certified by `central_exponent_test_accepts`.

The proof of

```tex
y = g^{-1}x^{-1}g' = Delta_n^{-2q} \bar b^{-1} b
```

is correct.  Starting from
`x = Delta_n^{2q} a g \bar b g^{-1}`, invert `x`, multiply by
`g' = a g b`, and use centrality of `Delta_n^2`.

### Lemma 4.2: Detector Pair

The partition argument is Lean-certified in the abstract theorem
`detector_pair_for_proper_partitions`.  The Lean proof shows that the lemma is
purely combinatorial and does not depend on braid theory.

### Main Lemma 4.3: Central Power Cannot Occur

The reduction to standard parabolics is correct: conjugating by the chosen
`alpha,beta` moves `A,B` to standard parabolics, and centrality of `Delta_n^2`
preserves the central exponent.

The remaining proof uses standard braid facts:

- the endpoint permutation homomorphism `nu : B_n -> S_n`;
- if `p` is the order of `nu(a)`, then `a^p` and `b^p` are pure;
- pairwise crossing numbers define homomorphisms `P_n -> Z`;
- crossing numbers are natural under conjugation;
- elements of a standard parabolic subgroup have zero crossing number between
  strands lying in distinct blocks; and
- `acr_{r,s}(Delta_n^{2m}) = 2m`.

Given these standard braid facts, the proof is complete.  Lemma 4.2 supplies
the strands `r,s`, crossing numbers give `2kp=0`, and Lean proves the integer
conclusion `k=0` in `central_power_from_crossing_detector`.

One small presentational point: the paper says "since `p >= 1`" after obtaining
`2kp=0`.  The logically relevant fact is `p != 0`; this is automatic because
`p` is the order of a permutation.  No text change is strictly necessary, but
adding "and hence `p != 0`" would make the final inference explicit.

### Main Theorem

The final proof follows from Theorem 4.1 and the cited solvability of SCP in
braid groups.  Since KTV gives an effective search SCP solution in Garside
groups, one can avoid relying on enumeration for a conjugator.  The existing
text is still correct because it explains the enumeration fallback using the
word problem.

## Remaining Lean-Formalization Gap

The remaining gap is not a gap in the mathematical proof; it is the absence of
a Lean braid-group library in this workspace.  To make the entire paper a
literal Lean proof, the following objects and facts would have to be formalized:

1. Artin braid groups `B_n`, pure braid groups `P_n`, and the endpoint
   permutation homomorphism.
2. Standard and conjugate parabolic subgroups.
3. The full twist `Delta_n^2` and the theorem `Z(B_n)=<Delta_n^2>` for `n>=3`.
4. Deletion maps to smaller braid groups, especially to `B_2`.
5. Pairwise algebraic crossing-number homomorphisms on `P_n`.
6. Centralizer generation and the GKLT double-centralizer theorem, or explicit
   black-box theorem declarations in a project-level formalization.
7. A formal model of computability/decidability for the algorithmic statements.

This is a substantial separate formalization project.  The current Lean file
certifies all local, non-braid-library reasoning that the paper adds on top of
the cited external results.

## Referee-Level Conclusion

From a meticulous referee's perspective, the paper's proof is coherent and the
main reduction is correct, assuming the cited centralizer/double-centralizer and
SCP results.  The previous source-access concern for Makanina is closed by the
local PDF in `CitedPapers/Makanina.pdf`; its Theorem 1 states exactly the
particular occurrence-problem unsolvability needed for the paper's preliminary
DCP-unsolvability theorem.

For the main positive theorem, the proof is robust.  The only possible polish
would be to add a sentence or citation identifying the standard braid-geometric
facts about strand deletion and crossing-number homomorphisms, but the present
arguments are mathematically complete for readers familiar with braid groups.
