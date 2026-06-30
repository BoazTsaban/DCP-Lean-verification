# DCP9 Lean Verification Report

Date: 2026-07-01

Source paper: `DCP9.tex`

Lean artifact: `DCP9Verification.lean`

Lean version used: Lean 4.31.0

## Scope

The workspace does not contain a Lean/mathlib project, and core Lean does not
include braid groups or the usual algebraic hierarchy.  The verification
therefore uses a self-contained group interface and proves the local logical,
group-theoretic, combinatorial, and integer-arithmetic parts of the paper.

No Lean `axiom`, `constant`, `sorry`, or `admit` is used.  External braid
theory and algorithmic results are not declared as Lean axioms; they are
recorded here as black-box inputs to the paper proof.  A literal end-to-end
formalization would additionally require a Lean library for braid groups,
parabolic subgroups, centralizers, strand-deletion maps, and pairwise crossing
number homomorphisms.

## Commands Run

```sh
lean Lean/DCP9Verification.lean
```

Result: the file compiles.  Lean emitted only the toolchain warning that it
could not query the latest release and used the installed version
`leanprover/lean4:v4.31.0`.

```sh
rg -n "DCP5|sorry|admit|axiom|constant" Lean/DCP9Verification.lean
```

Result: no matches.

## Lean-Certified Claims

The following proof obligations are Lean-certified in `DCP9Verification.lean`.

1. `membership_iff_double_coset_with_trivial_right`

   This proves the reduction used in the first corollary of `DCP9.tex`:
   membership in a subgroup predicate `H` is equivalent to membership in the
   double coset `H * 1 * {1}`.

2. `detector_pair_for_proper_partitions`

   This proves the abstract combinatorial content of Lemma
   `lem:detector-pair`.  For two proper equivalence relations and a surjective
   relabeling, there exists a pair separated by the first partition whose
   images are separated by the second.  The Lean theorem is slightly stronger
   than the finite braid-strand statement because it does not use finiteness.

3. `accepted_central_exponent_gives_witness`

   This proves the positive branch of the central correction step.  If
   `x = z^k a0`, `y = z^l b0`, `g' = x g y`, the `z^m` are central and
   additive, and `k + l = 0`, then `g'` has an actual double-coset witness in
   `A g B`.

4. `central_exponent_test_accepts`

   This proves the integer arithmetic used after Main Lemma
   `lem:central-power`: from `k = p`, `l = -q`, and `p = q`, it follows that
   `k + l = 0`.

5. `failed_central_exponent_test_rules_out_witness`

   This proves the negative branch once the completeness implication has been
   established by the Main Lemma: if every genuine witness forces `k + l = 0`,
   then `k + l != 0` rules out membership.

6. `central_exponent_correction_decides_membership`

   This combines the two central-exponent branches into the decision step used
   in Theorem `thm:reduction`.

7. `conjugation_fixes_commuting_element`

   This proves the basic calculation that if an element commutes with a
   centralizer generator, then conjugation by that element fixes the generator.

8. `quotient_of_fixed_conjugacy_solutions_centralizes`

   This proves that if two elements both fix a generator by conjugation, then
   their quotient centralizes that generator.  This supports the step
   `a^{-1}x in C(C(A))` in Theorem `thm:reduction`.

9. `quotient_of_same_conjugacy_solutions_centralizes_target`

   This proves that if two elements solve the same conjugacy equation with the
   same target, then their quotient centralizes the target.  This supports the
   step
   `a^{-1}x in g C(C(B)) g^{-1}` in Theorem `thm:reduction`.

10. `central_power_from_crossing_detector`

   This proves the final integer step in Main Lemma `lem:central-power`: if a
   crossing-number argument gives `2 * k * p = 0` and `p != 0`, then `k = 0`.

11. `same_delta_conjugate_gives_centralizer_element`

   This proves the group calculation in the subgroup-restricted conjugacy
   theorem: from
   `w^{-1} delta w = ell^{-1} delta ell`, it follows that
   `w ell^{-1}` centralizes `delta`.

12. `membership_iff_subgroup_restricted_conjugacy`

   This proves the local reduction in Theorem
   `thm:subgroup-conjugacy-unsolvable`.  Assuming `L <= M`, closure of `M`
   under products `x y^{-1}`, the input condition `w in M`, and the externally
   proved fact `M cap C(delta) = 1`, the subgroup-restricted conjugacy instance
   for `delta` and `w^{-1} delta w` is positive exactly when `w in L`.

## External Black-Box Inputs

The following are the non-Lean inputs used by `DCP9.tex`.

| Paper use | Black-box statement used | Verification status |
|---|---|---|
| Corollary after the DCP definition | For `n >= 5`, braid groups `B_n` contain finitely generated subgroups with unsolvable subgroup membership problem. | External theorem of Makanina, using Mikhailova's theorem. |
| Context around `B_3` and `B_4` | Rational subset membership in `B_3` is decidable; the subgroup membership problem in `B_4` remains open. | External literature input; not used in the proof of the Main Theorem. |
| Theorem `thm:double-centralizer` | For parabolic `H <= B_n`, `C(C(H)) = <Delta_n^2> H`. | External theorem of Garber, Kalka, Liberman and Teicher. |
| Theorem `thm:reduction` | Centralizers of parabolic braid subgroups are finitely generated and effectively computable. | External braid-theoretic algorithmic result. |
| Theorem `thm:reduction` and Main Theorem | The simultaneous conjugacy problem in braid groups is solvable and a conjugator can be produced in positive instances. | External theorem of Lee and Lee. |
| Proposition `prp:decomposition` | Strand deletion maps are effective; deleting all but two strands in distinct parabolic blocks kills the parabolic component and detects the central exponent in `B_2 ~= Z`. | Standard braid geometry; not formalized in the kernel. |
| Main Lemma `lem:central-power` | Endpoint permutations, purity of powers, naturality of pairwise crossing numbers, vanishing of crossing numbers across parabolic blocks, and `acr_{r,s}(Delta_n^{2m}) = 2m`. | Standard braid geometry; the final arithmetic is Lean-certified. |
| Theorem `thm:subgroup-conjugacy-unsolvable` | Makanina's explicit braids generate a copy of `F_2 x F_2` in `P_n`, and Mikhailova provides a finitely generated subgroup with unsolvable membership problem. | External construction and theorem. |
| Theorem `thm:subgroup-conjugacy-unsolvable` | `C_{B_n}(delta) = <delta>` for `delta = sigma_1 ... sigma_{n-1}`, and `delta^n = Delta_n^2`. | External braid centralizer and Garside facts. |

## Proof Audit by Paper Section

### Section 1: Double Coset Problem

The reduction from subgroup membership to the double coset problem is
Lean-certified.  The unsolvability conclusion for arbitrary finitely generated
subgroups depends on Makanina's theorem.

The statement that double cosets of finitely generated subgroups are rational
in `B_3` is not used later in the proof.  It is a contextual consequence of
rational subsets being closed under product.

### Section 2: Decomposing Parabolic Modulo Central Elements

The proposition is mathematically coherent but depends on braid-specific
geometry not available in the Lean kernel:

- effective deletion of all but two strands;
- the fact that elements of a standard parabolic subgroup do not cross strands
  from distinct blocks;
- the image of `Delta_n^{2q}` under the two-strand deletion being
  `Delta_2^{2q}`;
- the identification `B_2 ~= Z`, which lets one read off `q`.

Given these standard braid facts, the proof determines the central exponent and
then the parabolic component uniquely.

### Section 3: Proof of the Main Theorem

Lemma `lem:detector-pair` is Lean-certified in its abstract partition form.

Main Lemma `lem:central-power` is correct modulo the standard crossing-number
facts listed above.  The reduction from conjugate parabolics to standard
parabolics uses only centrality of `Delta_n^2`.  After crossing numbers give
`2kp = 0`, the conclusion `k = 0` is Lean-certified from `p != 0`; in the paper
this is stated as `p >= 1`, which is stronger than needed.

The simultaneous conjugacy instance in Theorem `thm:reduction` is aligned with
the proof:

- if `g' = a g b`, then `a` satisfies the displayed simultaneous conjugacy
  system;
- if a solution `x` exists, the first equations put `x` in `C(C(A))`;
- with `y = g^{-1} x^{-1} g'`, the second equations put `y` in `C(C(B))`;
- the double-centralizer theorem and the decomposition proposition yield the
  central exponents `k,l`;
- the test `k + l = 0` is Lean-certified to give a genuine double-coset
  witness;
- if the original instance is positive, Main Lemma `lem:central-power` forces
  the paper's exponents `p,q` to be equal, and Lean verifies the arithmetic
  conclusion `k + l = 0`.

No local group-theoretic error was found in this section.

### Section 4: Subgroup-Restricted Conjugacy

The new reduction is Lean-certified modulo the stated external braid facts.
The Lean theorem `membership_iff_subgroup_restricted_conjugacy` formalizes the
heart of the argument:

```text
SRCP_L(delta, w^{-1} delta w) is positive  <->  w in L
```

under the hypotheses `w in M`, `L <= M`, closure of `M` under `x y^{-1}`, and
`M cap C(delta) = 1`.

The proof of `M cap C(delta) = 1` in the paper depends on:

- `C_{B_n}(delta) = <delta>`;
- `delta^n = Delta_n^2`;
- `M <= P_n`;
- `nu(delta)` has order `n`;
- `Delta_n^2` is central;
- `M ~= F_2 x F_2` has trivial center.

These are standard or cited inputs, not Lean-certified in this kernel.

### Discussion and Formal Verification Paragraph

The formal-verification paragraph in `DCP9.tex` accurately describes the
verification as partial and conditional on cited black-box braid-theoretic and
algorithmic results.  The updated Lean file also verifies the local reduction
used in the subgroup-restricted conjugacy theorem, which is additional coverage
beyond the short list in that paragraph.

## Conclusion

The updated Lean folder verifies the local formal content of `DCP9.tex` that
can be expressed without a braid-group library.  The DCP reduction, the central
ambiguity correction, the detector-pair combinatorics, the final arithmetic in
the Main Lemma, and the subgroup-restricted conjugacy reduction all compile in
Lean 4 with no axioms, constants, admits, or sorrys.

The correctness of the full paper remains conditional on the explicitly cited
external braid-theoretic and algorithmic results, as stated in the paper.
