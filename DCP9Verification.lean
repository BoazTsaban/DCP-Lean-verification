/-!
Lean verification kernel for `DCP9.tex`.

This file deliberately avoids Mathlib: the folder contains no Lean project, and
core Lean does not provide the algebraic hierarchy.  We therefore use a tiny
self-contained group interface.  Cited braid-theoretic and algorithmic results
are not reproved here; in the paper-verification report they are listed as
black-box hypotheses tied to their references.

The theorems below formalize the group-theoretic part of the reduction:

* subgroup membership reduces to the double coset problem;
* the detector-pair lemma is a statement about proper partitions;
* if the central-exponent correction test accepts, the constructed elements are
  genuine double-coset witnesses;
* if a positive DCP instance gives the exponent identities proved in the paper
  using the Main Lemma and uniqueness of the decompositions, then the
  correction test necessarily accepts;
* consequently, a failed correction test rules out double-coset membership once
  the paper's completeness hypothesis for the exponent identities is available;
* the new subgroup-restricted conjugacy unsolvability argument reduces
  membership in `L <= M` to conjugacy by an element of `L`, assuming the
  externally proved fact `M ∩ C(delta) = 1`.
-/

set_option autoImplicit false

namespace DCP9

universe u v

class GroupCore (G : Type u) where
  one : G
  mul : G → G → G
  inv : G → G
  mul_assoc : ∀ a b c : G, mul (mul a b) c = mul a (mul b c)
  one_mul : ∀ a : G, mul one a = a
  mul_one : ∀ a : G, mul a one = a
  inv_mul_cancel : ∀ a : G, mul (inv a) a = one
  mul_inv_cancel : ∀ a : G, mul a (inv a) = one

/- Abstract partition form of Lemma 3.1 in `DCP9.tex`.

The blocks of a standard parabolic subgroup define an equivalence relation on
the strands.  The only combinatorial fact needed in the paper is that, for two
proper partitions and a surjective relabeling of the strands, some pair is
separated by the first partition and its image is separated by the second.
The proof below does not use finiteness.
-/
def IsEquivRel {X : Type u} (R : X → X → Prop) : Prop :=
  (∀ x : X, R x x) ∧
    (∀ {x y : X}, R x y → R y x) ∧
    (∀ {x y z : X}, R x y → R y z → R x z)

def HasAtLeastTwoBlocks {X : Type u} (R : X → X → Prop) : Prop :=
  ∃ x y : X, ¬ R x y

theorem detector_pair_for_proper_partitions
    {X : Type u} {Y : Type v}
    (A : X → X → Prop)
    (B : Y → Y → Prop)
    (π : X → Y)
    (hAeq : IsEquivRel A)
    (hBeq : IsEquivRel B)
    (hAproper : HasAtLeastTwoBlocks A)
    (hBproper : HasAtLeastTwoBlocks B)
    (hsurj : ∀ y : Y, ∃ x : X, π x = y) :
    ∃ r s : X, ¬ A r s ∧ ¬ B (π r) (π s) := by
  classical
  by_cases hex : ∃ r s : X, ¬ A r s ∧ ¬ B (π r) (π s)
  · exact hex
  · exfalso
    have A_symm : ∀ {x y : X}, A x y → A y x := hAeq.2.1
    have A_trans : ∀ {x y z : X}, A x y → A y z → A x z := hAeq.2.2
    have B_symm : ∀ {x y : Y}, B x y → B y x := hBeq.2.1
    have B_trans : ∀ {x y z : Y}, B x y → B y z → B x z := hBeq.2.2
    have hcross : ∀ r s : X, ¬ A r s → B (π r) (π s) := by
      intro r s hnotA
      by_cases hB : B (π r) (π s)
      · exact hB
      · exfalso
        exact hex ⟨r, s, hnotA, hB⟩
    rcases hAproper with ⟨a0, b0, hnot_a0_b0⟩
    have h_a0_b0 : B (π a0) (π b0) :=
      hcross a0 b0 hnot_a0_b0
    have h_anchor : ∀ x : X, B (π x) (π b0) := by
      intro x
      by_cases hx : A x a0
      · have hx_not_b0 : ¬ A x b0 := by
          intro hxb0
          exact hnot_a0_b0 (A_trans (A_symm hx) hxb0)
        exact hcross x b0 hx_not_b0
      · exact B_trans (hcross x a0 hx) h_a0_b0
    have hB_universal : ∀ y z : Y, B y z := by
      intro y z
      rcases hsurj y with ⟨r, hr⟩
      rcases hsurj z with ⟨s, hs⟩
      rw [← hr, ← hs]
      exact B_trans (h_anchor r) (B_symm (h_anchor s))
    rcases hBproper with ⟨y, z, hnot_y_z⟩
    exact hnot_y_z (hB_universal y z)

variable {G : Type u} [GroupCore G]

scoped notation "𝟙" => GroupCore.one
scoped infixl:70 " ⋆ " => GroupCore.mul
scoped postfix:max "⁻¹ᵍ" => GroupCore.inv

open scoped DCP9

@[simp] theorem one_mul (a : G) : 𝟙 ⋆ a = a :=
  GroupCore.one_mul a

@[simp] theorem mul_one (a : G) : a ⋆ 𝟙 = a :=
  GroupCore.mul_one a

@[simp] theorem inv_mul_cancel (a : G) : a⁻¹ᵍ ⋆ a = 𝟙 :=
  GroupCore.inv_mul_cancel a

@[simp] theorem mul_inv_cancel (a : G) : a ⋆ a⁻¹ᵍ = 𝟙 :=
  GroupCore.mul_inv_cancel a

theorem assoc (a b c : G) : (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) :=
  GroupCore.mul_assoc a b c

theorem inv_eq_of_mul_eq_one_right {a b : G} (h : a ⋆ b = 𝟙) : b = a⁻¹ᵍ := by
  calc
    b = 𝟙 ⋆ b := by rw [one_mul]
    _ = (a⁻¹ᵍ ⋆ a) ⋆ b := by rw [inv_mul_cancel]
    _ = a⁻¹ᵍ ⋆ (a ⋆ b) := by rw [assoc]
    _ = a⁻¹ᵍ ⋆ 𝟙 := by rw [h]
    _ = a⁻¹ᵍ := by rw [mul_one]

theorem eq_of_mul_inv_eq_one {a b : G} (h : a ⋆ b⁻¹ᵍ = 𝟙) : a = b := by
  calc
    a = a ⋆ 𝟙 := by rw [mul_one]
    _ = a ⋆ (b⁻¹ᵍ ⋆ b) := by rw [inv_mul_cancel]
    _ = (a ⋆ b⁻¹ᵍ) ⋆ b := by rw [assoc]
    _ = 𝟙 ⋆ b := by rw [h]
    _ = b := by rw [one_mul]

theorem inv_mul (a b : G) : (a ⋆ b)⁻¹ᵍ = b⁻¹ᵍ ⋆ a⁻¹ᵍ := by
  symm
  apply inv_eq_of_mul_eq_one_right
  calc
    (a ⋆ b) ⋆ (b⁻¹ᵍ ⋆ a⁻¹ᵍ)
        = a ⋆ (b ⋆ (b⁻¹ᵍ ⋆ a⁻¹ᵍ)) := by rw [assoc]
    _ = a ⋆ ((b ⋆ b⁻¹ᵍ) ⋆ a⁻¹ᵍ) := by rw [← assoc b b⁻¹ᵍ a⁻¹ᵍ]
    _ = a ⋆ (𝟙 ⋆ a⁻¹ᵍ) := by rw [mul_inv_cancel]
    _ = a ⋆ a⁻¹ᵍ := by rw [one_mul]
    _ = 𝟙 := by rw [mul_inv_cancel]

def Central (z : G) : Prop :=
  ∀ t : G, z ⋆ t = t ⋆ z

def InDoubleCoset (A B : G → Prop) (g gp : G) : Prop :=
  ∃ a b : G, A a ∧ B b ∧ gp = (a ⋆ g) ⋆ b

def SubgroupRestrictedConjugacy (H : G → Prop) (alpha beta : G) : Prop :=
  ∃ c : G, H c ∧ beta = (c⁻¹ᵍ ⋆ alpha) ⋆ c

/- The reduction used in the first corollary of the paper: membership in `H`
is the same as membership in the double coset `H * 1 * {1}`. -/
theorem membership_iff_double_coset_with_trivial_right
    (H : G → Prop)
    (x : G) :
    InDoubleCoset H (fun y : G => y = 𝟙) 𝟙 x ↔ H x := by
  constructor
  · intro hmem
    rcases hmem with ⟨a, b, ha, hb, hx⟩
    have hxa : x = a := by
      calc
        x = (a ⋆ 𝟙) ⋆ b := hx
        _ = (a ⋆ 𝟙) ⋆ 𝟙 := by rw [hb]
        _ = a := by rw [mul_one, mul_one]
    rw [hxa]
    exact ha
  · intro hx
    refine ⟨x, 𝟙, hx, rfl, ?_⟩
    rw [mul_one, mul_one]

/- The accepted central-exponent branch constructs an actual DCP witness. -/
theorem accepted_central_exponent_gives_witness
    (A B : G → Prop)
    (zpow : Int → G)
    (hzero : zpow 0 = 𝟙)
    (hadd : ∀ m n : Int, zpow (m + n) = zpow m ⋆ zpow n)
    (hcentral : ∀ m : Int, Central (zpow m))
    (g gp x y a0 b0 : G)
    (k l : Int)
    (ha0 : A a0)
    (hb0 : B b0)
    (hx : x = zpow k ⋆ a0)
    (hy : y = zpow l ⋆ b0)
    (hgp : gp = (x ⋆ g) ⋆ y)
    (htest : k + l = 0) :
    InDoubleCoset A B g gp := by
  refine ⟨a0, b0, ha0, hb0, ?_⟩
  calc
    gp = ((zpow k ⋆ a0) ⋆ g) ⋆ (zpow l ⋆ b0) := by rw [hgp, hx, hy]
    _ = (zpow k ⋆ (a0 ⋆ g)) ⋆ (zpow l ⋆ b0) := by rw [assoc (zpow k) a0 g]
    _ = ((a0 ⋆ g) ⋆ zpow k) ⋆ (zpow l ⋆ b0) := by rw [hcentral k (a0 ⋆ g)]
    _ = (a0 ⋆ g) ⋆ (zpow k ⋆ (zpow l ⋆ b0)) := by rw [assoc]
    _ = (a0 ⋆ g) ⋆ ((zpow k ⋆ zpow l) ⋆ b0) := by
      rw [← assoc (zpow k) (zpow l) b0]
    _ = (a0 ⋆ g) ⋆ (zpow (k + l) ⋆ b0) := by rw [← hadd k l]
    _ = (a0 ⋆ g) ⋆ (𝟙 ⋆ b0) := by rw [htest, hzero]
    _ = (a0 ⋆ g) ⋆ b0 := by rw [one_mul]

/- Arithmetic part of the completeness argument in Theorem 3.3.

In the paper:
* `p = q` is obtained from Main Lemma 3.2;
* `k = p` follows from uniqueness of the decomposition of `x`;
* `l = -q` follows from uniqueness of the decomposition of `y`.
-/
theorem central_exponent_test_accepts
    (k l p q : Int)
    (hk : k = p)
    (hl : l = -q)
    (hpq : p = q) :
    k + l = 0 := by
  subst k
  subst l
  subst p
  omega

/- Once the preceding theorem is available for every genuine double-coset
instance, the negative branch is logically sound. -/
theorem failed_central_exponent_test_rules_out_witness
    (A B : G → Prop)
    (g gp : G)
    (k l : Int)
    (hcomplete : InDoubleCoset A B g gp → k + l = 0)
    (hfail : k + l ≠ 0) :
    ¬ InDoubleCoset A B g gp := by
  intro hmem
  exact hfail (hcomplete hmem)

/- The paper's correction step, stated as a single verified decision theorem.

At this point of the proof the simultaneous conjugacy problem has already
returned a solution `x`, and the two decompositions have returned `a0,b0,k,l`.
The remaining mathematical content is exactly:

* if `k+l=0`, the displayed formula gives a witness in `A g B`;
* if `k+l≠0`, the completeness implication derived from the Main Lemma rules
  out every possible witness.
-/
theorem central_exponent_correction_decides_membership
    (A B : G → Prop)
    (zpow : Int → G)
    (hzero : zpow 0 = 𝟙)
    (hadd : ∀ m n : Int, zpow (m + n) = zpow m ⋆ zpow n)
    (hcentral : ∀ m : Int, Central (zpow m))
    (g gp x y a0 b0 : G)
    (k l : Int)
    (ha0 : A a0)
    (hb0 : B b0)
    (hx : x = zpow k ⋆ a0)
    (hy : y = zpow l ⋆ b0)
    (hgp : gp = (x ⋆ g) ⋆ y)
    (hcomplete : InDoubleCoset A B g gp → k + l = 0) :
    (k + l = 0 → InDoubleCoset A B g gp) ∧
      (k + l ≠ 0 → ¬ InDoubleCoset A B g gp) := by
  constructor
  · intro htest
    exact accepted_central_exponent_gives_witness
      A B zpow hzero hadd hcentral g gp x y a0 b0 k l
      ha0 hb0 hx hy hgp htest
  · intro hfail
    exact failed_central_exponent_test_rules_out_witness
      A B g gp k l hcomplete hfail

/- A standard group calculation used when reading the simultaneous conjugacy
system in centralizer form: if `a` commutes with `c`, then conjugation by `a`
fixes `c`. -/
theorem conjugation_fixes_commuting_element
    (a c : G)
    (hcomm : a ⋆ c = c ⋆ a) :
    (a⁻¹ᵍ ⋆ c) ⋆ a = c := by
  calc
    (a⁻¹ᵍ ⋆ c) ⋆ a = a⁻¹ᵍ ⋆ (c ⋆ a) := by rw [assoc]
    _ = a⁻¹ᵍ ⋆ (a ⋆ c) := by rw [hcomm]
    _ = (a⁻¹ᵍ ⋆ a) ⋆ c := by rw [← assoc]
    _ = 𝟙 ⋆ c := by rw [inv_mul_cancel]
    _ = c := by rw [one_mul]

theorem commutes_of_conjugation_fixes
    (a c : G)
    (hfix : (a⁻¹ᵍ ⋆ c) ⋆ a = c) :
    a ⋆ c = c ⋆ a := by
  calc
    a ⋆ c = a ⋆ ((a⁻¹ᵍ ⋆ c) ⋆ a) := by rw [hfix]
    _ = (a ⋆ (a⁻¹ᵍ ⋆ c)) ⋆ a := by rw [← assoc]
    _ = ((a ⋆ a⁻¹ᵍ) ⋆ c) ⋆ a := by rw [← assoc]
    _ = (𝟙 ⋆ c) ⋆ a := by rw [mul_inv_cancel]
    _ = c ⋆ a := by rw [one_mul]

theorem inv_commutes_of_commutes
    (a c : G)
    (hcomm : a ⋆ c = c ⋆ a) :
    a⁻¹ᵍ ⋆ c = c ⋆ a⁻¹ᵍ := by
  calc
    a⁻¹ᵍ ⋆ c = a⁻¹ᵍ ⋆ (c ⋆ 𝟙) := by rw [mul_one]
    _ = a⁻¹ᵍ ⋆ (c ⋆ (a ⋆ a⁻¹ᵍ)) := by rw [mul_inv_cancel]
    _ = a⁻¹ᵍ ⋆ ((c ⋆ a) ⋆ a⁻¹ᵍ) := by rw [assoc c a a⁻¹ᵍ]
    _ = a⁻¹ᵍ ⋆ ((a ⋆ c) ⋆ a⁻¹ᵍ) := by rw [hcomm]
    _ = (a⁻¹ᵍ ⋆ (a ⋆ c)) ⋆ a⁻¹ᵍ := by rw [← assoc]
    _ = ((a⁻¹ᵍ ⋆ a) ⋆ c) ⋆ a⁻¹ᵍ := by rw [← assoc]
    _ = (𝟙 ⋆ c) ⋆ a⁻¹ᵍ := by rw [inv_mul_cancel]
    _ = c ⋆ a⁻¹ᵍ := by rw [one_mul]

theorem mul_commutes_of_commutes
    (a b c : G)
    (ha : a ⋆ c = c ⋆ a)
    (hb : b ⋆ c = c ⋆ b) :
    (a ⋆ b) ⋆ c = c ⋆ (a ⋆ b) := by
  calc
    (a ⋆ b) ⋆ c = a ⋆ (b ⋆ c) := by rw [assoc]
    _ = a ⋆ (c ⋆ b) := by rw [hb]
    _ = (a ⋆ c) ⋆ b := by rw [← assoc]
    _ = (c ⋆ a) ⋆ b := by rw [ha]
    _ = c ⋆ (a ⋆ b) := by rw [assoc]

/- If both `a` and `x` fix a centralizer generator by conjugation, then the
quotient `a^{-1}x` centralizes that generator. -/
theorem quotient_of_fixed_conjugacy_solutions_centralizes
    (a x c : G)
    (ha : (a⁻¹ᵍ ⋆ c) ⋆ a = c)
    (hx : (x⁻¹ᵍ ⋆ c) ⋆ x = c) :
    (a⁻¹ᵍ ⋆ x) ⋆ c = c ⋆ (a⁻¹ᵍ ⋆ x) := by
  have hca : a ⋆ c = c ⋆ a := commutes_of_conjugation_fixes a c ha
  have hcx : x ⋆ c = c ⋆ x := commutes_of_conjugation_fixes x c hx
  exact mul_commutes_of_commutes (a⁻¹ᵍ) x c
    (inv_commutes_of_commutes a c hca) hcx

theorem source_mul_eq_mul_target_of_conjugacy
    (x source target : G)
    (hconj : (x⁻¹ᵍ ⋆ source) ⋆ x = target) :
    x ⋆ target = source ⋆ x := by
  calc
    x ⋆ target = x ⋆ ((x⁻¹ᵍ ⋆ source) ⋆ x) := by rw [hconj]
    _ = (x ⋆ (x⁻¹ᵍ ⋆ source)) ⋆ x := by rw [← assoc]
    _ = ((x ⋆ x⁻¹ᵍ) ⋆ source) ⋆ x := by rw [← assoc]
    _ = (𝟙 ⋆ source) ⋆ x := by rw [mul_inv_cancel]
    _ = source ⋆ x := by rw [one_mul]

theorem inv_mul_source_eq_target_mul_inv_of_conjugacy
    (x source target : G)
    (hconj : (x⁻¹ᵍ ⋆ source) ⋆ x = target) :
    x⁻¹ᵍ ⋆ source = target ⋆ x⁻¹ᵍ := by
  calc
    x⁻¹ᵍ ⋆ source = (x⁻¹ᵍ ⋆ source) ⋆ 𝟙 := by rw [mul_one]
    _ = (x⁻¹ᵍ ⋆ source) ⋆ (x ⋆ x⁻¹ᵍ) := by rw [mul_inv_cancel]
    _ = ((x⁻¹ᵍ ⋆ source) ⋆ x) ⋆ x⁻¹ᵍ := by rw [← assoc]
    _ = target ⋆ x⁻¹ᵍ := by rw [hconj]

/- If `a` and `x` solve the same conjugacy equation with target `target`, then
`a^{-1}x` centralizes `target`.  This is the abstract calculation behind the
second centralizer assertion in the reduction theorem. -/
theorem quotient_of_same_conjugacy_solutions_centralizes_target
    (a x source target : G)
    (ha : (a⁻¹ᵍ ⋆ source) ⋆ a = target)
    (hx : (x⁻¹ᵍ ⋆ source) ⋆ x = target) :
    (a⁻¹ᵍ ⋆ x) ⋆ target = target ⋆ (a⁻¹ᵍ ⋆ x) := by
  calc
    (a⁻¹ᵍ ⋆ x) ⋆ target = a⁻¹ᵍ ⋆ (x ⋆ target) := by rw [assoc]
    _ = a⁻¹ᵍ ⋆ (source ⋆ x) := by
      rw [source_mul_eq_mul_target_of_conjugacy x source target hx]
    _ = (a⁻¹ᵍ ⋆ source) ⋆ x := by rw [← assoc]
    _ = (target ⋆ a⁻¹ᵍ) ⋆ x := by
      rw [inv_mul_source_eq_target_mul_inv_of_conjugacy a source target ha]
    _ = target ⋆ (a⁻¹ᵍ ⋆ x) := by rw [assoc]

/- The final arithmetic step in Main Lemma 3.2.

After applying a pairwise crossing-number homomorphism, the paper obtains
`2*k*p = 0`, where `p` is the positive order of a permutation.  Lean proves the
only arithmetic fact used there: if `p` is nonzero, then the central exponent
`k` must be zero.
-/
theorem central_power_from_crossing_detector
    (k p : Int)
    (hp : p ≠ 0)
    (hcross : 2 * k * p = 0) :
    k = 0 := by
  have h' : (2 * p) * k = 0 := by
    rw [Int.mul_assoc, Int.mul_comm k p, ← Int.mul_assoc] at hcross
    exact hcross
  have hprod : 2 * p = 0 ∨ k = 0 := by
    simpa [Int.mul_eq_zero] using h'
  cases hprod with
  | inl h2p =>
      have hp0 : p = 0 := by omega
      contradiction
  | inr hk => exact hk

/- If `w^{-1} delta w = ell^{-1} delta ell`, then `w ell^{-1}` centralizes
`delta`.  This is the group calculation used in the last theorem of `DCP9.tex`.
-/
theorem same_delta_conjugate_gives_centralizer_element
    (delta w ell : G)
    (hconj : (w⁻¹ᵍ ⋆ delta) ⋆ w = (ell⁻¹ᵍ ⋆ delta) ⋆ ell) :
    (w ⋆ ell⁻¹ᵍ) ⋆ delta = delta ⋆ (w ⋆ ell⁻¹ᵍ) := by
  have hleft : delta ⋆ w = (w ⋆ (ell⁻¹ᵍ ⋆ delta)) ⋆ ell := by
    calc
      delta ⋆ w = (𝟙 ⋆ delta) ⋆ w := by rw [one_mul]
      _ = ((w ⋆ w⁻¹ᵍ) ⋆ delta) ⋆ w := by rw [mul_inv_cancel]
      _ = (w ⋆ (w⁻¹ᵍ ⋆ delta)) ⋆ w := by rw [assoc w w⁻¹ᵍ delta]
      _ = w ⋆ ((w⁻¹ᵍ ⋆ delta) ⋆ w) := by rw [assoc w (w⁻¹ᵍ ⋆ delta) w]
      _ = w ⋆ ((ell⁻¹ᵍ ⋆ delta) ⋆ ell) := by rw [hconj]
      _ = (w ⋆ (ell⁻¹ᵍ ⋆ delta)) ⋆ ell := by rw [← assoc]
  symm
  calc
    delta ⋆ (w ⋆ ell⁻¹ᵍ) = (delta ⋆ w) ⋆ ell⁻¹ᵍ := by rw [assoc]
    _ = ((w ⋆ (ell⁻¹ᵍ ⋆ delta)) ⋆ ell) ⋆ ell⁻¹ᵍ := by rw [hleft]
    _ = (w ⋆ (ell⁻¹ᵍ ⋆ delta)) ⋆ (ell ⋆ ell⁻¹ᵍ) := by rw [assoc]
    _ = (w ⋆ (ell⁻¹ᵍ ⋆ delta)) ⋆ 𝟙 := by rw [mul_inv_cancel]
    _ = w ⋆ (ell⁻¹ᵍ ⋆ delta) := by rw [mul_one]
    _ = (w ⋆ ell⁻¹ᵍ) ⋆ delta := by rw [← assoc]

/- Local verification of the new subgroup-restricted conjugacy reduction.

The paper applies this with:
* `M` the copy of `F_2 x F_2` inside the pure braid group;
* `L <= M` Mikhailova's finitely generated subgroup;
* `delta = sigma_1 ... sigma_{n-1}`;
* `htrivialCentralizer` supplied by the externally proved equality
  `M ∩ C_{B_n}(delta) = 1`.

For every input `w in M`, conjugacy of `delta` to `w^{-1} delta w` by an
element of `L` is equivalent to membership of `w` in `L`.
-/
theorem membership_iff_subgroup_restricted_conjugacy
    (M L : G → Prop)
    (delta w : G)
    (hLsubM : ∀ {x : G}, L x → M x)
    (hM_mul_inv : ∀ {x y : G}, M x → M y → M (x ⋆ y⁻¹ᵍ))
    (htrivialCentralizer :
      ∀ {x : G}, M x → x ⋆ delta = delta ⋆ x → x = 𝟙)
    (hwM : M w) :
    SubgroupRestrictedConjugacy L delta ((w⁻¹ᵍ ⋆ delta) ⋆ w) ↔ L w := by
  constructor
  · intro hsrc
    rcases hsrc with ⟨ell, hell, hbeta⟩
    have hcentral : (w ⋆ ell⁻¹ᵍ) ⋆ delta = delta ⋆ (w ⋆ ell⁻¹ᵍ) :=
      same_delta_conjugate_gives_centralizer_element delta w ell hbeta
    have hM : M (w ⋆ ell⁻¹ᵍ) :=
      hM_mul_inv hwM (hLsubM hell)
    have hunit : w ⋆ ell⁻¹ᵍ = 𝟙 :=
      htrivialCentralizer hM hcentral
    have hwell : w = ell :=
      eq_of_mul_inv_eq_one hunit
    rw [hwell]
    exact hell
  · intro hwL
    refine ⟨w, hwL, rfl⟩

end DCP9
