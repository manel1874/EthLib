module

public import EthLib.Cryptography.Proofs.Aes.Field
public import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Proofs: GHASH is almost XOR universal

GHASH of `m` blocks is a polynomial in its hash key of degree at most `m`.

For distinct block lists of the same length, their polynomials differ.

Thus any fixed XOR difference occurs for at most `m` of the `2^128` hash keys.

The probability below samples the hash key uniformly and keeps both inputs fixed.

It does not assert that the AES-derived hash key is uniform.

The argument is the polynomial root bound of [McGrew and Viega][mv], Appendix A, Lemma 2.

Their GHASH includes the length encoding that SP 800-38D §7 adds before §6.4.

[mv]: https://eprint.iacr.org/2004/193
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

open Polynomial OracleComp OracleSpec ENNReal

private instance : CharP (AdjoinRoot modulus) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (AdjoinRoot modulus)).injective 2

/-- The polynomial in the hash key computed by GHASH, SP 800-38D §6.4. -/
noncomputable def ghashPolynomial (blocks : List Block) : (AdjoinRoot modulus)[X] :=
  blocks.foldl (fun p B => (p + C (residue B)) * X) 0

theorem ghashPolynomial_nil : ghashPolynomial [] = 0 := rfl

theorem ghashPolynomial_append (blocks : List Block) (B : Block) :
    ghashPolynomial (blocks ++ [B]) = (ghashPolynomial blocks + C (residue B)) * X := by
  simp [ghashPolynomial, List.foldl_append]

/-- Evaluating the polynomial gives the residue of the executable GHASH. -/
theorem eval_ghashPolynomial (H : Block) (blocks : List Block) :
    (ghashPolynomial blocks).eval (residue H) = residue (ghash H blocks) := by
  induction blocks using List.reverseRecOn with
  | nil => simp [ghashPolynomial_nil, ghash, residue_zeroBlock]
  | append_singleton blocks B ih =>
    rw [ghashPolynomial_append, eval_mul, eval_add, eval_C, eval_X, ih,
      residue_ghash_append]

/-- GHASH has no constant term. -/
theorem coeff_zero_ghashPolynomial (blocks : List Block) :
    (ghashPolynomial blocks).coeff 0 = 0 := by
  induction blocks using List.reverseRecOn with
  | nil => simp [ghashPolynomial_nil]
  | append_singleton blocks B _ => simp [ghashPolynomial_append]

/-- The coefficient of the hash key is the final block's residue. -/
theorem coeff_one_ghashPolynomial_append (blocks : List Block) (B : Block) :
    (ghashPolynomial (blocks ++ [B])).coeff 1 = residue B := by
  simp [ghashPolynomial_append, coeff_mul_X, coeff_zero_ghashPolynomial]

/-- The polynomial degree is at most the number of blocks. -/
theorem natDegree_ghashPolynomial_le (blocks : List Block) :
    (ghashPolynomial blocks).natDegree ≤ blocks.length := by
  induction blocks using List.reverseRecOn with
  | nil => simp [ghashPolynomial_nil]
  | append_singleton blocks B ih =>
    rw [ghashPolynomial_append, List.length_append, List.length_singleton]
    exact natDegree_mul_le.trans
      (Nat.add_le_add ((natDegree_add_le _ _).trans (max_le ih (by simp))) (by simp))

/-- Equal GHASH polynomials of equal-length block lists determine the same list. -/
theorem ghashPolynomial_inj_of_length_eq {A B : List Block} (hlen : A.length = B.length)
    (h : ghashPolynomial A = ghashPolynomial B) : A = B := by
  induction A using List.reverseRecOn generalizing B with
  | nil => simpa using (List.length_eq_zero_iff.mp hlen.symm).symm
  | append_singleton A a ih =>
    rcases List.eq_nil_or_concat' B with rfl | ⟨B, b, rfl⟩
    · simp at hlen
    · have hab : a = b := residue_injective (by
        simpa only [coeff_one_ghashPolynomial_append] using
          congrArg (fun p => p.coeff 1) h)
      subst b
      rw [ghashPolynomial_append, ghashPolynomial_append] at h
      have hpoly : ghashPolynomial A = ghashPolynomial B :=
        add_right_cancel (mul_right_cancel₀ X_ne_zero h)
      exact congrArg (· ++ [a]) (ih (by simpa using hlen) hpoly)

/-- A prescribed XOR difference becomes a root of this polynomial. -/
private noncomputable def ghashDifference (A B : List Block) (c : Block) :
    (AdjoinRoot modulus)[X] :=
  ghashPolynomial A - ghashPolynomial B - C (residue c)

private theorem ghashDifference_ne_zero {A B : List Block}
    (hne : ghashPolynomial A ≠ ghashPolynomial B) (c : Block) :
    ghashDifference A B c ≠ 0 := by
  intro h
  have hc := congrArg (fun p => p.coeff 0) h
  simp only [ghashDifference, coeff_sub, coeff_C_zero, coeff_zero,
    coeff_zero_ghashPolynomial, sub_self, zero_sub, neg_eq_zero] at hc
  apply hne
  exact sub_eq_zero.mp (by simpa [ghashDifference, hc] using h)

private theorem natDegree_ghashDifference_le (A B : List Block) (c : Block) :
    (ghashDifference A B c).natDegree ≤ max A.length B.length := by
  exact (natDegree_sub_le _ _).trans (max_le
    ((natDegree_sub_le _ _).trans (max_le
      ((natDegree_ghashPolynomial_le A).trans (le_max_left _ _))
      ((natDegree_ghashPolynomial_le B).trans (le_max_right _ _)))) (by simp))

private theorem eval_ghashDifference_eq_zero {A B : List Block} {c H : Block}
    (h : xorBlock (ghash H A) (ghash H B) = c) :
    (ghashDifference A B c).eval (residue H) = 0 := by
  have hc := congrArg residue h
  rw [residue_xorBlock] at hc
  simp only [ghashDifference, eval_sub, eval_C, eval_ghashPolynomial]
  simp only [CharTwo.sub_eq_add]
  rw [hc, CharTwo.add_self_eq_zero]

/-- Different GHASH polynomials have at most the longer input's length of keys for any XOR.

This also permits unequal-length lists when their polynomials differ. -/
theorem card_ghash_xor_eq_le_of_polynomial_ne {A B : List Block}
    (hne : ghashPolynomial A ≠ ghashPolynomial B) (c : Block) :
    Nat.card {H : Block // xorBlock (ghash H A) (ghash H B) = c}
      ≤ max A.length B.length := by
  classical
  let roots := (ghashDifference A B c).roots.toFinset
  let f : {H : Block // xorBlock (ghash H A) (ghash H B) = c} → roots :=
    fun H => ⟨residue H.1, Multiset.mem_toFinset.mpr
      ((mem_roots (ghashDifference_ne_zero hne c)).mpr (eval_ghashDifference_eq_zero H.2))⟩
  have hf : Function.Injective f := fun H H' h =>
    Subtype.ext (residue_injective (congrArg Subtype.val h))
  calc Nat.card {H : Block // xorBlock (ghash H A) (ghash H B) = c}
      ≤ Nat.card roots := Nat.card_le_card_of_injective f hf
    _ = (ghashDifference A B c).roots.toFinset.card := by
      simp only [Nat.card_eq_fintype_card, Fintype.card_coe, roots]
    _ ≤ (ghashDifference A B c).roots.card := Multiset.toFinset_card_le _
    _ ≤ (ghashDifference A B c).natDegree := card_roots' _
    _ ≤ max A.length B.length := natDegree_ghashDifference_le A B c

/-- Distinct lists of `m` blocks have at most `m` keys for each prescribed XOR difference. -/
theorem card_ghash_xor_eq_le {A B : List Block} (hlen : A.length = B.length)
    (hne : A ≠ B) (c : Block) :
    Nat.card {H : Block // xorBlock (ghash H A) (ghash H B) = c} ≤ A.length := by
  simpa only [hlen, max_self] using card_ghash_xor_eq_le_of_polynomial_ne
    (fun h => hne (ghashPolynomial_inj_of_length_eq hlen h)) c

/-- There are `2^128` hash keys. -/
theorem card_block : Fintype.card Block = 2 ^ 128 := by
  rw [Fintype.card_congr (arrayVectorEquivFin _ _), Fintype.card_fun, Fintype.card_fin,
    ← FinEnum.card_eq_fintypeCard, FinEnum.card_UInt8]
  norm_num

/-- For a uniform key, each XOR has probability at most the longer length over `2^128`. -/
theorem prEvent_ghash_xor_eq_le_of_polynomial_ne {A B : List Block}
    (hne : ghashPolynomial A ≠ ghashPolynomial B) (c : Block) :
    Pr{let H ← $ᵗ Block}[xorBlock (ghash H A) (ghash H B) = c]
      ≤ (max A.length B.length : ℝ≥0∞) / 2 ^ 128 := by
  classical
  rw [SampleableType.prEvent_uniformSample, card_block,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply ENNReal.div_le_div_right
  have hmono : Monotone (fun n : Nat => (n : ℝ≥0∞)) := by
    intro a b h
    change (a : ℝ≥0∞) ≤ (b : ℝ≥0∞)
    exact_mod_cast h
  rw [← hmono.map_max]
  exact_mod_cast card_ghash_xor_eq_le_of_polynomial_ne hne c

/-- Distinct lists of `m` blocks have each fixed XOR with probability at most `m / 2^128`.

Only the hash key is sampled, uniformly from all blocks. -/
theorem prEvent_ghash_xor_eq_le {A B : List Block} (hlen : A.length = B.length)
    (hne : A ≠ B) (c : Block) :
    Pr{let H ← $ᵗ Block}[xorBlock (ghash H A) (ghash H B) = c]
      ≤ (A.length : ℝ≥0∞) / 2 ^ 128 := by
  simpa only [hlen, max_self] using prEvent_ghash_xor_eq_le_of_polynomial_ne
    (fun h => hne (ghashPolynomial_inj_of_length_eq hlen h)) c

end EthLib.Cryptography.Aes.Gcm
