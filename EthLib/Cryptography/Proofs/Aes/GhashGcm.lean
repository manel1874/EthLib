module

public import EthLib.Cryptography.Proofs.Aes.Ghash

/-!
# Proofs: GHASH of GCM's authentication input

GCM pads the additional data and ciphertext separately, then appends their bit lengths.

The final block distinguishes different lengths, which raw GHASH does not.

The padding is that of SP 800-38D §7.1, Algorithm 4, steps 4 and 5.
-/

@[expose] public section

namespace EthLib.Cryptography.Aes.Gcm

open OracleComp OracleSpec ENNReal

/-- The blocks hashed in SP 800-38D §7.1, Algorithm 4, step 5. -/
def authenticationBlocks (aad ciphertext : ByteArray) : List Block :=
  blocksOf aad ++ blocksOf ciphertext ++
    [blockOfNat (8 * aad.size * 2 ^ 64 + 8 * ciphertext.size)]

/-- Padding preserves a byte string when its original length is known. -/
theorem blocksOf_inj_of_size_eq {a b : ByteArray} (hs : a.size = b.size)
    (h : blocksOf a = blocksOf b) : a = b := by
  apply ByteArray.ext
  apply Array.ext hs
  intro i hi hi'
  change i < a.size at hi
  change i < b.size at hi'
  have hj : i / 16 < (a.size + 15) / 16 := by omega
  have hj' : i / 16 < (b.size + 15) / 16 := by omega
  have hk : i % 16 < 16 := Nat.mod_lt _ (by decide)
  have hblock := congrArg (fun blocks : List Block =>
    (blocks.getD (i / 16) zeroBlock)[i % 16]) h
  simp only [blocksOf, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range, hj, hj', Option.map_some, Option.getD_some,
    Vector.getElem_ofFn] at hblock
  have hindex : 16 * (i / 16) + i % 16 = i := by omega
  simpa only [hindex, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hi', Option.getD_some] using hblock

private theorem lengthBlock_lt {a c : Nat} (ha : 8 * a < 2 ^ 64) (hc : 8 * c < 2 ^ 64) :
    8 * a * 2 ^ 64 + 8 * c < 2 ^ 128 := by omega

/-- The two 64-bit length fields determine both byte lengths. -/
theorem size_eq_of_lengthBlock_eq {a c a' c' : ByteArray}
    (ha : 8 * a.size < 2 ^ 64) (hc : 8 * c.size < 2 ^ 64)
    (ha' : 8 * a'.size < 2 ^ 64) (hc' : 8 * c'.size < 2 ^ 64)
    (h : blockOfNat (8 * a.size * 2 ^ 64 + 8 * c.size) =
      blockOfNat (8 * a'.size * 2 ^ 64 + 8 * c'.size)) :
    a.size = a'.size ∧ c.size = c'.size := by
  have hbound := lengthBlock_lt ha hc
  have hbound' := lengthBlock_lt ha' hc'
  have heq := congrArg blockToNat h
  rw [blockToNat_blockOfNat hbound, blockToNat_blockOfNat hbound'] at heq
  clear hbound hbound' ha ha' h
  constructor <;> omega

/-- Distinct admissible pairs give distinct GHASH polynomials, even at different lengths. -/
theorem ghashPolynomial_authenticationBlocks_ne {a c a' c' : ByteArray}
    (ha : 8 * a.size < 2 ^ 64) (hc : 8 * c.size < 2 ^ 64)
    (ha' : 8 * a'.size < 2 ^ 64) (hc' : 8 * c'.size < 2 ^ 64)
    (hne : (a, c) ≠ (a', c')) :
    ghashPolynomial (authenticationBlocks a c) ≠
      ghashPolynomial (authenticationBlocks a' c') := by
  intro h
  -- The coefficient of `H` is the final length block.
  have hlast := congrArg (fun p => p.coeff 1) h
  simp only [authenticationBlocks, coeff_one_ghashPolynomial_append] at hlast
  obtain ⟨haSize, hcSize⟩ :=
    size_eq_of_lengthBlock_eq ha hc ha' hc' (residue_injective hlast)
  -- Equal lengths align both data portions, where padding is injective.
  have hlength : (authenticationBlocks a c).length =
      (authenticationBlocks a' c').length := by
    simp [authenticationBlocks, blocksOf, haSize, hcSize]
  have hblocks := ghashPolynomial_inj_of_length_eq hlength h
  have hdata := (List.append_inj' hblocks (by simp)).1
  obtain ⟨haBlocks, hcBlocks⟩ := List.append_inj hdata (by simp [blocksOf, haSize])
  exact hne (Prod.ext (blocksOf_inj_of_size_eq haSize haBlocks)
    (blocksOf_inj_of_size_eq hcSize hcBlocks))

/-- GCM's padded inputs have each fixed XOR with probability at most `m / 2^128`.

Here `m` counts the blocks of the longer padded input, including the length block.

Both input pairs and the XOR are fixed before the uniform hash key is sampled.

The 64-bit bounds include every input accepted by GCM's length checks. -/
theorem prEvent_authenticationBlocks_xor_eq_le {a c a' c' : ByteArray}
    (ha : 8 * a.size < 2 ^ 64) (hc : 8 * c.size < 2 ^ 64)
    (ha' : 8 * a'.size < 2 ^ 64) (hc' : 8 * c'.size < 2 ^ 64)
    (hne : (a, c) ≠ (a', c')) (offset : Block) :
    Pr{let H ← $ᵗ Block}[xorBlock (ghash H (authenticationBlocks a c))
      (ghash H (authenticationBlocks a' c')) = offset]
      ≤ (max (authenticationBlocks a c).length
        (authenticationBlocks a' c').length : ℝ≥0∞) / 2 ^ 128 :=
  prEvent_ghash_xor_eq_le_of_polynomial_ne
    (ghashPolynomial_authenticationBlocks_ne ha hc ha' hc' hne) offset

end EthLib.Cryptography.Aes.Gcm
