# GRS-CC at 756 bytes

An accepted signature discloses at most 47 labels of 16 bytes and one four-byte counter. The seven layers contribute six labels each. Five more labels authenticate the outer choice. The registered graph and encoder use fewer than 11,676,797 expected signing hashes and at most 441 verification hashes on success.

## Counting all twenty local cases

Fix a six-bit inclusion–exclusion mask. For each target assignment let `a` count avoiding histories in the target slot, `b` count avoiding histories in the other slots, and `c` count legal completions of the target. With `v` same-slot histories and `w` other-slot histories, the assignment contributes `c a^v b^w`. The mask determines the sign. The organizer's reduction covers `2 ≤ v+w ≤ 6` with `v ≥ 1`.

Sum the polynomial `c (1 + a X + b X^7)^6` over the assignments of a mask. Its coefficient at degree `v+7w` is the required unsigned moment multiplied by `choose(6,w) choose(6-w,v)`. The indices are distinct because both exponents lie between zero and six. All coefficients are nonnegative. Lean bounds their sum by a number strictly below `2^200`, so evaluating once at this radix stores every coefficient in its own digit. The bound applies before signs are introduced.

The proof checks 63 integer evaluations, one for each mask in the organizer's guarded numerator. It extracts the digits, divides out the multinomial factor, applies the inclusion–exclusion signs, and checks all twenty rational inequalities. The organizer's Poisson head and tail theorem then supplies the raw-target covering bound of 2⁻¹²⁸ for the fixed DAG. The final theorem also discharges correctness, authentication, failure, work and size for the literal program.

`proof/Main.lean` is the unconditional certificate. The numerical witness table is independently recomputed by the Lean kernel. This is a feasible upper bound under the challenge model.
