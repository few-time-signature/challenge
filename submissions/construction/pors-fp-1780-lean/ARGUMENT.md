# PORS+FP, 1,780 bytes

One accepted rank selects nine distinct leaves of a 491,520-leaf tree. The encoder accepts a support when it needs at most 102 sibling labels. The signature carries at most 111 labels of 16 bytes and a four-byte counter. Verification uses at most 121 hashes and the expected signing ceiling is 16,133,231 hashes.

With q accepted histories, at most 9q private source labels can have been disclosed. A covered target must select nine of them. Colex ranks identify distinct supports, so the covered raw-target count is at most the smaller of the accepted count and choose(9q,9). Divide by 2^152 and average over one Poisson(1) history count. The formal endpoint also checks correctness, authentication and counter failure on the registered Boolean encoder and DAG. The byte bound certifies feasibility.
