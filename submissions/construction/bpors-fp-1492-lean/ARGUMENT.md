# BPORS+FP, 1,492 bytes

Each coordinate chooses one of 1,024 buckets and six distinct leaves of a 1,792-leaf tree. The two supports use at most 61 inner siblings in total. Six private labels and ten outer siblings per coordinate give at most 93 transmitted labels and a four-byte counter. The expected signing ceiling is 15,333,760 hashes and verification needs at most 106.

For a fixed history length q, condition on both pruned support tuples in every history. The bucket choices remain uniform. A covered target leaf requires a historical supplier in the same coordinate and bucket. In a bucket with m matching histories there are at most 6m available leaves. Bound the number of target six-subsets, average over matching buckets in each coordinate at this same q, then apply the outer Poisson sum. The Lean certificate checks this experiment on the registered graph and Boolean program.
