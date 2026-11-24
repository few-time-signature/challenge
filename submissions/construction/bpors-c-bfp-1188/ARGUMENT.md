# BPORS-C+BFP, 1,188 bytes

Each of the four coordinates chooses a bucket, a four-leaf support in a 24-leaf tree, and four nonnegative residual chain depths with sum 32. A shared budget of 18 inner siblings leaves at most 74 transmitted labels. With a four-byte counter the signature takes at most 1,188 bytes. The signing ceiling is 9,816,603 hashes and a successful verification uses at most 219.

For a fixed history length, each covered target leaf has a historical supplier in the same bucket with sufficient chain depth. A supplier serving specified demands of total d has choose(35-d,3) possible depth vectors. Partition the four requested leaves among the suppliers, count the resulting assignments, then average over bucket matches and the shared Poisson history length. The certificate is for raw DAG covering at probability at most 2^-128.
