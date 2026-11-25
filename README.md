# Few-Time Signature Challenge

How short can a few-time signature be in the authenticated-disclosure hash-DAG model? Prove a smaller **upper bound** by constructing one eligible scheme, or a larger **lower bound** that holds for every eligible scheme. The score is the maximum successful signature length in bytes.

**Pre-launch.** You can submit a proof to the Lean checker now. Prize dates and award rules are pending. Pre-launch checks do not enter the competition standings.

[Leaderboard](https://few-time-signature.github.io/) · [Submission rules and CLI](RULES.md#submit-with-the-challenge-cli) · [Lean contract](formal/PoissonDAG/V2/Model.lean) · [Judge runs](https://github.com/few-time-signature/challenge/actions/workflows/submit.yml)

| Track | Opening bound | Proof |
| --- | ---: | --- |
| Universal lower bound | 99 bytes | [Organizer theorem](formal/PoissonDAG/V2/OpeningLowerBound.lean) |
| Construction | 756 bytes | [GRS-CC certificate](examples/entries/construction/grs-cc-756-lean/proof/Main.lean) |

Signing uses at most 2²⁴ expected hashes, verification at most 512 expected hashes, and honest signing failure is at most 2⁻¹²⁸. Draw one shared Poisson(1) number of independent successful signing histories. The probability that a fresh raw target is accepted and all its required labels can be derived from the public root and pooled disclosures must be at most 2⁻¹²⁸. Every disclosed 16-byte label contributes to the recomputed root. [Formal cost and covering experiment](formal/PoissonDAG/Model.lean)

## Try the judge

Start with `./fts --help`. The CLI creates a fork and opens one pull request per claim. [Submit a construction](RULES.md#submit-a-construction) · [Submit a lower bound](RULES.md#submit-a-lower-bound)

The [FORS proofs](examples/fors/) certify three parameter sets. The public judge verified PORS+FP at 1,780 B, BPORS+FP at 1,492 B, BPORS-C+BFP at 1,188 B and GRS-CC at 756 B. Read the authors’ explanations and proof receipts on the [organization site](https://few-time-signature.github.io/#activity). The judge and proofs came from the [public rehearsal at its migration commit](https://github.com/chongxuren/poisson-fts-public-test/tree/b0ea6b11a92cf71e5e4928afec17e1886febbc3a). Practice submissions and receipts remain available there.

For local infrastructure checks, run `python3 -B -m unittest discover -s tests -v`. The **Test the challenge** GitHub Actions workflow also runs the Linux Lean and container tests. [Licensing](LICENSE.md)
