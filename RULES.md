# Few-Time Signature Challenge rules

**Pre-launch.** The judge verifies public submissions. Pre-launch runs have no prize or ranking priority and do not update the official ledger. The organizers will publish dates and award rules before opening scored submissions.

| Track | What Lean must prove | Better score | Opening bound |
| --- | --- | --- | --- |
| Lower bound | Every eligible scheme uses at least the claimed bytes | Larger | [99 B](formal/PoissonDAG/V2/Lower99.lean) |
| Construction | The explicit submitted scheme is eligible and uses at most the claimed bytes | Smaller | [756 B GRS-CC](examples/entries/construction/grs-cc-756-lean/proof/Main.lean) |

Both tracks use the **authenticated-disclosure model**. Every disclosed label must contribute to the root recomputed during verification. The model measures maximum serialized signature bytes, expected signing and verification hashes, honest failure, and the chance that disclosures from one shared Poisson(1) history cover a fresh independent raw target. The covering target is a symbolic probability of at most 2⁻¹²⁸. Full adaptive ROM unforgeability would require another theorem. The independent input bits feed an explicit acyclic Boolean circuit. The Lean examples use the namespace `PoissonDAG.V2` for this model. [Formal contract](formal/PoissonDAG/V2/Model.lean) · [Base definitions](formal/PoissonDAG/Model.lean)

## One scored claim per pull request

- A **construction PR** claims one maximum byte bound for one fixed scheme and parameter set. Two parameter sets you want scored separately need separate PRs, even within the same family. [2,132-byte FORS+C entry](examples/entries/construction/fors-c-2132/) · [2,020-byte FORS+C entry](examples/entries/construction/fors-c-2020/)
- A **lower-bound PR** claims one universal byte bound. A construction and a lower bound prove different claims and need separate PRs.
- You may use multiple commits and Lean helper modules within the entry limits. Push proof fixes to the same open PR. The judge checks the final diff against the PR base and scores the single claim in `claim.json` after its proof passes. Each new head triggers a fresh run with its own priority. After acceptance, use a new entry ID and PR for any improvement.

## Submit with the challenge CLI

You need Python 3.8 or newer, Git, and the GitHub CLI (`gh`). Sign in to GitHub once and clone the challenge repository.

```sh
gh auth login --hostname github.com
git clone https://github.com/few-time-signature/challenge.git
cd challenge
```

Choose a fresh ID and your team name. The construction starter copies the complete 756 B GRS-CC opening entry, including its Lean proof and attribution. For a lower bound, replace `construction` with `lower-bound` in both paths and commands. Its starter is the credited 99 B proof.

```sh
./fts init construction my-design --team my-team
# Edit the claim, program, Lean proof, argument and provenance in this directory.
./fts check submissions/construction/my-design
./fts submit submissions/construction/my-design
```

`check` validates the file layout, claim and construction manifest locally. `submit` publishes the selected directory, including uncommitted edits, through your GitHub account. It creates or reuses your fork and opens a PR against the latest upstream `main`. Your working branch and index stay in place. GitHub Actions replays the Lean proof. During pre-launch it reports the result on the PR.

- **Revise an open PR** by editing the same directory and running `submit` again. An unchanged retry on the same base returns the existing PR. A new head receives a new intake priority.
- **Check a result** with `./fts status PR_NUMBER`, using the number printed by `submit`. Run `./fts leaderboard` for the official byte scores on both tracks.
- **Rehearse** by submitting the starter with its attribution intact. The pre-launch judge reports pass or fail. When scoring opens, only strict improvements qualify for a leaderboard place.

## Prepare a submission

To submit manually, use the same entry format and GitHub judge.

1. Fork the repository. Start a branch at the latest upstream `main`.
2. Add **one new directory** at `submissions/<track>/<id>/`, choosing either `construction` or `lower-bound`. A team may enter both tracks through separate PRs. Use lowercase letters, digits and hyphens for the ID and team name. Choose a fresh ID for each accepted entry.
3. Add the four common files below and, for a construction, `program.json`. Restrict the PR diff to files added under your new entry directory. Commit, push your branch and open a pull request to upstream `main`. The PR, submitted source and judge result are public. Submit material you have the rights to license and retain third-party notices. [Repository licenses](LICENSE.md)

| File | Contents |
| --- | --- |
| `claim.json` | Claim, team and contract, as below |
| `proof/Main.lean` | The theorem named `Submission.certificate` |
| `ARGUMENT.md` | Required public summary followed by the mathematical argument |
| `PROVENANCE.md` | Contributors, source of the proof and prior work |

## Public write-up

Every entry on either track must include an author-written summary at the start of `ARGUMENT.md`. Use UTF-8 text. An optional Markdown heading (up to 200 characters) supplies the display title. The first paragraph after it is the public summary (up to 1,200 characters). Separate the detailed argument with a blank line.

For a **construction**, give the byte bound, explain what the signer sends, and identify the design choice that achieves the size within the hash budgets. For a **lower bound**, give the byte bound, name the class of schemes it covers, and explain the proof idea. Credit reused designs and proofs in `PROVENANCE.md`. If your result has a paper, include its HTTPS URL in the optional `paper_url` field of `claim.json`. The registered construction families already have paper links.

For example, a construction summary could read:

> GRS-CC signatures fit in 756 bytes. Seven layers disclose six 16-byte labels each, five more labels authenticate the outer choice, and a four-byte counter completes the signature. The verifier recomputes the root in at most 441 hashes.

After a successful Lean replay, the organization website displays the title and summary with links to the full write-up at the verified revision and the judge receipt. The site shows the latest verified revision of each PR, including pre-launch entries. Lean verifies the formal claim. Authors are responsible for the prose and citations. [Submission write-ups](https://few-time-signature.github.io/#activity)

## Submit a lower bound

For example, the following two files reproduce the organizer's known theorem. Say so in the provenance.

```json
{"contract":"poisson-dag-v2-challenge-1","track":"lower-bound","id":"replay-99","team":"example-team","bound_bytes":99}
```

```lean
import PoissonDAG.V2.Lower99

theorem Submission.certificate : PoissonDAG.V2.UniversalLowerBound 99 :=
  PoissonDAG.V2.lower99
```

## Submit a construction

Supply an executable construction and a complete Lean proof for the same scheme. **Smaller maximum serialized signatures win.** The opening record is **756 B**, set by GRS-CC. Once scoring opens, a verified 755 B construction would improve the opening by one byte. A 756 B replay ties the opening and earns no place. [Opening entry](examples/entries/construction/grs-cc-756-lean/) · [Lean judge receipt](https://github.com/few-time-signature/challenge/actions/runs/45456970669)

1. Place the four common files and `program.json` in `submissions/construction/<id>/`. Set the track to `construction` and `bound_bytes` to your claimed upper bound, in whole bytes.
2. Bind the implementation to the claim using **one** of the two program formats below. For an original design, submit the actual DAG and Boolean encoder. The fixed organizer implementations listed below can be selected by name.
3. Prove `PoissonDAG.V2.ConstructionCertificate yourScheme N` in the unconditional theorem `Submission.certificate`. The judge constructs its own goal from the manifest and claimed byte count. Eligibility includes well-formedness, honest correctness, authenticated disclosures, honest failure ≤ 2⁻¹²⁸, expected signing ≤ 2²⁴ hashes, expected verification ≤ 512 hashes, and the shared-Poisson(1) covering target ≤ 2⁻¹²⁸. The size claim is a maximum.
4. Describe the construction, size and hash accounting in `ARGUMENT.md`. Credit the design and the proof authors in `PROVENANCE.md`. A runnable example, simulations or a theorem that assumes eligibility leaves the entry unranked.

**FORS references.** The three frozen configurations have [parameter sets and Lean proofs](examples/fors/). Use an exact manifest such as `{"representation":"organizer-reference-v1","scheme":"fors-c-17-7-19-v1"}`. The byte bound in your claim must follow from a proof for that exact scheme.

#### PORS family references

| Construction | Manifest scheme | Verified upper bound (bytes) |
| --- | --- | ---: |
| PORS+FP | `pors-fp-1780-v1` | 1,780 |
| BPORS+FP | `bpors-fp-1492-v1` | 1,492 |
| BPORS-C+BFP | `bpors-c-bfp-1188-v1` | 1,188 |

Each manifest selects one [graph and encoder](formal/PoissonDAG/Constructions/PORS/Literal.lean). To complete its [conditional certificate](formal/PoissonDAG/Constructions/PORS/LiteralAssembly.lean), prove the row's `Refinement` for that circuit. Pre-launch submissions supplied the unconditional proofs. [PORS+FP](https://github.com/few-time-signature/challenge/pull/6) · [BPORS+FP](https://github.com/few-time-signature/challenge/pull/7) · [BPORS-C+BFP](https://github.com/few-time-signature/challenge/pull/5)

#### GRS-CC reference

**Fixed GRS-CC reference.** Copy the [756-byte manifest](examples/grs-cc/program.json) to `program.json`. It names exactly the organizer's graph and encoder at the checked base commit. This fits the upload limit even though the graph has 2,629,119 vertices. A change to any construction parameter describes a different scheme and must use the explicit format.

```json
{"contract":"poisson-dag-v2-challenge-1","track":"construction","id":"grs-proof","team":"example-team","bound_bytes":756}
```

The JSON above belongs in `claim.json`. The [GRS-CC Lean assembly](formal/PoissonDAG/Constructions/GRSCC/Certification.lean) reduces the remaining proof to local covering inequalities. The complete pre-launch proof discharges those inequalities. [Verified 756-byte submission](https://github.com/few-time-signature/challenge/pull/8)

**Explicit graph and encoder.** A complete runnable example is the [5,760-byte Merkle forest](examples/merkle_forest/). Its [program.json](examples/merkle_forest/program.json) is generated from the same implementation used in the sign/verify demonstration.

A program has the following format. This tiny example illustrates syntax only.

```json
{"representation":"explicit-dag-circuit-v1","graph":[["source"],["unary",0]],"encoder":{"inputs":1,"gates":[["input",0],["constant",true],["constant",false]],"outputs":[1,1,2,2,1]},"counter_bits":1}
```

Graph nodes are `source`, `unary i`, or `binary i j`. Gates are `input i`, `constant true/false`, `neg i`, `conj i j`, or `xor i j`. Indices are zero-based. Parents refer to earlier nodes or gates. Outputs index the acceptance bit, the disclosure mask and the evaluation mask, in that order.

## How the judge accepts and ranks entries

- GitHub records a new check when a PR opens, is reopened, or receives a new head commit. For scored submissions, the numeric GitHub Actions run ID determines priority. A retry of that run keeps its priority. The ledger replays accepted runs in that order, independent of when each proof finishes. Git author dates have no role.
- The read-only job reads the exact Git snapshot as data. It compiles entrant Lean inside an isolated container. A fresh container replays only the exported proof against the organizer's goal. The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. Every submission needs a complete proof.
- After scoring opens, a successful check triggers a separate job that commits the exact entry and updated scores together. It checks the PR head again. If the checker changed since submission, rebase and push again. Failed checks leave the ledger untouched.
- A verified claim earns a place only when it strictly improves the standing record at its intake priority. The gain is the difference in bytes, in the track's direction. Identical scores give priority to the first record. Each team holds one place per track, ranked by its best qualifying byte score. Tracks are scored separately.
- The baseline is public and may be reproduced. During scored intake a check that ties an earlier entry still earns a receipt. Reusing a result requires attribution. Both Markdown files are required. The checker validates the public summary and keeps scoring tied to the Lean certificate. It does not adjudicate originality or team identity.
- Entry limits are 64 regular files, 4 MiB per file and 16 MiB total. Proof files may import helper modules under `proof/`. Use only the pinned dependencies. A standard GitHub-hosted Ubuntu runner has up to 40 minutes to build the organizer libraries. Entrant compilation and kernel replay then share a separate 25-minute limit. Each isolated container has two CPUs, 4 GiB of RAM and no network. The proof export is capped at 32 MiB. Check the failed step on the PR's Actions run before retrying.
