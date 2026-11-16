# The composition and the Rust code

This file holds the sketch of the composition of the setup and the signing with its open points, and the gaps of the Rust code. [statement.tex](../statement.tex) is the guide, and its Section 4 gives the rules of the deployment contract that this file cites.

## The composition

The composition is an unreviewed paper sketch that follows the sequential composition of Canetti [Can00]. The seeds enter the ceremonies only through $F$ at tree points. Each ceremony uses fresh PRSS keys. Only the signing masks use the pair keys. A tree with correct outputs is a function of $P$, the seeds and $H$.

1. Replace the seed generation by its dealer, at the cost of its simulation error.
2. Replace each ceremony, in order, by its dealer, at the cost of its proposed error. Ceremony security on the real network is stated and not proved, so this step is open. For one ceremony, the emulating adversary takes the keys of all operators as auxiliary input. It answers signing requests on other trees and repeats earlier phases.
3. The claim on dealer trees then shows that the dealer gives the trees of the signing game. The signing bound then applies through the $\mathrm{Th}$ heuristic.

Four issues remain in step 2.

- Each ceremony needs the hash budget of the full system, including the earlier phases and the signing. An archived, incomplete proof attempt stopped at this issue.
- The ceremony claim starts with an empty $H$ cache. So the composition must replay the earlier calls at the start, or the claim must be extended to a starting cache.
- The simulator of the ceremony must work beside the emulated signing service.
- The job list of a signature ceremony comes from the output of the ceremony before it, but the open claim fixes the job list of one ceremony in advance. So the two ceremonies of a bottom tree need their own composition lemma, with one shared oracle. `treeHybridSecurity` joins them in the hybrid model. No claim joins them on the real network.

The sketch of that join on the real network has these points.

- $`\mathcal F_{\mathrm{ceremony}}`$ gives one output to all its receivers. The codeword is a function of that output and of $H$. Fix one parameter, one tree, one circuit family and one oracle. Then rule 2 gives the same codeword to all honest operators that start. In the real run, this holds only up to the error of the ceremony of the bottom tree. A bound over all runs of a tree stays open.
- The adversary can give the output to one honest operator and not to another. By rule 2, the second operator does not start. In that run, the PRSS setup of the signature ceremony then ends at no honest operator, and its messages depend on no seed. Three points stay open, namely the agreement of the operators on the run, a simulator for the stopped run, and its link to the oracle.
- $`\mathcal F_{\mathrm{ceremony}}`$ opens the chain values of a top key at every codeword it gets. So only rules 1 and 2 limit a top key to one codeword.
- $`\mathcal F_{\mathrm{tree}}`$ lets the adversary choose the receivers one time, and two calls of $`\mathcal F_{\mathrm{ceremony}}`$ let it choose two times. No simulator and no bound is proved for a join of two calls of $`\mathcal F_{\mathrm{ceremony}}`$ on the real network, and each ceremony adds its own error.

## The Rust code

No theorem connects the Rust proof of concept to the model. In November 2026, two side-by-side readings of the code and the model, the second a check of the first, found these gaps.

- All hash uses call one Keccak function. Tags of 32 bytes separate the uses of the protocol (`doc/dkg.md`, 1.1.4). Lean checks the tag rule on a copy of the 17 tag names. Each tag block has 32 bytes and no zero byte, and the tag blocks are different (`tagBlocks_nodup`). So two hash inputs with different tags differ (`tagged_ne_of_ne`), and no $\mathrm{Th}$ input starts with a tag block (`thInput_ne_tagged`). Lean does not check that the encoding of one use is injective. No theorem connects the bytes of a hash call to its input in the model, and the $\mathrm{Th}$ domain of the model takes every byte string.
- No theorem connects the circuits, the constants or the wire layout of the code to `CircuitsCompute` and `Constants`, and nobody has checked the circuits against `CircuitsCompute`.
- The code uses acknowledgements where the note assumes consensus for one message per key.
- The code drops memory without clearing it.
- The code runs batches concurrently to save memory and overlap network waits. The model completes each batch before the next, for every positive batch size, even one batch of all jobs.
- AES uses counter blocks, and the model has one bit for each key and position. No proof maps the positions to the blocks.
- The code enforces none of the run limits, ceremony locks and saved-file checks of rules 2 and 3.
- The code uses plain TCP and one service for all phases.
- The model counts the round labels over the ceremonies of a tree, and the code counts the rounds of each channel. Both continue one counter over the two ceremonies of a bottom tree. This counter is the batch tag in the model and the channel number in the code. Neither separates the hash inputs of two ceremonies by a domain.
- Malformed messages can make the code panic where the model aborts. The search in the code also panics at its limit of $L$ attempts, where the model aborts.

## Sources

- [Can00] Ran Canetti. Security and composition of multiparty cryptographic protocols. Journal of Cryptology, 13(1):143-202, 2000. [doi:10.1007/s001459910006](https://doi.org/10.1007/s001459910006).
