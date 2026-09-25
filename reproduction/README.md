# Independent-context derivation attempts and method-guided rederivation

**Supplementary research records. The additional results collected here have not received a separate complete adversarial audit and are not premises of the released manuscript.** Some steps received targeted post-freeze reading, described in [REVIEW_NOTES.md](REVIEW_NOTES.md). No human validation is claimed.

| Run | Information supplied before freezing | Frozen outcome | What was obtained |
| --- | --- | --- | --- |
| [CR0-1: 5.6 Sol](runs/CR0-1/RESULT.md) | Problem, conventions and primary background papers; no candidate proof or method framework | PARTIAL | Bounds, exact special families and a fixed-size fermionic attainment argument; general target unresolved. |
| [CR0-2: 6 Pro](runs/CR0-2/RESULT.md) | Same CR0 input | PARTIAL | Fixed-size attainment and a claimed bound of at most r auxiliary modes per side; general matched-size comparison unresolved. |
| [MR1-1: 5.6 Sol](runs/MR1-1/RESULT.md) | Problem and sources plus an explicit method framework; no full candidate manuscript | CLAIMED_PROOF | All eight requested nodes claimed closed. Targeted reading found no load-bearing gap; this was method-guided reconstruction, not blind discovery. |

The author reports separate temporary, memoryless contexts. Model identities and access restrictions are reported records, not independently authenticated execution environments. Network and filesystem isolation were not technically verified. The two PARTIAL outcomes remain unchanged after the later MR1 result.

## Additional mathematical material

[EXTRA_RESULTS.md](EXTRA_RESULTS.md) separates the rank-based compression claims, special-case results and the shorter attainment route from the released proof. Inclusion is for inspection and possible future work, not an assertion of new priority or an extension of the manuscript's audit coverage.

Each public RESULT.md adds a clearly identified publication notice; the original result text following that notice is byte-identical to the frozen payload. [RUNS.json](RUNS.json) records both hashes, the notice length, the original archive fingerprints, input identities and procedural qualifications. Original archives and raw access logs remain unchanged in the author's private records.

## Complete input packets

- [CR0 input v0.1](inputs/Gaussian_MinPur_CleanRoom_Input_v0.1.zip): task, conventions, protocol, complete permitted background papers and freeze tool.
- [MR1 input v0.1](inputs/Gaussian_MinPur_Method_Rederivation_Input_v0.1.zip): the same background plus the disclosed method architecture and node obligations.

These are the exact packets used, including their internal integrity manifests and third-party notices. To conduct a new blind attempt, give a fresh solver only the CR0 packet; this repository's paper, method-guided packet and result records reveal information unavailable in the original CR0 phase. MR1 explicitly permits that method information. Freeze any new run before comparison with other answers.

The input packets redistribute the two specified source papers under their own CC BY 4.0 notices; see [licensing scope](../LICENSING.md). Hashes identify files, not mathematical correctness or trusted timestamps.
