# Independent-context derivation attempts and method-guided rederivation

**Supplementary research records; not premises of the released manuscript.** The original targeted reading and the later Stage C coverage of selected nodes are distinguished in [REVIEW_NOTES.md](REVIEW_NOTES.md). This is not a blanket audit of all ancillary claims. No human validation or proof-assistant formalization is claimed.

| Run | Information supplied before freezing | Frozen outcome | What was obtained |
| --- | --- | --- | --- |
| [CR0-1: 5.6 Sol](runs/CR0-1/RESULT.md) | Problem, conventions and primary background papers; no candidate proof or method framework | PARTIAL | Bounds, exact special families and a fixed-size fermionic attainment argument; general target unresolved. |
| [CR0-2: 6 Pro](runs/CR0-2/RESULT.md) | Same CR0 input | PARTIAL | Fixed-size attainment and a claimed bound of at most r auxiliary modes per side; general matched-size comparison unresolved. |
| [MR1-1: 5.6 Sol](runs/MR1-1/RESULT.md) | Problem and sources plus an explicit method framework; no full candidate manuscript | CLAIMED_PROOF | All eight requested nodes claimed closed. Targeted reading, then Stage C cross-proof assessment, found no load-bearing gap in the complete route; this was method-guided reconstruction, not blind discovery. |

The author reports separate temporary, memoryless contexts. Model identities and access restrictions are reported records, not independently authenticated execution environments. Network and filesystem isolation were not technically verified. The two PARTIAL outcomes remain unchanged after the later MR1 result.

## Additional mathematical material

[EXTRA_RESULTS.md](EXTRA_RESULTS.md) separates the rank-based compression claims, special-case results and the shorter attainment route from the released proof. Later review includes the mixed-mode reduction and gauge-attainment interfaces; the collection as a whole is not certified, and no new priority claim is made.

Each public RESULT.md adds a clearly identified publication notice; the original result text following that notice is byte-identical to the frozen payload. [RUNS.json](RUNS.json) records both hashes, the notice length, the original archive fingerprints, input identities and procedural qualifications. Original archives and raw access logs remain unchanged in the author's private records.

## Complete input packets

- [CR0 input v0.1](inputs/Gaussian_MinPur_CleanRoom_Input_v0.1.zip): task, conventions, protocol, complete permitted background papers and freeze tool.
- [MR1 input v0.1](inputs/Gaussian_MinPur_Method_Rederivation_Input_v0.1.zip): the same background plus the disclosed method architecture and node obligations.

These are the exact packets used, including their internal integrity manifests and third-party notices. To conduct a new blind attempt, give a fresh solver only the CR0 packet; this repository's paper, method-guided packet and result records reveal information unavailable in the original CR0 phase. MR1 explicitly permits that method information. Freeze any new run before comparison with other answers.

The input packets redistribute the two specified source papers under their own CC BY 4.0 notices; see [licensing scope](../LICENSING.md). Hashes identify files, not mathematical correctness or trusted timestamps.

## Later Stage A/B/C evidence

The [curated assessment](../audits/POST_STAGE_C.md) records Stage A's reported blind complete derivation, Stage B's hostile manuscript audit and both Stage C cross-proof audits. These new raw archives remain separately retained under the [archival policy](../provenance/ARCHIVAL_BOUNDARY.md); their input, report and frozen-archive hashes are in [POST_STAGE_C.json](../provenance/POST_STAGE_C.json). They are not part of the two public input packets above.

The publication notices prepended to the three historical RESULT files describe their status when projected publicly in September 2026. Their bytes and original frozen outcomes are preserved. Current review coverage is in this index and REVIEW_NOTES, not retroactively inserted into those payloads.
