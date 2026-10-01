# Licensing scope

The following licenses apply to the original project materials:

| Material | License |
| --- | --- |
| Original Python code in scripts/ and verification/, original Lean source (subject to the explicit exception below), and original code configuration | [MIT](LICENSE) |
| Original manuscript source and PDF, documentation, release notes and explanatory prose | [CC BY 4.0](LICENSES/CC-BY-4.0.txt) |
| Original metadata and diagnostic JSON/log content | CC BY 4.0 to the extent rights apply; mathematical facts and raw numerical values are not claimed as exclusive rights |
| Third-party publications, attributed quotations, license texts and dependency software | Their respective terms; excluded from the project grants |

Attribution: Dehao Lin, *A Mode Bound for Gaussian Entanglement of Purification*; manuscript v0.1.1, repository documentation v0.1.3. Link to [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/) and indicate changes where applicable.

The MIT license applies to original code. Its standard reference to associated documentation does not override the separate CC BY 4.0 treatment of the manuscript and project prose.

The repository does not redistribute dependency binaries. The two complete input ZIPs under reproduction/inputs/ include Windt et al., SciPost Physics 10, 066 (2021), and Hackl–Bianchi, SciPost Physics Core 4, 025 (2021), under their own CC BY 4.0 terms. Each ZIP retains its THIRD_PARTY_NOTICES.md, source metadata and license text. These publications are excluded from the project's original-material grant; their authors do not endorse this project. Bibliographic links and archive hashes do not grant rights in the referenced material. The full pre-existing research and audit archives are retained separately and are not relicensed wholesale by these notices.

Original verifier files are distributed byte-identically, without inserting new license headers. This scope notice applies alongside those files. The included CC BY 4.0 text was taken from the author's prior repository; its canonical legal text is [Creative Commons' legal code](https://creativecommons.org/licenses/by/4.0/legalcode).

The original research-output prose in reproduction/ and the expert brief are covered by the project prose license. Publication notices are editorial additions; the frozen output payloads themselves are unchanged. Any original tools inside the input ZIPs retain their included MIT notices.

## Lean source and dependency exception

All 313 protected project files were inspected for explicit license/copyright notices without changing them. `formalization/Gaussian/Algebra/SymplecticPivot.lean` contains a proof reproduced from Mathlib's `Mathlib/LinearAlgebra/SymplecticGroup.lean` at commit `d13f23b723b8a846827a245b89c10fc7d3f11612`. Its preserved header credits Copyright (c) 2022 Matej Penciak and the upstream authors Matej Penciak, Moritz Doll, Fabien Clery, Seed Prover and Huanyu Zheng, and specifies **Apache 2.0**. The reproduced/upstream-derived material remains under [Apache-2.0](LICENSES/Apache-2.0.txt), not the project's MIT grant. Its original notice and the statement that it is re-exposed from a private upstream theorem remain intact; integration made no edits to that file. No conflicting explicit license notice was found elsewhere in the protected inventory.

The Apache license text distributed here is taken unchanged from the frozen archive's recorded Mathlib license. Original additions remain under the original-code MIT grant where applicable, without overriding upstream conditions. The immutable project README is original explanatory prose covered by CC BY 4.0; its source/configuration metadata is original code metadata under MIT where rights apply. Generated factual provenance and SHA-256 inventories are not claimed as exclusive mathematical or factual rights.

Lean, mathlib, Physlib and all transitive dependencies belong to their respective contributors and retain their upstream terms. The repository does not claim ownership of them and does not vendor dependency sources or binaries. Exact pinned package dependencies are fetched at build time. The one explicitly attributed, already verified Mathlib proof excerpt above is the documented exception to a source-only original-project distribution; its upstream attribution must be retained. The frozen evidence archives, if publicly distributed after privacy review, retain all embedded third-party notices and are not relicensed wholesale.
