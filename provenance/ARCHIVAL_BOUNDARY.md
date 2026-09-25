# Research archive and public file view

The complete scientific freeze is retained locally as Gaussian_MinPur_v0.1.zip. Its SHA-256 is:

    1610956a15654942ef7fa7db0f737e4345a353b50ff37faff8864b27fadd33b0

This repository contains the current paper, byte-identical scientific scripts, explanatory documents, and diagnostic records. SOURCE_MAP.json records each selected archive member and its original and distributed hashes. The paper contains the introductory attribution revision documented in EDITORIAL_CHANGES.json and the one-sentence introduction disclosure documented in AI_DISCLOSURE_UPDATE.json. The independent reference JSON has only its local interpreter path replaced; its numerical fields are unchanged.

The larger archive includes historical drafts, raw AI reviews and search records, local build/runtime paths, and intermediate audit implementations discussed in audits/STATUS.md. Those packages are retained separately, unchanged, for author-controlled reviewer access.

The repository's original diagnostic scripts and the independent density implementation match their archived sources byte for byte. The new scripts/ entry points only stage, execute and check them. Reference logs are preserved, while a fresh replay creates new logs under .local/.

## Audit-report identities

- Independent-context A1V2 report: 611c6a558c080ea0e317096a2ecdac9c9241785388ab6246168e4776d931209c
- ds4.1Flash report: 0e957bfee0f8d5142d490a6f5e3e0dfafdd1d49f037a5893f3332a6e1b0f6004
- Additional supplied AI report: 5133a5b0b0646f7f852ff5ee5068f3aa91ca06d9cc2579a847f3f8a6738ec5ab
- Parent three-report adjudication: 96a4ed1dac3f22888f711761d48584bcb60103a34865045f55717d790812dce7

These are archive fingerprints, not publicly registered DOIs or mathematical certificates. The public summary records the material qualifications of the raw reviews.

## Distribution scope

| Public repository and source ZIP | Retained locally |
| --- | --- |
| Current paper, scientific checks, reference results and explanatory documents | Complete historical research and review archives |
| Source maps, licenses, citation metadata and file checksums | Author review notes, build caches and working directories |
| Tracked Git history, including author and committer metadata | Git configuration and reflogs; these are not transferred by a Git push |

The repository ZIP is exported from a committed Git tree. It excludes .git/, .local/, virtual environments, raw compiler logs and local author-review documents. A Git bundle is a repository backup, not the suggested public source archive; it contains committed objects and refs, but no local configuration or reflogs.

The author's name, affiliation and academic contact email are intentionally public. The same approved academic email appears in the candidate's Git authorship metadata. Fresh local diagnostic and compiler outputs can contain the executing reader's own paths; these remain under the ignored .local/ directory and are not part of the release.

## Public v0.1 reconstruction projection

The complete CR0/MR1 input packets and three mathematical result payloads are public under reproduction/. Each result receives a publication-status notice, with both original and distributed hashes in reproduction/RUNS.json and SOURCE_MAP.json. No original frozen archive is rewritten. Raw run/access logs, environment files, intermediate optimizer code and full result ZIPs remain private. The curated index discloses the known procedural deviations and the limits of isolation verification. Additional results have not received a separate complete adversarial audit.
