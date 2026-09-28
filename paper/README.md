# Manuscript v0.1.1

[manuscript.pdf](manuscript.pdf) is the 11-page manuscript in public release v0.1.1; [manuscript.tex](manuscript.tex) is its source. This revision states the original authors' Section 6.3 matched-mode assertion more explicitly and updates the manuscript date. The theorem, proof argument and bibliography are unchanged from v0.1. See the [v0.1.1 editorial record](../provenance/V0_1_1_EDITORIAL.json), together with the earlier [rc2 attribution](../provenance/EDITORIAL_CHANGES.json) and [rc3 AI-disclosure](../provenance/AI_DISCLOSURE_UPDATE.json) records. The v0.1 tag and release preserve the earlier text and PDF.

From the repository root:

~~~sh
python scripts/build_paper.py --engine tectonic
~~~

Alternatively:

~~~sh
python scripts/build_paper.py --engine pdflatex
~~~

The source is copied into a new .local/builds/ directory before compilation. Tectonic reruns LaTeX automatically; the pdflatex option runs twice. The bibliography is included in the source, so BibTeX is unnecessary. A first Tectonic build can download its TeX bundle; an offline build requires that cache or a complete local TeX installation.

The current PDF was compiled with Tectonic 0.17.0 and rendered with Poppler for the editorial revision. No figures, shell-escape operations, or proprietary fonts are required.

Use the prebuilt PDF to inspect the exact released artifact. A rebuild can differ in timestamp or compiler metadata even when the source and displayed content agree.
