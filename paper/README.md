# Manuscript v0.1

[manuscript.pdf](manuscript.pdf) is the 11-page manuscript v0.1 with the rc3 editorial revision; [manuscript.tex](manuscript.tex) is its source. Relative to the scientific v0.1 archive, one introductory attribution paragraph has been rephrased (rc2), one AI-workflow disclosure sentence has been added before the introductory roadmap (rc3), and the PDF has been rebuilt. The complete source is unchanged outside those edits; see the [rc2 editorial record](../provenance/EDITORIAL_CHANGES.json) and [rc3 disclosure record](../provenance/AI_DISCLOSURE_UPDATE.json). The full AI contribution statement at the end of the paper is retained. The earlier freezes are preserved.

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

Use the prebuilt PDF to inspect the exact candidate artifact. A rebuild can differ in timestamp or compiler metadata even when the source and displayed content agree.
