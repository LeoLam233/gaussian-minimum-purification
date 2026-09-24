# Manuscript v0.1

[manuscript.pdf](manuscript.pdf) is the 11-page frozen paper; [manuscript.tex](manuscript.tex) is its source. Both match the corresponding files in the private v0.1 archive byte for byte.

From the repository root:

~~~sh
python scripts/build_paper.py --engine tectonic
~~~

Alternatively:

~~~sh
python scripts/build_paper.py --engine pdflatex
~~~

The source is copied into a new .local/builds/ directory before compilation. Tectonic reruns LaTeX automatically; the pdflatex option runs twice. The bibliography is included in the source, so BibTeX is unnecessary. A first Tectonic build can download its TeX bundle; an offline build requires that cache or a complete local TeX installation.

The delivered PDF was compiled with Tectonic 0.17.0 and rendered with Poppler before the scientific freeze. No figures, shell-escape operations, or proprietary fonts are required.

Use the prebuilt PDF to inspect the exact frozen artifact. A rebuild can differ in timestamp or compiler metadata even when the source and displayed content agree.
