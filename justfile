default: tex lean

tex:
    @tex-build lean.tex
    @tex-check lean.log
    @compress-pdf -h lean.pdf
    @compress-pdf -h lean.pdf
    @compress-pdf -h lean.pdf

lean:
    lake build

cache:
    lake exe cache get
