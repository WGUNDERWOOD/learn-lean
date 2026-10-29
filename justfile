default: slides lean

slides:
    @just slides/

lean:
    lake build

cache:
    lake exe cache get
