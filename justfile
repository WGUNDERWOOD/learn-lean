default: tex

tex:
    @tex-build primes.tex
    @tex-check primes.log
    @compress-pdf -h primes.pdf
    @compress-pdf -h primes.pdf
    @compress-pdf -h primes.pdf

lean:
    lake build

cache:
    lake exe cache get
