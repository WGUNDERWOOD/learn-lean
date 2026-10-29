# Repository guide

## Purpose and layout

This repository contains teaching examples for learning Lean 4 and Mathlib.

- `LearnLean/` contains all Lean files.
- `slides/` contains presentation slides in beamer.
- `lakefile.lean` and `lake-manifest.json`: package configuration and dependency lockfile.
- `lean-toolchain`: pinned Lean version; keep it aligned with the Mathlib dependency.
- `flake.nix` and `flake.lock`: Nix build and development environment.

## Development and validation

- Enter the Nix environment with `nix develop` if Lean and Lake are unavailable.
- Run `lake build` (or `just lean`) to check all Lean modules.
- Run `lake env lean LearnLean/Basics.lean` to check an individual file, substituting the relevant path.
- Run `lake exe cache get` (or `just cache`) when Mathlib's compiled artifacts are needed.
- The default `just` recipe builds both the teaching PDF and Lean modules. For Lean-only edits, use `lake build`.

## Editing conventions

- Preserve the accessible, step-by-step style of the teaching proofs. Prefer readable intermediate facts over unnecessarily compressed tactic scripts.
- Follow nearby Lean formatting and naming conventions; files currently use `import Mathlib` and tactic-mode proofs.
- Complete proofs without introducing `sorry` or new axioms unless explicitly requested for an exercise.
- Check changed Lean files with Lean; compilation is the primary proof validation.
- Keep changes focused. Do not upgrade Lean, Mathlib, or lockfiles unless the task requires it.
- Do not edit `.lake/` dependencies or build output. Avoid incidental changes to generated LaTeX files and PDFs.
