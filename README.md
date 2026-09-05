# Lean Formalization

This repository contains the Lean 4 formalization accompanying the submitted
manuscript.

## Verification

Install Lean through Elan, then run:

    lake exe cache get
    lake build

The project uses Lean and Mathlib v4.33.1. Exact dependency revisions are
recorded in `lake-manifest.json`.

## Structure

- `StateDepMOR.lean`: root import
- `StateDepMOR/Main.lean`: main formalization entry point
- `StateDepMOR/PaperStatements.lean`: correspondence between manuscript
  statements and Lean statements
- `LEANIFICATION.md`: detailed coverage and verification report

A successful `lake build` verifies the complete configured formalization.
