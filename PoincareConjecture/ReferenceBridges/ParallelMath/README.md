# Optional, checked reference adapters

These Lean files use the original MorganTianLib and HatcherLib definitions.
They are not in the primary PoincareConjecture Lake library glob; no extra
project dependency or toolchain pin was silently added. Build the exact
reference import closure, then use the fixed-goal verifier to recheck these
files and their transitive axioms. The published report lists exact inputs,
outputs, source hashes, assumptions and unfinished geometric producers.

See `reports/parallel/math-mapreduce/README.md` and
`tools/lean_swarm/build_math_references.py` for reproduction. None of these
adapters is a proof of the full Poincare conjecture.
