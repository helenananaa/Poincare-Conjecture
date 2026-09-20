# Sard–Moreira source provenance

Upstream: https://github.com/urkud/SardMoreira.git

Pinned revision: `14bc8a1eeaedb14f9ae95e125c95a5eb4f47f8c5`

License: Apache-2.0; see LICENSE. Original source headers are retained.

This directory contains the 23-source import closure needed for MainTheorem, ported to the project-pinned Lean 4.32.1 / Mathlib environment. Unimported upstream scratch and unused compatibility files were not copied.

The added ordinary Sard wrappers in MainTheorem concern ambient C-infinity maps or maps on open sets. They do not claim the original generic closed-model-range within-derivative statement without further work.

Independent compilation and a module-wide transitive axiom audit of all 692 declarations passed using only propext, Classical.choice, and Quot.sound. This is an imported open-source formalization with local compatibility repairs, not a claim of authorship of the upstream mathematical proof.
