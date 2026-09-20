# PBW provenance

The ten supporting files were ported from Tau Ceti at the revision recorded in
UPSTREAM_PIN. Their original notices remain in place; LICENSE is copied from the
saved upstream checkout. The port targets the pinned Lean 4.32.1.

PolyAction.lean and Basis.lean are project-local additions constructed in the
Grok h18/h19 proof tasks and combined before the Luna l03 review. They must not
be described as unmodified upstream results. Luna l03 required no further proof
edits. The controller rebuilt all twelve sources independently and audited eleven
key declarations before this integration. Only standard axioms were found.
