# Workstream contract — fixed-projection ultraweak and order infrastructure

**Read and obey `docs/development/SAKAI_DESIGN_CONTRACT.md` and the authoritative Sak-AI specifications it references. These requirements govern this workstream. Do not introduce designs inconsistent with them.**

Baseline: `162271ac17505779d1b2345ef5d4de434bf82c49` plus the coordination commit
that contains this contract.

Objective: audit the pinned/current Mathlib, Sak-AI, and read-only original LeanOA APIs needed to
pass fixed left/right/two-sided multiplication and order inequalities through specified-ultraweak
limits. Kernel-check the smallest missing reusable theorem, if any.

Own only a scratch proof/report unless a genuinely missing, general, recognizable theorem has a
clear production home below spectral theory. Any production proposal must preserve existing
specified-predual interfaces and use the weakest natural assumptions.

Required checks: fixed multiplication continuity; congruence of `Tendsto`; ultraweak closedness of
the positive cone and order intervals; limit preservation of `≤`; projection multiplication and
support implications. State exactly what already exists and what is only a convenient derived
composition.

Forbidden: norm substitutes for ultraweak arguments; spectral-specific copies of general topology
facts; redesigning predual instances; editing Verso/shared coordination; pushing.

Commit the isolated result and report focused validation, Mathlib overlap, and upstream candidates.
