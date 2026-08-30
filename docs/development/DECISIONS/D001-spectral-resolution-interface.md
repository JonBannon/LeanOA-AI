# D001 — defer the set-indexed spectral-resolution interface

Status: Proposed / RED guardrail

Affected streams: architecture, Mathlib reconnaissance, spectral theorem clusters, Verso

Relevant Sak-AI specification: root `ARCHITECTURE.md`, `STYLE_GUIDE.md` generality and reuse rules,
`CONTINUATION.md`, and `REVIEW_QUEUE.md` spectral naming audit.

## Problem

The completed finite spectral sums converge to a self-adjoint element, while the next Sakai
checkpoint is normally written as a spectral integral. A premature local projection-valued measure
or integration type could become an expensive parallel foundation.

## Alternatives considered

1. Immediately define a set-indexed projection-valued measure and an operator-valued integral.
2. Treat the existing dyadic norm limit as the public integral without a general object.
3. First add theorem-level spectral-band and tagged-sum interfaces, audit Mathlib, then choose the
   smallest object demanded by the representation and uniqueness proofs.

## Decision

Use alternative 3 during the first wave. This is a guardrail, not the final API decision.

## Reason

It creates useful kernel-checked mathematics behind stable interfaces while preserving the ability
to adopt a future Mathlib spectral-measure design. It also supplies concrete consumer signatures
against which the architecture can be judged.

## Migration consequences

No public declaration may currently claim a general spectral measure or integral. The existing
`spectralProjectionIio` name and half-line semantics remain unchanged.

## Follow-up

Resolve IQ-001 after the Mathlib audit and first theorem-cluster integration.
