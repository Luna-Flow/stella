# theory Tutorial

Use the Typst note as the narrative overview before diving into elaboration details or extending the proof language.

## Suggested Flow

1. Read the repository README and the theory API reference.
2. Start from the constructors or entry points under `doc/doc_en.typ`.
3. Validate behavior with the existing tests or examples before depending on edge-case semantics.

## Practical Guidance

- Prefer the documented entry points over internal helpers.
- Record runtime, numeric, or proof-state assumptions explicitly in downstream code.
