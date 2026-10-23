# Packaging validation (2026-10-23)

- All 284 manuscript sources match the validated source snapshot dated 2026-09-29.
- All 881 required supporting modules are present, byte for byte, in stochastic-analysis-lean at commit `0cb33378176178d269f53a4dada439f8ecd3bf5e`.
- The combined manuscript import and axiom audit passed using previously compiled proof objects: 1,402 theorem declarations, with only `propext`, `Classical.choice`, and `Quot.sound`.
- The supporting library is a pinned Lake dependency; its sources are not included here.

This packaging validation reused existing compiled proof objects. It was not a fresh rebuild of every proof. Build from source using the commands in README.md. Local caches and dependency links are excluded from Git.
