# Retained negative case

`comparator-4884.json` is copied unchanged from Open Formal Workflows commit
`3300a105864c34ed97ad30a182496b3d570e0039`, `pilot/comparator-outcome.json`.
It records an invocation error, parsing not attempted, and policy not evaluated.
The regression exercises this distinction through the current controller with a simulated
process failure. It does not rerun the historical proof or reinterpret its terminal output.
