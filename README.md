# FinSc‑Metric‑Substrate

The **FinSc‑Metric‑Substrate** library implements the metric‑substrate algebra that underpins the Finite‑Science ecosystem. It provides the geometric substrate, metric signatures, and primitive linear‑state structures required by higher‑level physics packages.

## Overview
- **Core types** – `Pixel`, `Spread`, `UniverseState`, `Vexel`, `DepMaxel`, and supporting witnesses.
- **Stage 0** – Strict (non‑coinductive) definitions forming the foundation for downstream modules.
- **Stage 1** – Coinductive, stream‑based abstractions (`Carrier.Vexel`, `Carrier.Maxel`, `Carrier.Boxel`, `Carrier.BalanceArray`, `UnixelFraction`, `QuadStream`, etc.) that model the physical universe.
- **Reflect** – Compile‑time invariant auditors (`SubstrateAuditor.idr`) expressed as `%macro` elaborator macros to guarantee constructivist physical laws.

## Directory layout
```
FinSc-Metric-Substrate/
├─ .git/                     # VCS metadata
├─ .gitignore                # Ignores generated artefacts (build/, *.ttc, *.ttm, *.o, *.so, *.dyn)
├─ FinSc-Metric-Substrate.ipkg   # Idris package descriptor
├─ src/                      # Source code
│   ├─ Core.idr
│   ├─ MetricSubstrate.idr
│   ├─ Reflect/              # Auditor macros
│   ├─ Stage0/               # Strict core types
│   └─ Stage1/               # Coinductive physics layer
└─ build/                    # Temporary build artefacts (ignored)
```

## Building & installing
```bash
# Run inside the fedora toolbox as required by the project
toolbox run -c fedora-toolbox-44 /var/home/justin/.local/bin/idris2 \
  --install FinSc-Metric-Substrate/FinSc-Metric-Substrate.ipkg
```
The command compiles the library and makes it available to other packages via `import FinSc.Metric.Substrate.*`.

## Quick usage (Idris REPL)
```idris
import FinSc.Metric.Substrate.Core
import FinSc.Metric.Substrate.Stage1.UnixelFraction

-- create a simple universe state
let u0 = emptyUniverseState
let u1 = addMatter u0 [BoxInt 1, BoxInt 2]
printLn u1
```

## Testing & verification
The companion wiki (`FinSc-Metric-Substrate-Wiki`) contains Idris test suites that verify algebraic properties, generate Lean 4/Coq export files, and run compile‑time auditors. See its README for detailed instructions.

## Contributing
1. Add new modules under `src/` following the existing naming conventions.
2. Keep all invariants auditable via macros in `src/Reflect/`.
3. Run the full ecosystem build (`./build-all.sh`) to ensure no regressions.

---
*Generated automatically by Antigravity.*
