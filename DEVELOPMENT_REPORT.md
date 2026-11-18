# Development Report: Vampire Rust Bindings Enhancement

## 1. Objectives
The primary goal was to enhance the `vampire` crate to support modern TPTP features and provide a stable foundation for a persistent Logical API. Key features included:
- **TFF Sort Support**: Native handling of multi-sorted logic.
- **Interpreted Arithmetic**: Integration with Vampire's built-in theory symbols (integers and reals).
- **CNF Clausification**: Ability to extract simplified clauses from complex formulas.
- **Persistent Stability**: Allowing repeated solver calls within a single long-running process.

## 2. Encountered Problems

### A. Process-Global Static State
Vampire was originally designed as a process-per-run CLI tool. It relies heavily on global static variables for:
- **Hash-Consing Caches**: Shared terms and literals.
- **Signature Singletons**: Built-in sorts like `$int` and `$real` are initialized as static objects.
- **Saturation Debris**: The proof engine leaves behind state (ordering diagrams, statistics) that is not fully re-entrant.

**Symptoms**: SIGSEGV during the second or third proof attempt in a single process, or corruption of result data.

### B. FFI Boundary Fragility
- **Vector Alignment**: Using `reinterpret_cast` to treat `std::vector<Derived*>` as `std::vector<Base*>` caused memory misalignment and crashes.
- **Value Type Persistence**: Vampire's `TermList` is an 8-byte value type (similar to a pointer). Passing it to Rust as a raw ID and back often resulted in invalid bit-patterns if not handled via a stable heap address.

### C. API-Layer TFF Instability
Despite correct mapping of TFF symbols and sorts, the underlying Vampire C++ kernel frequently triggered a `signal 11` (SIGSEGV) during the saturation of typed formulas. This appears to be a fundamental limitation or bug in the specific version of the Vampire `Api` layer when used for multi-sorted problems.

## 3. Implemented Solutions

### 1. Robust Clausification (Verified)
We implemented a standalone `clausify()` method using the `Shell::NewCNF` engine. Unlike the basic `CNF` class, `NewCNF` handles complex connectives like `IFF` and `XOR` and preserves sort information. This feature is **fully stable** and verified by the `test_clausification` suite.

### 2. Process Isolation via `fork()`
To protect the persistent parent process (the Logical API) from solver crashes, we implemented `solve_isolated()`.
- **Mechanism**: It uses `fork()` to create a disposable memory clone. The solver runs in the child, and the result is serialized back to the parent via an anonymous pipe.
- **Benefit**: If Vampire segfaults or leaks memory, the parent process remains 100% clean and can continue its execution.

### 3. Cache Isolation Logic
In the C++ layer, we enhanced `prepareForNextProof` to specifically target saturation-engine caches:
- `Term::resetStaticCaches()`
- `AtomicSort::resetStaticCaches()`
- `InferenceStore::instance()->reset()`
These calls allow the `Signature` (and thus your Rust handles) to remain alive while clearing the engine's internal debris.

### 4. Safe FFI Architecture
- **Manual Conversions**: All vector passing now uses explicit element-by-element loops to ensure C++ ABI compatibility.
- **Heap Allocation**: `vampire_term_t` handles now point to stable heap-allocated `TermList` objects, preventing bit-pattern corruption across the FFI boundary.

## 4. Current Project State

| Feature | Status | Verification |
|---------|--------|--------------|
| **FOF Proving** | Stable (Isolated) | `solve_isolated()` prevents parent crashes. |
| **TFF Sorts** | Implemented | API signatures mapped; unstable in saturation. |
| **Arithmetic** | Implemented | 30+ theory symbols mapped; unstable in saturation. |
| **Clausification** | **Fully Stable** | Verified via `test_clausification`. |
| **TPTP Parser** | Functional | Supports FOF and TFF basics. |

## 5. Recommendations for Future Use
For the implementing project (Logical API):
1. **Always use `solve_isolated()`** for proof attempts. It provides the necessary fault tolerance.
2. **Use `clausify()`** for formula normalization within the main process, as it is stable.
3. **Avoid `vampire_reset()`**. Rely on the automatic per-proof reset to keep your `Predicate` and `Function` handles valid for the lifetime of your API.
