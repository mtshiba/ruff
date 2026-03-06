# Investigation: Non-deterministic Diagnostics (ty issue #1670)

## Summary

Running ty against sympy reveals **129 diagnostic locations** that are non-deterministic across
multi-threaded runs. The non-determinism manifests in two distinct ways:

1. **Diagnostics that appear or disappear entirely** depending on the run
2. **Union type element ordering** that varies between runs (cosmetic but affects output stability)

Using single-threaded execution as ground truth, we identified:
- **93 locations** where diagnostics are correct (present in single-threaded) but sometimes
  missing in multi-threaded runs (false negatives)
- **36 locations** where diagnostics are spurious (absent in single-threaded) but sometimes
  appear in multi-threaded runs (false positives)

## Methodology

- Built ty in debug mode from current main branch
- Set up sympy via `scripts/setup_primer_project.py`
- Ran ty 1x single-threaded (`RAYON_NUM_THREADS=1`) and 5x multi-threaded
- Extracted diagnostic locations and compared presence/absence across runs

### Raw numbers

| Run | Diagnostic locations | Flaky locs present (of 129) |
|-----|--------------------|-----------------------------|
| Single-threaded | 17,454 | 93 |
| Multi #1 | 17,502 | 128 |
| Multi #2 | 17,410 | 37 |
| Multi #3 | 17,358 | 0 |
| Multi #4 | 17,504 | 129 |
| Multi #5 | 17,452 | 92 |

## Root Cause Analysis

### Pattern 1: `call_highest_priority` decorator (primary cause, ~195 flaky locations)

The `call_highest_priority` decorator in sympy wraps binary operators (`__add__`, `__sub__`,
`__mul__`, `__pow__`, etc.) with a function that may dispatch to a different method based on
`_op_priority`:

```python
def binary_op_wrapper(self: T1, other: T2) -> T3:
    if hasattr(other, '_op_priority'):
        if other._op_priority > self._op_priority:
            f = getattr(other, method_name, None)
            if f is not None:
                return f(self)  # returns T2's method return type
    return func(self, other)  # returns T3
```

ty infers the return type as a union of both branches. In a cycle (e.g., `MatrixBase.__mul__`
calling `self._new(...)` which calls back into matrix operations), the cycle recovery combines
types from different iterations. The type `T2'return@call_highest_priority | T1'return@call_highest_priority`
leaks into the inferred type of matrix operations.

**Example:** `(B**2).rank()` where `B` is a `MatrixBase`:
- Single-threaded / some multi-threaded runs: `B**2` has type `MatrixBase` → no error
- Other multi-threaded runs: `B**2` has type `MatrixBase | MatrixExpr | Unknown` →
  error because `MatrixExpr` has no `rank` attribute

The specific diagnostics affected:

```
error[invalid-return-type]: expected `Self@_eval_pow_by_cayley`, found
    `Self@_eval_pow_by_cayley | T2'return@call_highest_priority | T1'return@call_highest_priority | Unknown`

error[unresolved-attribute]: Attribute `rank` is not defined on `MatrixExpr`
    in union `MatrixBase | MatrixExpr | Unknown`

error[unsupported-operator]: Unsupported `-` operation
    (operands: `MatrixBase` and `MatrixBase | Expr | Unknown`)

error[unresolved-attribute]: Object of type
    `T2'return@call_highest_priority | T1'return@call_highest_priority` has no attribute `pow`
```

### Pattern 2: `sympify` overload resolution (secondary cause, ~36 false-positive locations)

`sympify` has multiple overloads:
```python
def sympify(a: int, ...) -> Integer: ...
def sympify(a: float, ...) -> Float: ...
def sympify(a: Expr | complex, ...) -> Expr: ...
def sympify(a: Tbasic, ...) -> Tbasic: ...
def sympify(a: Any, ...) -> Basic: ...
```

When called as `map(sympify, (n, k))`, the inferred return type depends on the inferred types
of `n` and `k`. In some multi-threaded runs, the argument types are wider (due to cycle recovery
effects upstream), causing ty to union together return types from multiple overloads, producing
`Basic | int | float | complex | Any` instead of just `Basic`.

This causes false-positive errors like:
```
error[unresolved-attribute]: Attribute `is_nonnegative` is not defined on `int`, `float`, `complex`
    in union `Basic | int | float | complex | Any`
```

### Pattern 3: Union element ordering (cosmetic, ~7 locations)

The same diagnostics appear but with different union element ordering:
```
run1: union `Basic | int | float | complex | Any`
run2: union `Any | Basic | int | float | complex`
```

This is purely cosmetic and does not affect correctness, but breaks baseline comparisons.

## Mechanism

The non-determinism occurs because:

1. Salsa (the incremental computation framework) executes queries in parallel across threads
2. When a **cycle** is detected, the entry point depends on which thread reaches the cycle first
3. The `cycle_initial` value is `Type::divergent(id)`, and the cycle recovery function
   (`Type::cycle_recover`) unions together the previous and current iteration types
4. Different cycle entry points lead to different intermediate types being unioned together
5. Even though the fixpoint iteration should converge, the **path to convergence** differs,
   and the union accumulates different type elements along different paths

Specifically, in `Type::cycle_recover` (types.rs:900-955):
```rust
UnionType::from_elements_cycle_recovery(db, [previous, self])
```
This unions the previous iteration's type with the current one. If the cycle is entered from
a different query, `previous` contains different type elements, leading to a wider union that
may include types like `T2'return@call_highest_priority` that wouldn't appear if the cycle
were entered from the "correct" starting point.

## Affected Files in sympy

The flaky diagnostics concentrate in:
- `sympy/matrices/` (37 test files + 13 source files) — matrix arithmetic operators
- `sympy/parsing/autolev/` (10 files) — uses matrix operations
- `sympy/polys/` (8 files) — uses `sympify`
- `sympy/functions/combinatorial/` (7 files) — uses `sympify`
- `sympy/tensor/` (8 files) — uses `sympify` and matrix operations
- `sympy/physics/` (various, 15 files) — uses matrix operations

## Potential Fix Directions

1. **Normalize union types during cycle recovery**: Sort union elements in
   `UnionType::from_elements_cycle_recovery` to ensure deterministic ordering.
   This fixes Pattern 3 but not Patterns 1-2.

2. **Ensure cycle convergence produces the same fixpoint regardless of entry point**:
   The fundamental issue is that `Type::cycle_recover` accumulates different union elements
   depending on which intermediate types were computed. A possible approach:
   - During cycle recovery, avoid accumulating intermediate decorator wrapper types
     (like `T1'return@call_highest_priority`) that are artifacts of the computation path
   - Or: ensure that `from_elements_cycle_recovery` simplifies unions more aggressively
     to remove redundant/subsumed types

3. **Improve decorator type inference**: The `call_highest_priority` decorator's return type
   should ideally be simplified. The `T1` and `T2` type variables should be resolved to
   concrete types rather than left as unresolved type variable references in the final type.
