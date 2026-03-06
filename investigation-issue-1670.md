# Investigation: Non-deterministic Diagnostics (ty issue #1670)

## Summary

Running ty against sympy reveals **129 diagnostic locations** that are non-deterministic across
multi-threaded runs. The non-determinism manifests in two distinct ways:

1. **Diagnostics that appear or disappear entirely** depending on the run
1. **Union type element ordering** that varies between runs (cosmetic but affects output stability)

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

| Run             | Diagnostic locations | Flaky locs present (of 129) |
| --------------- | -------------------- | --------------------------- |
| Single-threaded | 17,454               | 93                          |
| Multi #1        | 17,502               | 128                         |
| Multi #2        | 17,410               | 37                          |
| Multi #3        | 17,358               | 0                           |
| Multi #4        | 17,504               | 129                         |
| Multi #5        | 17,452               | 92                          |

## Detailed Flaky Diagnostic Classification

### Group A: Matrix `unsupported-operator` (59 locations, all correct in single-threaded)

**Python code pattern:**

```python
m + m  # where m: MutableDenseMatrix (or MatrixBase, Self, etc.)
```

**Expected type:** `MutableDenseMatrix.__add__` is defined via `MatrixBase.__add__`, which is
decorated with `@call_highest_priority('__radd__')`. ty should recognize this operator.

**Actual behavior (single-threaded):** ty reports `unsupported-operator` because the
`@call_highest_priority` decorator wraps `__add__` in `binary_op_wrapper`, and ty's analysis of
the wrapper body fails to produce a valid `__add__` signature. The result type is `Unknown`.

This is a **pre-existing bug** unrelated to non-determinism: `MutableDenseMatrix + MutableDenseMatrix`
always reports `unsupported-operator` in single-threaded mode. The flakiness is that in some
multi-threaded runs this error **disappears**, because cycle recovery provides a different
(accidentally more permissive) type for the operator.

**Why it disappears in some multi-threaded runs:** When a cycle is detected via a different entry
point, the `is_redundant_with` check (relation.rs:301, `cycle_initial=true`) causes some union
simplifications to return `true` (i.e., "this type is redundant") when they would normally return
`false`. This can cause the type checker to see a simpler type for the decorated method, which
happens to pass the operator check.

### Group B: `call_highest_priority` type leaking (8 locations, all correct in single-threaded)

**Python code pattern:**

```python
# matrixbase.py:2957 - _eval_pow_by_cayley returns Self, but cycle introduces wider type
def _eval_pow_by_cayley(self, exp: int) -> Self:
    ...
    return ans  # ty infers: Self | T2'return@call_highest_priority | T1'return@call_highest_priority | Unknown

# matrixbase.py:3310 - __rsub__ uses operator that leaks wrapper types
def __rsub__(self, a: MatrixBase) -> MatrixBase:
    return (-self) + a  # Both operands: MatrixBase, but operator has leaked types

# eigen.py:1202 - subtraction result has leaked type without .pow attribute
mat_cache[(val, pow)] = (mat - val*M.eye(M.rows)).pow(pow)  # T2'return | T1'return has no .pow
```

**Expected type:** The return type of decorated methods should be the annotated type (e.g., `Self`,
`MatrixBase`), not the union with decorator TypeVar artifacts.

**Root cause in ty:** When `call_highest_priority` wraps a method, ty infers the return type of
`binary_op_wrapper` as a union of both branches:

1. `func(self, other)` → `T3` (the declared return type)
1. `f(self)` where `f = getattr(other, method_name, None)` → `T1'return@call_highest_priority`

These TypeVar-like types should be resolved to concrete types but remain unresolved because:

- `T1` and `T2` in the decorator are bound at `call_highest_priority`'s scope

- The `@wraps(func)` annotation tells ty to preserve the original signature, but ty still
    analyzes the body of `binary_op_wrapper` and unions both return paths

- In a cycle, `Type::cycle_recover` (types.rs:950) accumulates these intermediate types:

    ```rust
    UnionType::from_elements_cycle_recovery(db, [previous, self])
    ```

### Group C: Matrix `__pow__` wider union (4 locations, all correct in single-threaded)

**Python code pattern:**

```python
B = A - Matrix.eye(4) * I
assert (B**2).rank() == 2   # error: MatrixExpr has no attribute rank
```

**Expected type:** `B**2` should return `MatrixBase | MatrixExpr` (per `MatrixBase.__pow__`
annotation). `MatrixExpr` does lack `.rank()`, so this is a **correct diagnostic** that
sometimes disappears.

**Why it disappears:** Same mechanism as Group A — cycle recovery via a different entry point
causes `is_redundant_with` to return `true` for some union elements, simplifying the type and
accidentally suppressing the error.

### Group D: Matrix other operators (9 locations, all correct in single-threaded)

Same root cause as Group A but with types like `MatrixBase`, `Unknown | MatrixBase`, etc.
instead of `MutableDenseMatrix`.

### Group E: `sympify` overload union (36 locations, all FALSE POSITIVES)

**Python code pattern:**

```python
# In Application.__new__ (function.py:300):
args = list(map(sympify, args))      # args: *args of __new__, type Unknown
cls.eval(*args)                       # calls e.g. binomial.eval(n, k)

# In binomial.eval (factorials.py:966-968):
def eval(cls, n, k):                  # n, k come from map(sympify, args)
    n, k = map(sympify, (n, k))       # sympify called again
    n_nonneg = n.is_nonnegative       # ERROR if n has type int|float|complex
```

**Expected type for `map(sympify, (n, k))`:**

- When `n`, `k` have type `Unknown`: all sympify overloads match → return `Basic | int | float | complex | Any`
- When `n`, `k` have type `Basic` (from the first `map(sympify, args)` in `__new__`): only
    the `sympify(a: Tbasic) -> Tbasic` and `sympify(a: Any) -> Basic` overloads match → return `Basic`

**Single-threaded result:** `n` has type `Basic` → `sympify(n)` returns `Basic` → `n.is_nonnegative` is valid.

**Some multi-threaded results:** `n` has type `Basic | int | float | complex | Any` →
`n.is_nonnegative` errors because `int`, `float`, `complex` don't have `is_nonnegative`.

**Root cause in ty — the cycle and `is_redundant_with`:**

The cycle is: `Application.__new__` → `cls.eval(*args)` → eval body creates new instances →
`Application.__new__` again.

1. In single-threaded, the cycle always enters at `Application.__new__`. The first call to
    `map(sympify, args)` with `Unknown` args produces `list[Basic | int | float | complex | Any]`.
    However, `is_redundant_with` simplification during union building removes `int`, `float`,
    `complex` (they are subtypes of or redundant with `Basic`/`Any`), yielding `list[Basic]`.

1. In multi-threaded, the cycle can enter at `eval` instead. The `n`, `k` parameters get the
    cycle initial type `Unknown` (from `Type::divergent`). When `map(sympify, (n, k))` is called
    with `Unknown` args, the same overload union is produced. But this time, `is_redundant_with`
    encounters a Salsa cycle (because checking type relations requires resolving types that are
    part of the same cycle), and returns `true` (its `cycle_initial` value) for **different**
    pairs of types than in the single-threaded case, causing different elements to survive.

**The key code:** `relation.rs:301`:

```rust
#[salsa::tracked(cycle_initial=|_, _, _, _| true, heap_size=ruff_memory_usage::heap_size)]
fn is_redundant_with_impl<'db>(db: &'db dyn Db, self_ty: Type<'db>, other: Type<'db>) -> bool {
    self_ty.has_relation_to(db, other, InferableTypeVars::None, TypeRelation::Redundancy)
         .is_always_satisfied(db)
}
```

When a cycle is detected during `is_redundant_with`, it returns `true` ("yes, this type is
redundant"). This means:

- If `is_redundant_with(int, Basic)` hits a cycle → returns `true` → `int` is filtered out of
    the union → result is `Basic` (correct)
- If `is_redundant_with(int, Basic)` does NOT hit a cycle → actually checks subtyping →
    `int` is not a subtype of `Basic` → returns `false` → `int` stays in the union →
    result is `Basic | int | ...` (over-wide)

Whether the cycle is hit depends on the execution order of concurrent queries, which varies
between threads.

### Group F: `Self@` type mismatches (3 locations, all correct in single-threaded)

**Python code pattern:**

```python
def add(self, b: Self) -> Self:
    return self + b   # Both operands: Self@add, unsupported operator
```

Same root cause as Group A — `__add__` is decorated, operator not recognized.

### Group G: Other union-related (5 locations, all correct in single-threaded)

Various matrix operation results with `Unknown` or `MatrixBase | Expr | Unknown` types.
Same root cause as Groups A/B.

## Root Cause Summary

There is a single fundamental mechanism causing all non-determinism:

**`is_redundant_with_impl` (relation.rs:301) has `cycle_initial=true`, and which queries
encounter cycles depends on thread execution order.**

This affects the system in two ways:

1. **Union simplification varies** (Groups A-D, F-G): When building unions during cycle recovery,
    `is_redundant_with` may or may not hit a cycle for each pair of types. The `true` cycle-initial
    value means "this type IS redundant" — so when a cycle is hit, extra elements get filtered out,
    producing a simpler (possibly incorrect) union. When no cycle is hit, extra elements survive,
    producing a wider (possibly incorrect) union.

1. **Overload resolution varies** (Group E): The `sympify` overload resolution produces different
    return types because the argument types it receives vary (due to the same `is_redundant_with`
    mechanism affecting upstream union building).

## Affected Code Locations in ty

| File                 | Lines       | Role                                                               |
| -------------------- | ----------- | ------------------------------------------------------------------ |
| `types/relation.rs`  | 300-317     | `is_redundant_with` with `cycle_initial=true` — **the root cause** |
| `types/builder.rs`   | 714-717     | Union builder calls `is_redundant_with` to filter elements         |
| `types.rs`           | 900-955     | `Type::cycle_recover` unions previous and current iteration types  |
| `types.rs`           | 12327-12339 | `from_elements_cycle_recovery` builds union during recovery        |
| `types/call/bind.rs` | 575-602     | `Bindings::return_type` unions return types of matching overloads  |
| `types/call/bind.rs` | 2774-2789   | `CallableBinding::return_type` selects first matching overload     |

## Potential Fix Directions

1. **Change `is_redundant_with` cycle initial to `false`**: Using `cycle_initial=false` means
    "when in a cycle, assume types are NOT redundant." This is more conservative — no elements
    get accidentally filtered — but may cause unions to be wider than necessary.
    Trade-off: deterministic but potentially wider types.

1. **Normalize union types during cycle recovery**: Sort union elements in
    `from_elements_cycle_recovery` to ensure deterministic ordering. This only fixes the
    cosmetic ordering issue (Group E ordering) but not the presence/absence issue.

1. **Decouple `is_redundant_with` from Salsa cycle detection**: Instead of using Salsa's
    cycle detection for `is_redundant_with`, implement a separate mechanism that doesn't
    depend on query execution order. For example, use a structural comparison that doesn't
    trigger further type inference queries.

1. **Improve decorator type inference**: Ensure that `@wraps(func)` causes ty to use the
    wrapped function's signature directly, without analyzing the wrapper body. This would
    fix Groups A and B by preventing `T'return@call_highest_priority` from appearing in types.
