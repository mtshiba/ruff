# Analysis: Query Cycle Panic in PR #22633 (Lambda Callable Type Context)

## Summary

PR #22633 introduces eager inference of lambda bodies as part of their parent scope's
inference (similar to how comprehensions work). This creates a new dependency edge in
the query graph: `infer_definition_types` for a definition containing a lambda now
transitively depends on all names referenced in the lambda body. When these names form
a circular dependency chain involving unpacking assignments, the Salsa fixed-point
iteration fails to converge and panics after 200 iterations.

## Reproducer

```python
lambda: name_4                          # (A) standalone lambda referencing name_4

@(lambda: name_5)                       # (B) decorator lambda referencing name_5
class name_1:
    pass

name_2 = [lambda: name_4, name_1]       # (C) list containing lambda->name_4 and name_1

if name_2:
    @(*name_2,)                          # (D) decorator unpacking name_2
    class name_3:
        pass
    assert name_3

@(lambda: name_3)                       # (E) decorator lambda referencing name_3
class name_4[*name_2](0, name_1=name_3):  # (F) class with type params and bases
    pass

try:
    [name_5, name_4] = *name_4, = name_4  # (G) chained unpack assignment
except:
    pass
else:
    async def name_4():                    # (H) redefines name_4
        pass

for name_3 in name_4:                      # (I) redefines name_3, iterates name_4
    pass
```

All elements are necessary for the panic. Removing any single one breaks the cycle or
allows convergence.

## The Cycle

The PR's key change adds `NodeWithScopeKind::Lambda` to `accepts_type_context()`, which
causes lambda body scopes to be inferred eagerly as part of their parent scope via
`infer_scope_types()`. This creates a new transitive dependency:

```
infer_definition_types(name_2 = [...])     # inferring name_2's definition
  → infer_lambda_expression(lambda: name_4)  # eagerly infer lambda body
    → infer_scope_types(lambda body scope)
      → infer_expression(name_4)             # lambda body references name_4
        → place_by_id(name_4)                # lookup name_4's type
          → infer_definition_types(name_4 class def)  # definition (F)
            → infer_definition_types(name_4 unpack)   # definition (G)
              → infer_unpack_types([name_5, name_4] = *name_4, = name_4)
                → infer_expression_types(name_4 value)
                  → infer_definition_types(...)
                    → ... → place_by_id(name_4)  # CYCLE BACK
```

### Why it oscillates (does not converge)

The fixed-point machinery works by:
1. Starting with `Type::Divergent` for all types in the cycle
2. Re-executing queries with previous results
3. Applying `cycle_normalized()` which unions previous and current types
4. Repeating until types stabilize

The problem involves multiple interacting cycle participants across different query
types (`infer_definition_types`, `infer_scope_types_impl`, `infer_unpack_types`,
`infer_expression_types_impl`, `place_by_id`). The cycle heads listed in the backtrace
are:

```
place_by_id(Id(2400)) -> iteration = 200
infer_expression_type_impl(Id(1800)) -> iteration = 200
infer_expression_type_impl(Id(1801)) -> iteration = 200
infer_definition_types(Id(1402)) -> iteration = 200
infer_definition_types(Id(1404)) -> iteration = 200
```

The oscillation likely occurs because:

1. **Multi-level nesting of cycle recovery**: The lambda body scope inference
   (`infer_scope_types_impl`) participates in the cycle with its own `cycle_initial`
   and `cycle_fn`. When this is nested inside `infer_definition_types` (which also
   has its own cycle recovery), the two levels of cycle normalization interact in
   ways that prevent convergence.

2. **The chained assignment `[name_5, name_4] = *name_4, = name_4`**: This creates
   an `infer_unpack_types` query (yet another cycle participant with its own recovery).
   The unpack reads `name_4`'s value which depends on the class definition, which
   depends on the lambda body, which depends on `name_4` again. Each iteration,
   the unpack produces different unpacked types because the input type keeps changing.

3. **Multiple definitions of `name_4`**: `name_4` has at least 3 definitions:
   - The class definition (F)
   - The unpack target in try block (G)
   - The async function in else block (H)

   The `place_by_id` query must union these. The class definition itself depends on
   `name_3` (via decorator and base classes), and `name_3` depends on `name_2` (via
   the `@(*name_2,)` decorator), and `name_2` contains `lambda: name_4`. This creates
   a long dependency chain where type changes propagate through multiple levels before
   coming back, and the union at each level means the type keeps growing or oscillating
   between representations.

4. **`function_like_callable` return type changes**: Before the PR, the lambda expression
   type was always `() -> Unknown`. After the PR, it becomes `() -> <body_type>` where
   `<body_type>` depends on the lambda body's evaluation. When the body references a
   name involved in a cycle, the body type changes on each iteration, causing the
   lambda's type to change, which causes the containing list type to change, which
   causes downstream definitions to change, and so on without convergence.

## Root Cause

The fundamental issue is that **eagerly inferring lambda bodies creates a new category
of dependency edges** that can form cycles through name references in lambda bodies.
Unlike comprehensions (which typically iterate over existing values), lambda bodies
can contain arbitrary name references that may not yet be resolved.

The current cycle recovery infrastructure assumes that each query's `cycle_normalized`
function produces a monotonically widening type (via union). But when a lambda body
type feeds back into its own definition chain through multiple intermediate queries,
the type can oscillate because:

- The `function_like_callable` wrapper around the body type means that "previous union
  current" at the `DefinitionInference` level may produce a union of two different
  callable types with different return types
- This union then propagates as the element type of a list (`name_2`)
- Which propagates through the decorator chain to `name_3` and back to `name_4`
- Each propagation step may create new intermediate types that don't simplify

## Potential Fixes

1. **Don't eagerly infer lambda bodies that reference names from the enclosing scope**:
   Fall back to `Type::unknown()` return type when the lambda body would create a cycle.
   This could be detected by checking if any name in the lambda body is currently being
   inferred.

2. **Add lambda-specific cycle recovery**: When a `function_like_callable` type is
   involved in cycle normalization, avoid unioning callable types with different return
   types from the same lambda definition (similar to how `FunctionLiteral` types are
   handled).

3. **Limit the scope of eager lambda inference**: Only eagerly infer lambda bodies when
   there's an actual `Callable` type context (the primary goal of the PR), rather than
   always eagerly inferring. If no type context is available, fall back to the current
   behavior of `Type::unknown()` for the return type.

4. **Break the cycle at `infer_scope_types` level**: When `infer_scope_types` for a
   lambda body scope detects it's being called as part of a cycle, return a fallback
   result instead of participating in fixed-point iteration.

Option 3 is likely the most practical: it achieves the PR's goal (better inference with
`Callable` context) while avoiding the cycle problem for cases where no type context
exists anyway.
