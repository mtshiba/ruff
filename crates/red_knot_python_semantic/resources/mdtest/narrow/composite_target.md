# Narrowing for composite targets

## Member access

```py
class C:
    def __init__(self):
        self.x: int | None = None
        self.y: int | None = None

c = C()
reveal_type(c.x)  # revealed: int | None
if c.x is not None:
    reveal_type(c.x)  # revealed: int
    reveal_type(c.y)  # revealed: int | None

if c.x is not None:
    def _():
        reveal_type(c.x)  # revealed: Unknown | int | None

def _():
    if c.x is not None:
        reveal_type(c.x)  # revealed: (Unknown & ~None) | int
```

## Subscript

### Number subscript

```py
def _(t1: tuple[int | None, int | None], t2: tuple[int, int] | tuple[None, None]):
    if t1[0] is not None:
        reveal_type(t1[0])  # revealed: int
        reveal_type(t1[1])  # revealed: int | None

    n = 0
    if t1[n] is not None:
        # Non-literal subscript narrowing are currently not supported, as well as mypy, pyright
        reveal_type(t1[0])  # revealed: int | None
        reveal_type(t1[n])  # revealed: int | None
        reveal_type(t1[1])  # revealed: int | None

    if t2[0] is not None:
        # TODO: should be int
        reveal_type(t2[0])  # revealed: @Todo(Support for `typing.TypeVar` instances in type expressions) & ~None
        # TODO: should be int
        reveal_type(t2[1])  # revealed: @Todo(Support for `typing.TypeVar` instances in type expressions)
```

### String subscript

```py
# TODO: no errors
# error: [unsupported-operator] "Operator `|` is unsupported between objects of type `Literal[str]` and `None`"
def _(d: dict[str, str | None]):
    if d["a"] is not None:
        # should be str
        reveal_type(d["a"])  # revealed: @Todo(specialized non-generic class) & ~None
        # should be str | None
        reveal_type(d["b"])  # revealed: @Todo(specialized non-generic class)
```

## Complex target

```py
class C:
    def __init__(self):
        self.x: tuple[int | None, int | None] = ()

c = C()
if c.x[0] is not None:
    reveal_type(c.x[0])  # revealed: int
```
