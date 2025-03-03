# Shadowing

## Valid (explicit) shadowing

```py
class Foo: ...
class Foo: ...

def _[Foo](x: Foo) -> Foo:
    reveal_type(Foo)  # revealed: Foo
    return x

class _[Foo]:
    reveal_type(Foo)  # revealed: Foo

reveal_type(Foo)  # revealed: Literal[Foo]

Foo: str = "foo"
reveal_type(Foo)  # revealed: Literal["foo"]

def Foo(): ...

reveal_type(Foo)  # revealed: Literal[Foo]
```

## Invalid (implicit) shadowing

```py
class Foo: ...

# error: [invalid-assignment] "Implicit shadowing of class `Foo`; annotate to make it explicit if this is intentional"
Foo = 1
reveal_type(Foo)  # revealed: Literal[Foo]

# error: [invalid-assignment] "Implicit shadowing of class `Foo`; annotate to make it explicit if this is intentional"
_ = (Foo := 2)
reveal_type(Foo)  # revealed: Literal[Foo]

# error: [invalid-assignment] "Implicit shadowing of class `Foo`; annotate to make it explicit if this is intentional"
import sys as Foo

reveal_type(Foo)  # revealed: Literal[Foo]

# error: [invalid-assignment] "Implicit shadowing of class `Foo`; annotate to make it explicit if this is intentional"
from typing import Any as Foo

reveal_type(Foo)  # revealed: Literal[Foo]

class IntIterator:
    def __next__(self) -> int:
        return 42

class IntIterable:
    def __iter__(self) -> IntIterator:
        return IntIterator()

# error: [invalid-assignment] "Implicit shadowing of class `Foo`; annotate to make it explicit if this is intentional"
for Foo in IntIterable():
    pass
reveal_type(Foo)  # revealed: Literal[Foo]

class Manager:
    def __enter__(self) -> int:
        return 42

    def __exit__(self, exc_type, exc_value, traceback): ...

# error: [invalid-assignment] "Implicit shadowing of class `Foo`; annotate to make it explicit if this is intentional"
with Manager() as Foo:
    pass
reveal_type(Foo)  # revealed: Literal[Foo]

try:
    pass
# error: [invalid-assignment] "Implicit shadowing of class `Foo`; annotate to make it explicit if this is intentional"
except Exception as Foo:
    pass
reveal_type(Foo)  # revealed: Literal[Foo]

# error: [invalid-assignment] "Implicit shadowing of class `Foo`; annotate to make it explicit if this is intentional"
type Foo = int
reveal_type(Foo)  # revealed: typing.TypeAliasType
```
