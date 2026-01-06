# This is a regression test for https://github.com/astral-sh/ty/issues/2360

from collections.abc import Iterable, Mapping
from typing import Any

type AnyComponent = "Component[Any]"
type Nested[T] = Iterable[Nested[T]] | Mapping[Any, Nested[T]]


class Component[T: Iterable[Nested[AnyComponent]] | Mapping[Any, Nested[AnyComponent]]]:
    pass


dict[str, list[AnyComponent]]().get("x", [])
