"""
Fixer that changes input(...) into eval(input(...)).
"""

from _typeshed import Incomplete
from typing import ClassVar, Literal

from .. import fixer_base

context: Incomplete

class FixInput(fixer_base.BaseFix):
    BM_compatible: ClassVar[Literal[True]]
    PATTERN: ClassVar[str]
    def transform(self, node, results): ...
