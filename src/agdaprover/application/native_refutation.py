"""Independent certificate replay, not a second symbolic search implementation.

The native adapter owns source/type classification and witness discovery. This
boundary checks the finite emitted recipe and its exact module bytes before the
ordinary fresh Agda validator checks the refutation. It neither finds witnesses
nor treats a classical valuation as proof authority.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from ..bridge.symbolic import SymbolicProtocolError

PROPOSAL_SCHEMA = "agdaprover.symbolic-refutation-proposal.v1"
CERTIFICATE_SCHEMA = "agdaprover.native-impossibility.v1"
FILENAME = "AgdaProverRefutation.agda"


@dataclass(frozen=True)
class _Scope:
    value: str
    parent: _Scope | None = None
    depth: int = 1

    def lookup(self, index: int) -> str:
        scope: _Scope | None = self
        while index and scope is not None:
            scope = scope.parent
            index -= 1
        if scope is None:
            raise SymbolicProtocolError("unbound native refutation recipe variable")
        return scope.value


def replay_source(proposal: dict[str, Any], goal_id: int) -> str:
    """Validate/replay a source-bound negative proposal without granting truth."""
    if (
        proposal.get("schema_version") != PROPOSAL_SCHEMA
        or proposal.get("fragment") != "pure-implication-over-abstract-types-v1"
        or proposal.get("status") != "refutation-candidate"
        or type(proposal.get("goal_id")) is not int
        or proposal["goal_id"] != goal_id
        or proposal.get("proof_authority") is not False
        or proposal.get("module_filename") != FILENAME
    ):
        raise SymbolicProtocolError("invalid native refutation proposal contract")
    count = _integer(proposal.get("parameter_count"), positive=True)
    canonical = proposal.get("canonical_type")
    if not isinstance(canonical, str) or count > len(canonical):
        raise SymbolicProtocolError("invalid native refutation parameter telescope")
    atoms: set[int] = set()
    expected = "".join(f"{{a{n} : Set}} → " for n in range(count)) + _render(
        "formula", proposal.get("formula"), count, atoms=atoms
    )
    if canonical != expected:
        raise SymbolicProtocolError("native refutation changed its classified type")
    _integer(proposal.get("assignments_checked"), positive=True)
    values = proposal.get("valuation")
    if not isinstance(values, list):
        raise SymbolicProtocolError("invalid native refutation valuation")
    valuation: dict[int, bool] = {}
    for entry in values:
        entry = _fields(entry, {"atom", "value"})
        atom = _integer(entry["atom"])
        if atom >= count or atom in valuation or type(entry["value"]) is not bool:
            raise SymbolicProtocolError("invalid native refutation valuation entry")
        valuation[atom] = entry["value"]
    if valuation.keys() != atoms:
        raise SymbolicProtocolError(
            "native refutation valuation does not cover its atoms"
        )
    applied = "h" + "".join(
        " {APUnit}" if valuation.get(n, False) else " {APEmpty}" for n in range(count)
    )
    expression = _render("expression", proposal.get("recipe"), count, _Scope(applied))
    source = "\n".join(
        (
            "{-# OPTIONS --safe --without-K #-}",
            "module AgdaProverRefutation where",
            "data APEmpty : Set where",
            "data APUnit : Set where apUnit : APUnit",
            "apAbsurd : {X : Set} → APEmpty → X",
            "apAbsurd ()",
            f"refute : ({canonical}) → APEmpty",
            f"refute = λ h → {expression}",
            "",
        )
    )
    if proposal.get("module_source") != source:
        raise SymbolicProtocolError("native refutation module failed recipe replay")
    return source


def _integer(value: Any, *, positive: bool = False) -> int:
    if type(value) is not int or value < (1 if positive else 0):
        raise SymbolicProtocolError("invalid native refutation integer")
    return value


def _fields(value: Any, keys: set[str]) -> dict[str, Any]:
    if not isinstance(value, dict) or value.keys() != keys:
        raise SymbolicProtocolError("malformed native refutation recipe")
    return value


def _render(
    kind: str,
    tree: Any,
    count: int,
    scope: _Scope | None = None,
    *,
    atoms: set[int] | None = None,
) -> str:
    # Iterative replay avoids imposing Python's recursion limit on native proof
    # depth. Linked scopes retain binder identity without quadratic list copies.
    pending: list[str | tuple[str, Any, _Scope | None]] = [(kind, tree, scope)]
    output: list[str] = []
    while pending:
        item = pending.pop()
        if isinstance(item, str):
            output.append(item)
            continue
        mode, node, env = item
        if not isinstance(node, dict):
            raise SymbolicProtocolError("malformed native refutation node")
        tag = node.get("tag")
        if not isinstance(tag, str):
            raise SymbolicProtocolError("invalid native refutation node tag")
        parts: list[str | tuple[str, Any, _Scope | None]]
        if mode in {"formula", "closed"} and tag == "arrow":
            _fields(node, {"tag", "domain", "codomain"})
            parts = [
                "(",
                (mode, node["domain"], env),
                " → ",
                (mode, node["codomain"], env),
                ")",
            ]
        elif mode == "formula" and tag == "atom":
            _fields(node, {"tag", "id"})
            atom = _integer(node["id"])
            if atom >= count:
                raise SymbolicProtocolError("unbound native refutation atom")
            if atoms is not None:
                atoms.add(atom)
            parts = [f"a{atom}"]
        elif mode == "closed" and tag in {"empty", "unit"}:
            _fields(node, {"tag"})
            parts = ["APEmpty" if tag == "empty" else "APUnit"]
        elif mode == "expression" and tag == "unit":
            _fields(node, {"tag"})
            parts = ["apUnit"]
        elif mode == "expression" and tag == "variable" and env is not None:
            _fields(node, {"tag", "index"})
            parts = ["(" + env.lookup(_integer(node["index"])) + ")"]
        elif mode == "expression" and tag == "lambda" and env is not None:
            _fields(node, {"tag", "domain", "body"})
            name = f"x{env.depth}"
            child = _Scope(name, env, env.depth + 1)
            parts = [
                f"(λ ({name} : ",
                ("closed", node["domain"], env),
                ") → ",
                (mode, node["body"], child),
                ")",
            ]
        elif mode == "expression" and tag == "apply":
            _fields(node, {"tag", "function", "argument"})
            parts = [
                "(",
                (mode, node["function"], env),
                " ",
                (mode, node["argument"], env),
                ")",
            ]
        elif mode == "expression" and tag == "absurd":
            _fields(node, {"tag", "result", "subject"})
            parts = [
                "(apAbsurd {",
                ("closed", node["result"], env),
                "} ",
                (mode, node["subject"], env),
                ")",
            ]
        else:
            raise SymbolicProtocolError("unsupported native refutation recipe node")
        pending.extend(reversed(parts))
    return "".join(output)
