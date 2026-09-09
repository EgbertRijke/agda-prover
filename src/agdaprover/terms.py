"""A deliberately small, closed proof-term IR for the P0 search fragment."""

from __future__ import annotations

from collections.abc import Callable, Iterable, Iterator
from dataclasses import dataclass, field
from typing import Any

from .notation import binary_mixfix_notation, render_application
from .type_syntax import top_level_arrow_count

TERM_SCHEMA_VERSION = "agdaprover.term.p0.v1"


@dataclass(frozen=True, eq=False)
class Term:
    tag: str
    index: int | None = None
    name: str | None = None
    function: Term | None = None
    argument: Term | None = None
    body: Term | None = None
    _hash: int = field(init=False, repr=False)
    _size: int = field(init=False, repr=False)
    _depth: int = field(init=False, repr=False)

    def __post_init__(self) -> None:
        fields = {
            "index": self.index,
            "name": self.name,
            "function": self.function,
            "argument": self.argument,
            "body": self.body,
        }
        required = {
            "bound": {"index"},
            "local": {"name"},
            "refl": set(),
            "lambda": {"body"},
            "apply": {"function", "argument"},
        }
        if self.tag not in required:
            raise ValueError(f"unsupported term tag: {self.tag!r}")
        present = {name for name, value in fields.items() if value is not None}
        if present != required[self.tag]:
            raise ValueError(f"malformed {self.tag!r} term fields: {sorted(present)}")
        if self.tag == "bound" and (self.index is None or self.index < 0):
            raise ValueError("a de Bruijn index cannot be negative")
        if self.tag == "local" and not self.name:
            raise ValueError("a local name cannot be empty")
        children = self.children()
        object.__setattr__(self, "_size", 1 + sum(child.size for child in children))
        object.__setattr__(
            self, "_depth", 1 + max((child.depth for child in children), default=0)
        )
        object.__setattr__(
            self,
            "_hash",
            hash(
                (
                    self.tag,
                    self.index,
                    self.name,
                    self.function,
                    self.argument,
                    self.body,
                )
            ),
        )

    def __hash__(self) -> int:
        return self._hash

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, Term):
            return NotImplemented
        pending = [(self, other)]
        while pending:
            left, right = pending.pop()
            if left is right:
                continue
            if (
                left._hash != right._hash
                or left.tag != right.tag
                or left.index != right.index
                or left.name != right.name
            ):
                return False
            pending.extend(zip(left.children(), right.children(), strict=True))
        return True

    def children(self) -> tuple[Term, ...]:
        if self.tag == "lambda":
            return (_lambda_body(self),)
        if self.tag == "apply":
            return _application_parts(self)
        return ()

    @staticmethod
    def bound(index: int) -> Term:
        if index < 0:
            raise ValueError("a de Bruijn index cannot be negative")
        return Term("bound", index=index)

    @staticmethod
    def local(name: str) -> Term:
        if not name:
            raise ValueError("a local name cannot be empty")
        return Term("local", name=name)

    @staticmethod
    def refl() -> Term:
        """Decode the historical P0 term; active search never constructs it."""

        return Term("refl")

    @staticmethod
    def lam(body: Term) -> Term:
        return Term("lambda", body=body)

    @staticmethod
    def app(function: Term, argument: Term) -> Term:
        return Term("apply", function=function, argument=argument)

    def to_dict(self) -> dict[str, Any]:
        result: dict[str, Any] = {}
        pending = [(self, result)]
        while pending:
            term, row = pending.pop()
            row.update(schema_version=TERM_SCHEMA_VERSION, tag=term.tag)
            for name in ("index", "name"):
                value = getattr(term, name)
                if value is not None:
                    row[name] = value
            for name in ("function", "argument", "body"):
                child = getattr(term, name)
                if child is not None:
                    row[name] = {}
                    pending.append((child, row[name]))
        return result

    @staticmethod
    def from_dict(value: dict[str, Any]) -> Term:
        pending = [(value, False)]
        active: set[int] = set()
        decoded: dict[int, Term] = {}
        children = {
            "bound": (),
            "local": (),
            "refl": (),
            "lambda": ("body",),
            "apply": ("function", "argument"),
        }
        while pending:
            row, exiting = pending.pop()
            if (
                not isinstance(row, dict)
                or row.get("schema_version") != TERM_SCHEMA_VERSION
            ):
                raise ValueError("unsupported term schema version")
            tag = row.get("tag")
            if not isinstance(tag, str) or tag not in children:
                raise ValueError(f"unsupported term tag: {tag!r}")
            identity = id(row)
            if exiting:
                active.remove(identity)
                if tag == "bound":
                    answer = Term.bound(int(row["index"]))
                elif tag == "local":
                    answer = Term.local(str(row["name"]))
                elif tag == "refl":
                    answer = Term.refl()
                elif tag == "lambda":
                    answer = Term.lam(decoded[id(row["body"])])
                else:
                    answer = Term.app(
                        decoded[id(row["function"])], decoded[id(row["argument"])]
                    )
                decoded[identity] = answer
            elif identity in active:
                raise ValueError("cyclic proof term")
            elif identity not in decoded:
                active.add(identity)
                pending.append((row, True))
                pending.extend((row[name], False) for name in reversed(children[tag]))
        return decoded[id(value)]

    @property
    def size(self) -> int:
        return self._size

    @property
    def depth(self) -> int:
        return self._depth

    @property
    def lambda_count(self) -> int:
        count, current = 0, self
        while current.tag == "lambda":
            count += 1
            current = _lambda_body(current)
        return count

    @property
    def application_count(self) -> int:
        count, pending = 0, [self]
        while pending:
            current = pending.pop()
            count += current.tag == "apply"
            pending.extend(current.children())
        return count


def _bound_index(term: Term) -> int:
    if term.tag != "bound" or term.index is None:
        raise ValueError("expected a well-formed bound term")
    return term.index


def _local_name(term: Term) -> str:
    if term.tag != "local" or term.name is None:
        raise ValueError("expected a well-formed local term")
    return term.name


def _lambda_body(term: Term) -> Term:
    if term.tag != "lambda" or term.body is None:
        raise ValueError("expected a well-formed lambda term")
    return term.body


def _application_parts(term: Term) -> tuple[Term, Term]:
    if term.tag != "apply" or term.function is None or term.argument is None:
        raise ValueError("expected a well-formed application term")
    return term.function, term.argument


def _render_term(
    term: Term,
    environment: tuple[str, ...],
    parent_precedence: int,
    *,
    shared: dict[Term, str] | None = None,
    expanding: Term | None = None,
) -> str:
    values: list[str] = []
    work: list[tuple[Any, ...]] = [
        ("visit", term, environment, parent_precedence, shared)
    ]
    while work:
        operation, *payload = work.pop()
        if operation == "lambda":
            binder, precedence = payload
            text = f"λ {binder} → {values.pop()}"
            values.append(f"({text})" if precedence > 0 else text)
            continue
        if operation == "apply":
            argument, function = values.pop(), values.pop()
            text = f"{function} {argument}"
            values.append(f"({text})" if payload[0] > 1 else text)
            continue
        if operation == "local-apply":
            head, count, precedence = payload
            arguments = values[-count:]
            del values[-count:]
            text = render_application(
                head, arguments, parenthesize_infix=precedence > 0
            )
            infix = binary_mixfix_notation(head) is not None and count >= 2
            values.append(f"({text})" if not infix and precedence > 1 else text)
            continue
        current, context, precedence, names = payload
        if names and current != expanding and current in names:
            values.append(names[current])
        elif current.tag == "bound":
            index = _bound_index(current)
            if index >= len(context):
                raise ValueError("out-of-scope de Bruijn index")
            values.append(context[-1 - index])
        elif current.tag in {"local", "refl"}:
            values.append(_local_name(current) if current.tag == "local" else "refl")
        elif current.tag == "lambda":
            binder = _fresh_binder(len(context), set(context))
            work.extend(
                (
                    ("lambda", binder, precedence),
                    ("visit", _lambda_body(current), context + (binder,), 0, None),
                )
            )
        else:
            spine = _local_application_spine(current)
            if spine is not None:
                head, term_arguments = spine
                work.append(("local-apply", head, len(term_arguments), precedence))
                work.extend(
                    ("visit", arg, context, 0, names)
                    for arg in reversed(term_arguments)
                )
            else:
                term_function, term_argument = _application_parts(current)
                work.extend(
                    (
                        ("apply", precedence),
                        ("visit", term_argument, context, 2, names),
                        ("visit", term_function, context, 1, names),
                    )
                )
    return values[0]


def _local_application_spine(term: Term) -> tuple[str, tuple[Term, ...]] | None:
    """Return the local declaration head and ordered arguments of TERM."""

    arguments: list[Term] = []
    current = term
    while current.tag == "apply":
        function, argument = _application_parts(current)
        arguments.append(argument)
        current = function
    if current.tag != "local":
        return None
    arguments.reverse()
    return _local_name(current), tuple(arguments)


def _fresh_binder(start: int, forbidden: set[str]) -> str:
    index = start
    while f"x{index}" in forbidden:
        index += 1
    return f"x{index}"


def render_term(term: Term) -> str:
    """Render the structured fragment to Agda, checking de Bruijn scope."""

    return _render_term(term, (), 0)


def render_top_level_clause(
    term: Term, *, forbidden_names: Iterable[str] = ()
) -> tuple[tuple[str, ...], str]:
    """Move leading lambdas into fresh clause binders and render their body."""

    body = term
    count = 0
    while body.tag == "lambda":
        count += 1
        body = _lambda_body(body)

    forbidden = set(forbidden_names)
    binders: list[str] = []
    next_index = 0
    for _ in range(count):
        binder = _fresh_binder(next_index, forbidden | set(binders))
        binders.append(binder)
        next_index = int(binder[1:]) + 1
    return tuple(binders), _render_term(body, tuple(binders), 0)


def render_top_level_clause_shared(
    term: Term, *, forbidden_names: Iterable[str] = ()
) -> tuple[tuple[str, ...], str]:
    """Render repeated clause-level applications once through local lets.

    Nested lambdas are excluded from sharing, so no generated binding crosses
    a de Bruijn scope boundary.
    """

    body = term
    lambda_count = 0
    while body.tag == "lambda":
        lambda_count += 1
        body = _lambda_body(body)

    forbidden = set(forbidden_names)
    binders: list[str] = []
    next_index = 0
    for _ in range(lambda_count):
        binder = _fresh_binder(next_index, forbidden | set(binders))
        binders.append(binder)
        next_index = int(binder[1:]) + 1

    counts: dict[Term, int] = {}
    encounter_order: dict[Term, int] = {}
    local_names: set[str] = set()
    stack = [body]
    while stack:
        current = stack.pop()
        counts[current] = counts.get(current, 0) + 1
        encounter_order.setdefault(current, len(encounter_order))
        if current.tag == "local":
            local_names.add(_local_name(current))
        elif current.tag == "apply":
            function, argument = _application_parts(current)
            stack.append(argument)
            stack.append(function)
        # Nested lambdas use a different environment and are rendered normally.

    candidates = sorted(
        (
            current
            for current, count in counts.items()
            if current.tag == "apply" and count > 1
        ),
        key=lambda current: (current.size, encounter_order[current]),
    )
    if not candidates:
        return tuple(binders), _render_term(body, tuple(binders), 0)

    shared: dict[Term, str] = {}
    used_names = forbidden | set(binders) | local_names

    def render_shared(
        current: Term, parent_precedence: int, *, expanding: Term | None = None
    ) -> str:
        return _render_term(
            current,
            tuple(binders),
            parent_precedence,
            shared=shared,
            expanding=expanding,
        )

    bindings: list[tuple[str, str]] = []
    for candidate in candidates:
        suffix = len(bindings)
        name = f"s{suffix}"
        while name in used_names:
            suffix += 1
            name = f"s{suffix}"
        rhs = render_shared(candidate, 0, expanding=candidate)
        shared[candidate] = name
        used_names.add(name)
        bindings.append((name, rhs))

    rendered = render_shared(body, 0)
    for name, rhs in reversed(bindings):
        rendered = f"let {name} = {rhs} in {rendered}"
    return tuple(binders), rendered


def _application_bodies(
    atom_count: int,
    max_size: int,
    continue_search: Callable[[], bool],
) -> Iterator[Term]:
    by_size: dict[int, list[Term]] = {
        1: [Term.bound(index) for index in range(atom_count)]
    }
    yield from by_size[1]
    for size in range(3, max_size + 1, 2):
        values: list[Term] = []
        seen: set[Term] = set()
        for left_size in range(1, size - 1, 2):
            right_size = size - 1 - left_size
            for function in by_size.get(left_size, ()):
                for argument in by_size.get(right_size, ()):
                    if not continue_search():
                        return
                    candidate = Term.app(function, argument)
                    if candidate in seen:
                        continue
                    seen.add(candidate)
                    values.append(candidate)
                    yield candidate
        by_size[size] = values


def iter_terms(
    local_names: Iterable[str],
    *,
    max_lambdas: int = 3,
    max_size: int = 8,
    continue_search: Callable[[], bool] = lambda: True,
) -> Iterator[Term]:
    """Lazily enumerate the deterministic legacy fragment with cancellation."""

    seen: set[Term] = set()
    # Constructor constants are obtained from Agda's live signature by the
    # kernel-guided path. The legacy ``refl`` variant remains readable only
    # for the explicit P0 serialization compatibility window.
    initial = tuple(Term.local(name) for name in local_names if name)
    for term in initial:
        if not continue_search():
            return
        if term.size <= max_size and term not in seen:
            seen.add(term)
            yield term
    for lambda_count in range(1, max_lambdas + 1):
        body_limit = max_size - lambda_count
        if body_limit < 1:
            continue
        for body in _application_bodies(lambda_count, body_limit, continue_search):
            candidate = body
            for _ in range(lambda_count):
                candidate = Term.lam(candidate)
            if candidate.size <= max_size and candidate not in seen:
                seen.add(candidate)
                yield candidate


def generate_terms(
    local_names: Iterable[str],
    *,
    max_lambdas: int = 3,
    max_size: int = 8,
) -> list[Term]:
    """Enumerate a deterministic finite fragment of beta-normal-shaped terms."""

    return list(
        iter_terms(
            local_names,
            max_lambdas=max_lambdas,
            max_size=max_size,
        )
    )


def symbolic_key(target: str, term: Term) -> tuple[int, int, str]:
    desired_lambdas = min(3, top_level_arrow_count(target))
    lambda_penalty = abs(term.lambda_count - desired_lambdas)
    return (lambda_penalty, term.size, render_term(term))
