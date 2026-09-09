"""Cheap, Agda-checked refutations for a narrow implication fragment.

A Boolean countermodel is used only as a bounded witness finder. The witness
is compiled into a term of ``G → APEmpty``, where ``G`` is the complete source
declaration type, and one fresh Agda process checks the generated module.
Failure or budget exhaustion never produces an impossibility claim.
"""

from __future__ import annotations

import hashlib
import re
import time
from collections import OrderedDict
from collections.abc import Mapping
from dataclasses import dataclass
from itertools import product
from pathlib import Path
from typing import Literal, cast

from .bridge.source_text import mask_agda_source
from .contracts import GoalInfo
from .focused import TypeExpr, parse_type
from .verification import (
    ValidationError,
    executable_sha256,
    validate_standalone_module,
)

IMPOSSIBILITY_SCHEMA_VERSION = "agdaprover.impossibility.p0.v2"
IMPLICATION_FRAGMENT_ID = "pure-implication-over-abstract-types-v1"
REFUTATION_COMPILER_ID = "boolean-refutation-compiler-v1"
COUNTERMODEL_ASSIGNMENT_BUDGET = 4096
COUNTERMODEL_TIME_BUDGET_SECONDS = 0.002
REFUTATION_MODULE_FILENAME = "AgdaProverImpossibility.agda"
_CACHE_CAPACITY = 256


@dataclass(frozen=True)
class Countermodel:
    """A finite valuation under which the assumptions hold and target fails."""

    assumptions: tuple[str, ...]
    target: str
    valuation: tuple[tuple[str, bool], ...]
    assignments_checked: int


@dataclass(frozen=True)
class CountermodelSearch:
    status: Literal["found", "no-countermodel", "budget-exhausted", "unsupported"]
    countermodel: Countermodel | None
    assignments_checked: int
    elapsed_ms: float


@dataclass(frozen=True)
class CompiledRefutation:
    full_goal: str
    abstract_parameters: tuple[str, ...]
    refutation_term: str
    source: str

    @property
    def source_sha256(self) -> str:
        return hashlib.sha256(self.source.encode()).hexdigest()


@dataclass(frozen=True)
class ImpossibilityCertificate:
    """Logical witness plus the identity of its successful Agda check."""

    assumptions: tuple[str, ...]
    target: str
    valuation: tuple[tuple[str, bool], ...]
    assignments_checked: int
    full_goal: str
    abstract_parameters: tuple[str, ...]
    refutation_term: str
    generated_module_sha256: str
    agda_version: str
    agda_binary_sha256: str
    checker_output_sha256: str
    checker_exit_status: int = 0
    schema_version: str = IMPOSSIBILITY_SCHEMA_VERSION
    fragment_id: str = IMPLICATION_FRAGMENT_ID
    method: str = "agda-checked-refutation"
    witness_method: str = "boolean-countermodel"
    compiler_id: str = REFUTATION_COMPILER_ID

    @staticmethod
    def from_dict(value: Mapping[str, object]) -> ImpossibilityCertificate:
        """Decode a persisted certificate, rejecting unknown or malformed data."""

        if value.get("schema_version") != IMPOSSIBILITY_SCHEMA_VERSION:
            raise ValueError("unsupported impossibility certificate version")
        if value.get("fragment_id") != IMPLICATION_FRAGMENT_ID:
            raise ValueError("unsupported impossibility fragment")
        if value.get("method") != "agda-checked-refutation":
            raise ValueError("unsupported impossibility certificate method")
        if value.get("witness_method") != "boolean-countermodel":
            raise ValueError("unsupported impossibility witness method")
        if value.get("compiler_id") != REFUTATION_COMPILER_ID:
            raise ValueError("unsupported refutation compiler")

        assumptions = value.get("assumptions")
        target = value.get("target")
        valuation = value.get("valuation")
        assignments_checked = value.get("assignments_checked")
        full_goal = value.get("full_goal")
        parameters = value.get("abstract_parameters")
        refutation_term = value.get("refutation_term")
        module_hash = value.get("generated_module_sha256")
        agda_version = value.get("agda_version")
        binary_hash = value.get("agda_binary_sha256")
        output_hash = value.get("checker_output_sha256")
        exit_status = value.get("checker_exit_status")
        if not (
            isinstance(assumptions, list)
            and all(isinstance(item, str) for item in assumptions)
            and isinstance(target, str)
            and bool(target)
            and isinstance(valuation, dict)
            and bool(valuation)
            and all(
                isinstance(name, str) and isinstance(truth, bool)
                for name, truth in valuation.items()
            )
            and isinstance(assignments_checked, int)
            and not isinstance(assignments_checked, bool)
            and assignments_checked > 0
            and isinstance(full_goal, str)
            and bool(full_goal)
            and isinstance(parameters, list)
            and bool(parameters)
            and all(isinstance(parameter, str) for parameter in parameters)
            and isinstance(refutation_term, str)
            and bool(refutation_term)
            and _is_sha256(module_hash)
            and isinstance(agda_version, str)
            and bool(agda_version)
            and _is_sha256(binary_hash)
            and _is_sha256(output_hash)
            and exit_status == 0
        ):
            raise ValueError("malformed impossibility certificate")
        return ImpossibilityCertificate(
            assumptions=tuple(assumptions),
            target=target,
            valuation=tuple(valuation.items()),
            assignments_checked=assignments_checked,
            full_goal=full_goal,
            abstract_parameters=tuple(parameters),
            refutation_term=refutation_term,
            generated_module_sha256=str(module_hash),
            agda_version=agda_version,
            agda_binary_sha256=str(binary_hash),
            checker_output_sha256=str(output_hash),
            checker_exit_status=0,
        )

    def to_dict(self) -> dict[str, object]:
        return {
            "schema_version": self.schema_version,
            "fragment_id": self.fragment_id,
            "method": self.method,
            "witness_method": self.witness_method,
            "compiler_id": self.compiler_id,
            "assumptions": list(self.assumptions),
            "target": self.target,
            "valuation": dict(self.valuation),
            "assignments_checked": self.assignments_checked,
            "full_goal": self.full_goal,
            "abstract_parameters": list(self.abstract_parameters),
            "refutation_term": self.refutation_term,
            "empty_type": "APEmpty",
            "generated_module_sha256": self.generated_module_sha256,
            "agda_version": self.agda_version,
            "agda_binary_sha256": self.agda_binary_sha256,
            "checker_output_sha256": self.checker_output_sha256,
            "checker_exit_status": self.checker_exit_status,
            "claim": "the complete polymorphic goal is uninhabited",
        }


@dataclass(frozen=True)
class ImpossibilityOutcome:
    status: Literal[
        "certified",
        "unsupported",
        "no-countermodel",
        "budget-exhausted",
        "checker-rejected",
    ]
    certificate: ImpossibilityCertificate | None
    validation: dict[str, object] | None
    trust_report: dict[str, object] | None
    assignments_checked: int
    witness_elapsed_ms: float
    checker_calls: int
    cache_hit: bool
    diagnostic: str = ""

    def metrics(self) -> dict[str, object]:
        return {
            "status": self.status,
            "assignment_budget": COUNTERMODEL_ASSIGNMENT_BUDGET,
            "time_budget_ms": COUNTERMODEL_TIME_BUDGET_SECONDS * 1000.0,
            "assignments_checked": self.assignments_checked,
            "witness_elapsed_ms": self.witness_elapsed_ms,
            "checker_calls": self.checker_calls,
            "checker_elapsed_ms": (
                self.validation.get("elapsed_ms", 0.0)
                if self.validation and self.checker_calls
                else 0.0
            ),
            "cache_hit": self.cache_hit,
        }


@dataclass(frozen=True)
class _CachedCertificate:
    certificate: ImpossibilityCertificate
    validation: dict[str, object]
    trust_report: dict[str, object]


_CERTIFICATE_CACHE: OrderedDict[tuple[str, str, str], _CachedCertificate] = (
    OrderedDict()
)


def clear_impossibility_cache() -> None:
    """Clear the bounded positive-certificate cache (primarily for tests)."""

    _CERTIFICATE_CACHE.clear()


def find_boolean_countermodel(
    goal: GoalInfo,
    *,
    assignment_budget: int = COUNTERMODEL_ASSIGNMENT_BUDGET,
    time_budget_seconds: float = COUNTERMODEL_TIME_BUDGET_SECONDS,
) -> CountermodelSearch:
    """Search a tightly bounded Boolean model; never make a logical claim."""

    started = time.monotonic()
    if assignment_budget <= 0 or time_budget_seconds <= 0:
        return CountermodelSearch("budget-exhausted", None, 0, 0.0)
    try:
        target, assumptions, _parameters = _fragment_formulas(goal)
    except ValueError:
        return CountermodelSearch(
            "unsupported", None, 0, (time.monotonic() - started) * 1000.0
        )

    formulas = (*assumptions, target)
    used_atoms = set().union(*(_atoms(formula) for formula in formulas))
    if not used_atoms:
        return CountermodelSearch(
            "unsupported", None, 0, (time.monotonic() - started) * 1000.0
        )
    ordered_atoms = tuple(sorted(used_atoms))
    total_assignments = 1 << len(ordered_atoms)
    checked = 0
    deadline = started + time_budget_seconds
    for values in product((False, True), repeat=len(ordered_atoms)):
        if checked >= assignment_budget or (checked and time.monotonic() >= deadline):
            return CountermodelSearch(
                "budget-exhausted",
                None,
                checked,
                (time.monotonic() - started) * 1000.0,
            )
        checked += 1
        valuation = dict(zip(ordered_atoms, values, strict=True))
        if all(_evaluate(formula, valuation) for formula in assumptions) and not (
            _evaluate(target, valuation)
        ):
            countermodel = Countermodel(
                assumptions=tuple(formula.canonical() for formula in assumptions),
                target=target.canonical(),
                valuation=tuple(valuation.items()),
                assignments_checked=checked,
            )
            return CountermodelSearch(
                "found",
                countermodel,
                checked,
                (time.monotonic() - started) * 1000.0,
            )
    if checked != total_assignments:
        raise RuntimeError("countermodel enumeration ended before its finite bound")
    return CountermodelSearch(
        "no-countermodel",
        None,
        checked,
        (time.monotonic() - started) * 1000.0,
    )


def compile_refutation(
    goal: GoalInfo, full_goal: str, countermodel: Countermodel
) -> CompiledRefutation:
    """Compile a countermodel into ``full_goal → APEmpty`` Agda source."""

    target, assumptions, parameters = _fragment_formulas(goal)
    if assumptions:
        raise ValueError("P0 refutation compilation requires the complete RHS hole")
    if any(" ".join(entry.type.split()) != "Set" for entry in goal.context):
        raise ValueError("P0 refutation compilation currently requires Set parameters")
    if tuple(entry.name for entry in goal.context) != parameters:
        raise ValueError("P0 refutation compilation requires only abstract parameters")
    valuation = dict(countermodel.valuation)
    if countermodel.target != target.canonical() or _evaluate(target, valuation):
        raise ValueError("countermodel does not refute the target")

    instantiated = "h" + "".join(
        f" {{{'APUnit' if valuation.get(parameter, True) else 'APEmpty'}}}"
        for parameter in parameters
    )
    names = _FreshNames()
    body = _refute_value(target, instantiated, valuation, names)
    refutation_term = f"λ h → {body}"
    source = (
        "module AgdaProverImpossibility where\n\n"
        "data APEmpty : Set where\n\n"
        "data APUnit : Set where\n"
        "  apUnit : APUnit\n\n"
        "apAbsurd : {X : Set} → APEmpty → X\n"
        "apAbsurd ()\n\n"
        f"refute : ({full_goal}) → APEmpty\n"
        f"refute = {refutation_term}\n"
    )
    return CompiledRefutation(
        full_goal=full_goal,
        abstract_parameters=parameters,
        refutation_term=refutation_term,
        source=source,
    )


def certify_impossible(
    source_file: Path,
    goal: GoalInfo,
    *,
    agda_executable: str = "agda",
    agda_version: str | None = None,
    checker_timeout_seconds: float = 2.0,
) -> ImpossibilityOutcome:
    """Produce an impossibility result only after one successful fresh check."""

    witness = find_boolean_countermodel(goal)
    if witness.status != "found" or witness.countermodel is None:
        status = witness.status
        if status not in {
            "unsupported",
            "no-countermodel",
            "budget-exhausted",
        }:
            raise RuntimeError(f"unexpected countermodel status: {status}")
        return ImpossibilityOutcome(
            cast(
                Literal["unsupported", "no-countermodel", "budget-exhausted"],
                status,
            ),
            None,
            None,
            None,
            witness.assignments_checked,
            witness.elapsed_ms,
            0,
            False,
        )
    if checker_timeout_seconds <= 0:
        return ImpossibilityOutcome(
            "budget-exhausted",
            None,
            None,
            None,
            witness.assignments_checked,
            witness.elapsed_ms,
            0,
            False,
        )

    try:
        full_goal = _complete_declaration_type(source_file, goal)
        compiled = compile_refutation(goal, full_goal, witness.countermodel)
        binary_hash = executable_sha256(agda_executable)
    except (OSError, ValueError, ValidationError) as error:
        return ImpossibilityOutcome(
            "unsupported",
            None,
            None,
            None,
            witness.assignments_checked,
            witness.elapsed_ms,
            0,
            False,
            str(error),
        )

    cache_key = (compiled.source_sha256, binary_hash, agda_version or "unknown")
    cached = _CERTIFICATE_CACHE.get(cache_key)
    if cached is not None:
        _CERTIFICATE_CACHE.move_to_end(cache_key)
        return ImpossibilityOutcome(
            "certified",
            cached.certificate,
            dict(cached.validation),
            dict(cached.trust_report),
            witness.assignments_checked,
            witness.elapsed_ms,
            0,
            True,
        )

    try:
        validation, trust_report = validate_standalone_module(
            compiled.source,
            filename=REFUTATION_MODULE_FILENAME,
            agda_executable=agda_executable,
            agda_version=agda_version,
            timeout_seconds=checker_timeout_seconds,
            policy_profile="p0-agda-checked-impossibility-refutation",
        )
    except (OSError, ValidationError) as error:
        return ImpossibilityOutcome(
            "checker-rejected",
            None,
            None,
            None,
            witness.assignments_checked,
            witness.elapsed_ms,
            1,
            False,
            str(error),
        )
    if not validation["checked"]:
        diagnostic = str(validation.get("diagnostic") or "Agda rejected refutation")
        return ImpossibilityOutcome(
            "checker-rejected",
            None,
            validation,
            trust_report,
            witness.assignments_checked,
            witness.elapsed_ms,
            1,
            False,
            diagnostic,
        )

    certificate = ImpossibilityCertificate(
        assumptions=witness.countermodel.assumptions,
        target=witness.countermodel.target,
        valuation=witness.countermodel.valuation,
        assignments_checked=witness.countermodel.assignments_checked,
        full_goal=compiled.full_goal,
        abstract_parameters=compiled.abstract_parameters,
        refutation_term=compiled.refutation_term,
        generated_module_sha256=compiled.source_sha256,
        agda_version=str(trust_report["agda_version"]),
        agda_binary_sha256=str(trust_report["agda_binary_hash"]),
        checker_output_sha256=str(validation["checker_output_sha256"]),
        checker_exit_status=int(validation["exit_status"]),
    )
    if not verify_impossibility_certificate(goal, certificate, source_file=source_file):
        return ImpossibilityOutcome(
            "checker-rejected",
            None,
            validation,
            trust_report,
            witness.assignments_checked,
            witness.elapsed_ms,
            1,
            False,
            "generated impossibility certificate failed structural replay",
        )

    cached_value = _CachedCertificate(certificate, validation, trust_report)
    _CERTIFICATE_CACHE[cache_key] = cached_value
    _CERTIFICATE_CACHE.move_to_end(cache_key)
    while len(_CERTIFICATE_CACHE) > _CACHE_CAPACITY:
        _CERTIFICATE_CACHE.popitem(last=False)
    return ImpossibilityOutcome(
        "certified",
        certificate,
        validation,
        trust_report,
        witness.assignments_checked,
        witness.elapsed_ms,
        1,
        False,
    )


def verify_impossibility_certificate(
    goal: GoalInfo,
    certificate: ImpossibilityCertificate,
    *,
    source_file: Path | None = None,
) -> bool:
    """Structurally replay the model and deterministic refutation compiler."""

    if (
        certificate.schema_version != IMPOSSIBILITY_SCHEMA_VERSION
        or certificate.fragment_id != IMPLICATION_FRAGMENT_ID
        or certificate.method != "agda-checked-refutation"
        or certificate.witness_method != "boolean-countermodel"
        or certificate.compiler_id != REFUTATION_COMPILER_ID
        or certificate.checker_exit_status != 0
        or not _is_sha256(certificate.agda_binary_sha256)
        or not _is_sha256(certificate.checker_output_sha256)
    ):
        return False
    try:
        target, assumptions, parameters = _fragment_formulas(goal)
        if source_file is not None and (
            _complete_declaration_type(source_file, goal) != certificate.full_goal
        ):
            return False
    except (OSError, ValueError):
        return False
    formulas = (*assumptions, target)
    used_atoms = set().union(*(_atoms(formula) for formula in formulas))
    valuation = dict(certificate.valuation)
    ordered_atoms = tuple(sorted(used_atoms))
    assignment_index = 1 + sum(
        int(valuation.get(atom, False)) << (len(ordered_atoms) - index - 1)
        for index, atom in enumerate(ordered_atoms)
    )
    if not (
        bool(used_atoms)
        and set(valuation) == used_atoms
        and certificate.assumptions
        == tuple(formula.canonical() for formula in assumptions)
        and certificate.target == target.canonical()
        and certificate.abstract_parameters == parameters
        and all(isinstance(value, bool) for value in valuation.values())
        and certificate.assignments_checked == assignment_index
        and all(_evaluate(formula, valuation) for formula in assumptions)
        and not _evaluate(target, valuation)
    ):
        return False
    try:
        compiled = compile_refutation(
            goal,
            certificate.full_goal,
            Countermodel(
                certificate.assumptions,
                certificate.target,
                certificate.valuation,
                certificate.assignments_checked,
            ),
        )
    except ValueError:
        return False
    return (
        compiled.refutation_term == certificate.refutation_term
        and compiled.source_sha256 == certificate.generated_module_sha256
    )


def _fragment_formulas(
    goal: GoalInfo,
) -> tuple[TypeExpr, tuple[TypeExpr, ...], tuple[str, ...]]:
    abstract_parameters = tuple(
        entry.name
        for entry in goal.context
        if not entry.in_scope and entry.name and _is_universe(entry.type)
    )
    abstract_atoms = set(abstract_parameters)
    if not abstract_atoms:
        raise ValueError("goal has no abstract Set parameters")
    target = parse_type(goal.target)
    assumptions = tuple(
        parse_type(entry.type)
        for entry in goal.context
        if entry.in_scope and entry.name
    )
    formulas = (*assumptions, target)
    used_atoms = set().union(*(_atoms(formula) for formula in formulas))
    if not used_atoms or not used_atoms.issubset(abstract_atoms):
        raise ValueError("goal is outside the pure abstract implication fragment")
    return target, assumptions, abstract_parameters


def _complete_declaration_type(source_file: Path, goal: GoalInfo) -> str:
    source = source_file.read_text()
    visible_source = mask_agda_source(source, source_file)
    hole_start = goal.source_range[0] - 1
    if hole_start < 0 or hole_start > len(source):
        raise ValueError("goal source range is invalid")
    line_start = source.rfind("\n", 0, hole_start) + 1
    prefix = source[line_start:hole_start]
    equals = prefix.rfind("=")
    if equals < 0 or prefix[equals + 1 :].strip():
        raise ValueError("refutation requires a complete declaration RHS hole")
    declaration_name = prefix[:equals].strip()
    if not re.fullmatch(r"[\w'-]+", declaration_name):
        raise ValueError("refutation requires a simple declaration name")

    signature_pattern = re.compile(rf"(?m)^[ \t]*{re.escape(declaration_name)}[ \t]*:")
    matches = list(signature_pattern.finditer(visible_source, 0, line_start))
    if not matches:
        raise ValueError("could not recover the complete declaration type")
    signature = source[matches[-1].end() : line_start].strip()
    if not signature or "--" in signature or "{-" in signature:
        raise ValueError("unsupported declaration signature layout")
    return " ".join(signature.split())


class _FreshNames:
    def __init__(self) -> None:
        self._next = 0

    def take(self) -> str:
        name = f"ap{self._next}"
        self._next += 1
        return name


def _positive_value(
    formula: TypeExpr, valuation: Mapping[str, bool], names: _FreshNames
) -> str:
    if formula.tag == "atom":
        atom = formula.atom_text()
        if not valuation[atom]:
            raise ValueError("cannot construct a positively valued false atom")
        return "apUnit"
    domain, codomain = formula.arrow_parts()
    if not _evaluate(formula, valuation):
        raise ValueError("cannot construct a negatively valued implication")
    binder = names.take()
    if _evaluate(codomain, valuation):
        body = _positive_value(codomain, valuation, names)
    else:
        contradiction = _refute_value(domain, binder, valuation, names)
        body = f"apAbsurd ({contradiction})"
    return f"(λ {binder} → {body})"


def _refute_value(
    formula: TypeExpr,
    value: str,
    valuation: Mapping[str, bool],
    names: _FreshNames,
) -> str:
    if _evaluate(formula, valuation):
        raise ValueError("cannot refute a positively valued implication")
    if formula.tag == "atom":
        return value
    domain, codomain = formula.arrow_parts()
    argument = _positive_value(domain, valuation, names)
    applied = f"({value}) ({argument})"
    return _refute_value(codomain, applied, valuation, names)


def _atoms(formula: TypeExpr) -> set[str]:
    atoms: set[str] = set()
    pending = [formula]
    while pending:
        current = pending.pop()
        if current.tag == "atom":
            atoms.add(current.atom_text())
        else:
            pending.extend(current.arrow_parts())
    return atoms


def _evaluate(formula: TypeExpr, valuation: Mapping[str, bool]) -> bool:
    pending = [(formula, False)]
    values: list[bool] = []
    while pending:
        current, visited = pending.pop()
        if current.tag == "atom":
            values.append(valuation[current.atom_text()])
        elif visited:
            codomain_value = values.pop()
            domain_value = values.pop()
            values.append((not domain_value) or codomain_value)
        else:
            domain, codomain = current.arrow_parts()
            pending.extend(((current, True), (codomain, False), (domain, False)))
    if len(values) != 1:
        raise ValueError("malformed implication formula")
    return values[0]


def _is_universe(type_text: str) -> bool:
    normalized = " ".join(type_text.split())
    universe_suffixes = "0123456789₀₁₂₃₄₅₆₇₈₉ω"
    return (
        normalized == "Set"
        or normalized.startswith("Set ")
        or (
            normalized.startswith("Set")
            and bool(normalized[3:])
            and all(character in universe_suffixes for character in normalized[3:])
        )
    )


def _is_sha256(value: object) -> bool:
    return isinstance(value, str) and bool(re.fullmatch(r"[0-9a-f]{64}", value))
