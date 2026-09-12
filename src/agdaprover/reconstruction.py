"""Minimal, versioned source edits for term and clause-style reconstruction."""

from __future__ import annotations

import re
from collections.abc import Iterable
from typing import Any

from .contracts import GoalInfo
from .project.sources import mask_comments_and_strings, mask_literate_markdown
from .proof_formatter import (
    FormattedProof,
    format_proof_term,
    validate_formatter_metadata,
)
from .terms import Term, render_top_level_clause_shared
from .type_syntax import split_top_level_application

RECONSTRUCTION_SCHEMA_VERSION = "agdaprover.reconstruction.p0.v1"
_INTRO_PREVIEW = re.compile(r"^\s*λ\s+(.+?)\s+→\s+\?\s*$")


def _valid_clause_binder(binder: str) -> bool:
    return (
        bool(binder)
        and binder not in {"λ", "→", "?"}
        and not any(character.isspace() or character == "=" for character in binder)
    )


def _goal_offsets(source: str, goal: GoalInfo) -> tuple[int, int]:
    start, end = goal.source_range
    if start <= 0 or end <= start or end - 1 > len(source):
        raise ValueError("Agda returned an invalid goal source range")
    return start - 1, end - 1


def _definition_prefix(source: str, goal: GoalInfo) -> tuple[int, int, str, str]:
    hole_start, hole_end = _goal_offsets(source, goal)
    line_start = source.rfind("\n", 0, hole_start) + 1
    prefix = source[line_start:hole_start]
    equals = prefix.rfind("=")
    if equals < 0 or prefix[equals + 1 :].strip():
        raise ValueError("P0 clause reconstruction requires a hole after `='")
    lhs = prefix[:equals].rstrip()
    if not lhs or "\n" in lhs:
        raise ValueError("P0 clause reconstruction requires a one-line clause head")
    if set(split_top_level_application(lhs)).intersection(
        {"=", "λ", "let", "in", "record"}
    ):
        raise ValueError("clause reconstruction cannot hoist an embedded definition")
    return line_start, hole_end, lhs, source[hole_start:hole_end]


def _source_edit(
    source: str,
    *,
    start_offset: int,
    end_offset: int,
    replacement: str,
    style: str,
    binders: Iterable[str],
    body: str,
    formatter: FormattedProof | None = None,
    layout: str | None = None,
) -> dict[str, Any]:
    if style != "term":
        # Check whole-declaration edit boundaries, not every cheap ownership
        # lookup. An expression's internal record field is not a clause even
        # if its line happens to have the shape "name = hole".
        visible = _visible_source(source, start_offset, end_offset)
        if visible[:start_offset].strip():
            split_top_level_application(visible[:start_offset])
    edit: dict[str, Any] = {
        "schema_version": RECONSTRUCTION_SCHEMA_VERSION,
        "style": style,
        "source_range": [start_offset + 1, end_offset + 1],
        "original": source[start_offset:end_offset],
        "replacement": replacement,
        "binders": list(binders),
        "body": body,
    }
    if formatter is not None:
        edit["formatter"] = formatter.metadata()
    if layout is not None:
        edit["layout"] = layout
    return edit


def _visible_source(source: str, start: int, end: int) -> str:
    """Lexical edit guard in full-file context, not Agda parsing authority.

    Whole-file context matters when a joint range starts inside a Markdown
    fence and crosses prose before another fence. Masking the fragment alone
    reverses those fence boundaries. Source selection and fresh Agda checking
    remain authoritative, as with the existing whole-declaration guard.
    """
    visible = mask_comments_and_strings(source)
    if "```" in visible:
        literate = mask_comments_and_strings(mask_literate_markdown(source))
        if literate[start:end].strip():
            return literate
    return visible


def _replacement_has_holes(source: str, start: int, end: int, replacement: str) -> bool:
    candidate = source[:start] + replacement + source[end:]
    new_end = start + len(replacement)
    visible = _visible_source(candidate, start, new_end)[start:new_end]
    return re.search(r"\{![\s\S]*?!\}|(?<![\w?])\?(?![\w?])", visible) is not None


def _line_indentation(source: str, offset: int) -> tuple[int, int]:
    """Return the source column and enclosing declaration indentation."""

    line_start = source.rfind("\n", 0, offset) + 1
    line = source[line_start:offset]
    matched = re.match(r"[ \t]*", line)
    leading = matched.group(0) if matched is not None else ""
    # Generated code uses spaces even if the surrounding source contains a tab.
    return offset - line_start, len(leading.expandtabs())


def _format_at_hole(source: str, hole_start: int, body: str) -> FormattedProof:
    column, continuation = _line_indentation(source, hole_start)
    # An inline expression belongs inside its declaration's layout block.
    # Infix formatting can break between sibling branches without adding its
    # own nesting; using the declaration column would start a new declaration.
    if column > continuation:
        continuation += 2
    return format_proof_term(
        body,
        initial_column=column,
        base_indentation=continuation,
    )


def _format_clause_body(
    *,
    lhs: str,
    head: str,
    body: str,
) -> tuple[FormattedProof, str, str]:
    """Format BODY inline when it fits, otherwise beneath the clause head."""

    matched = re.match(r"[ \t]*", lhs)
    leading = matched.group(0) if matched is not None else ""
    continuation_width = len(leading.expandtabs()) + 2
    inline = format_proof_term(
        body,
        initial_column=len(head.expandtabs()) + 3,
        base_indentation=continuation_width,
    )
    if inline.status == "preserved-unsupported" or not inline.multiline:
        return inline, f"{head} = {inline.text}", "inline"
    block = format_proof_term(
        body,
        initial_column=continuation_width,
        base_indentation=continuation_width,
    )
    continuation = " " * continuation_width
    return block, f"{head} =\n{continuation}{block.text}", "next-line"


def reconstruct_term_as_clause(
    source: str,
    goal: GoalInfo,
    term: Term,
    *,
    forbidden_names: Iterable[str] = (),
) -> dict[str, Any]:
    """Build the smallest source edit that renders leading lambdas as patterns."""

    binders, body = render_top_level_clause_shared(
        term, forbidden_names=forbidden_names
    )
    hole_start, hole_end = _goal_offsets(source, goal)
    if not binders:
        formatted = _format_at_hole(source, hole_start, body)
        return _source_edit(
            source,
            start_offset=hole_start,
            end_offset=hole_end,
            replacement=formatted.text,
            style="term",
            binders=(),
            body=formatted.text,
            formatter=formatted,
        )

    line_start, end_offset, lhs, _hole = _definition_prefix(source, goal)
    head = f"{lhs} {' '.join(binders)}"
    formatted, replacement, layout = _format_clause_body(
        lhs=lhs,
        head=head,
        body=body,
    )
    return _source_edit(
        source,
        start_offset=line_start,
        end_offset=end_offset,
        replacement=replacement,
        style="clause",
        binders=binders,
        body=formatted.text,
        formatter=formatted,
        layout=layout,
    )


def reconstruct_intro_as_clause(
    source: str, goal: GoalInfo, preview: str
) -> dict[str, Any]:
    """Move every binder in Agda's `λ x y … → ?' preview to the clause head."""

    matched = _INTRO_PREVIEW.fullmatch(preview)
    if matched is None:
        raise ValueError(f"unsupported lambda-introduction preview: {preview!r}")
    binders = tuple(matched.group(1).split())
    if not binders or not all(_valid_clause_binder(binder) for binder in binders):
        raise ValueError(f"unsupported lambda-introduction preview: {preview!r}")
    line_start, end_offset, lhs, hole = _definition_prefix(source, goal)
    return _source_edit(
        source,
        start_offset=line_start,
        end_offset=end_offset,
        replacement=f"{lhs} {' '.join(binders)} = {hole}",
        style="clause-intro",
        binders=binders,
        body=hole,
    )


def reconstruct_hole_completion(
    source: str, goal: GoalInfo, body: str, *, native_layout: bool = False
) -> dict[str, Any]:
    """Replace one selected hole with a complete kernel-checkable expression.

    ``native_layout`` accepts a column-zero Agda-printer expression. Preserve
    that printer's relative layout instead of parsing/reformatting its syntax.
    This is a rendering contract, not proof authority; fresh checking is required.
    """

    if not body.strip() or re.search(r"\{![\s\S]*?!\}|(?<![\w?])\?(?![\w?])", body):
        raise ValueError("hole completion is empty or still contains a proof hole")
    hole_start, hole_end = _goal_offsets(source, goal)
    original = source[hole_start:hole_end]
    if not _is_hole(original):
        raise ValueError("hole completion does not select a proof hole")
    if native_layout:
        column, _ = _line_indentation(source, hole_start)
        # Parentheses preserve the expression boundary even inside applications.
        # The first character is one column after the opening parenthesis.
        anchored = "(" + body.replace("\n", "\n" + " " * (column + 1)) + ")"
        return _source_edit(
            source,
            start_offset=hole_start,
            end_offset=hole_end,
            replacement=anchored,
            style="term",
            binders=(),
            body=anchored,
        )
    formatted = _format_at_hole(source, hole_start, body)
    return _source_edit(
        source,
        start_offset=hole_start,
        end_offset=hole_end,
        replacement=formatted.text,
        style="term",
        binders=(),
        body=formatted.text,
        formatter=formatted,
    )


def reconstruct_native_completion(
    source: str, goal: GoalInfo, presentation: dict[str, Any]
) -> dict[str, Any]:
    """Anchor Agda's native expression/clause export at its original source.

    The native renderer owns binder exposure. This is lexical patch assembly,
    not proof acceptance; callers still pin inputs and freshly validate the edit.
    """
    if presentation.get("schema_version") != "agdaprover.symbolic-source.v1":
        raise ValueError("unsupported native source schema")
    hole_start, hole_end = _goal_offsets(source, goal)
    expected_goal = [hole_start, hole_end]
    native_goal = presentation.get("goal_range")
    if (
        not isinstance(native_goal, list)
        or any(type(value) is not int for value in native_goal)
        or native_goal != expected_goal
    ):
        raise ValueError("native source selects a different goal")
    body = presentation.get("body")
    if not isinstance(body, str) or not body.strip():
        raise ValueError("native source has no body")
    if presentation.get("kind") == "expression":
        return reconstruct_hole_completion(source, goal, body, native_layout=True)
    if presentation.get("kind") != "clause":
        raise ValueError("unsupported native source kind")
    span = presentation.get("source_range")
    if (
        not isinstance(span, list)
        or len(span) != 2
        or any(type(value) is not int for value in span)
        or not 0 <= span[0] <= hole_start < hole_end <= span[1] <= len(source)
    ):
        raise ValueError("invalid native clause range")
    # Agda owns the original clause boundary and has checked that its whole RHS
    # is this hole. Preserve that boundary across multiline heads instead of
    # guessing the declaration from the hole's physical line. Lexical guards
    # below reject widened, embedded or multi-declaration edits even before the
    # reconstructed source is independently checked.
    if span[1] != hole_end or not _is_hole(source[hole_start:hole_end]):
        raise ValueError("native clause does not end at the selected whole RHS")
    line_start = source.rfind("\n", 0, span[0]) + 1
    indentation = source[line_start : span[0]]
    if indentation.strip():
        raise ValueError("native clause begins inside an expression")
    head = mask_comments_and_strings(source[span[0] : hole_start])
    tokens = split_top_level_application(head)
    if (
        len(tokens) < 2
        or tokens[-1] != "="
        or tokens.count("=") != 1
        or set(tokens).intersection({"λ", "let", "in", "record", ":", "where"})
    ):
        raise ValueError("native clause requires exactly one whole-clause hole")
    if re.search(r"\{![\s\S]*?!\}|(?<![\w?])\?(?![\w?])", body):
        raise ValueError("native clause retains a proof hole")
    lines = body.rstrip().splitlines()
    anchored = bool(indentation) and all(
        not line or line.startswith(indentation) for line in lines
    )
    replacement = "\n".join(
        indentation + line if line and not anchored else line for line in lines
    )
    return _source_edit(
        source,
        start_offset=line_start,
        end_offset=hole_end,
        replacement=replacement,
        style="case-split",
        binders=(),
        body=replacement,
    )


def reconstruct_intro(source: str, goal: GoalInfo, preview: str) -> dict[str, Any]:
    """Render Agda's checked introduction, preserving implicit abstractions.

    Even a function goal can have a constructor preview: Agda may insert its
    hidden lambdas during elaboration. Only explicit lambda binders can move to
    the clause head; all other previews remain expressions at the selected hole.
    """
    if not preview.strip():
        raise ValueError("introduction preview is empty")
    if re.match(r"^\s*λ(?=\s|\{)", preview):
        try:
            return reconstruct_intro_as_clause(source, goal, preview)
        except ValueError:
            pass
    start, end = _goal_offsets(source, goal)
    if not _is_hole(source[start:end]):
        raise ValueError("introduction does not select a proof hole")
    # A partial preview is an intermediate search state, not a completed
    # proof for the formatter. Keep its holes and binders exactly as supplied.
    replacement = f"({preview})"
    return _source_edit(
        source,
        start_offset=start,
        end_offset=end,
        replacement=replacement,
        style="term",
        binders=(),
        body=replacement,
    )


def reconstruct_case_split(
    source: str, goal: GoalInfo, clauses: Iterable[str]
) -> dict[str, Any]:
    """Replace exactly the selected clause with Agda's structured case clauses."""

    values = tuple(clause.rstrip() for clause in clauses)
    if not values or any(not clause for clause in values):
        raise ValueError("case split returned no usable clauses")
    hole_start, hole_end = _goal_offsets(source, goal)
    # The protocol gives clauses for the enclosing definition, not a
    # replacement for an arbitrary expression on the hole's physical line.
    # Replacing that line would erase record fields or other sibling terms.
    _definition_prefix(source, goal)
    line_start = source.rfind("\n", 0, hole_start) + 1
    line_end = source.find("\n", hole_end)
    if line_end < 0:
        line_end = len(source)
    original = source[line_start:line_end]
    suffix = source[hole_end:line_end]
    if (
        not _is_hole(source[hole_start:hole_end])
        or mask_comments_and_strings(suffix).strip()
    ):
        raise ValueError("case reconstruction requires a whole-clause hole")
    indentation_match = re.match(r"[ \t]*", original)
    indentation = indentation_match.group(0) if indentation_match is not None else ""
    # The interaction protocol renders generated clauses as standalone
    # declarations and commonly drops their enclosing module indentation.
    # Re-anchor each physical clause line at the selected declaration's
    # indentation.  If Agda already retained that prefix, preserve it rather
    # than doubling it.  This is lexical source reconstruction only; Agda
    # remains responsible for the layout block and clause validity.
    clauses_are_anchored = bool(indentation) and all(
        not clause or clause.startswith(indentation) for clause in values
    )
    if indentation and not clauses_are_anchored:
        values = tuple(
            "\n".join(
                indentation + line if line else line for line in clause.splitlines()
            )
            for clause in values
        )
    replacement = "\n".join(values) + suffix
    return _source_edit(
        source,
        start_offset=line_start,
        end_offset=line_end,
        replacement=replacement,
        style="case-split",
        binders=(),
        body=replacement,
    )


def guided_clause_region(source: str, goal: GoalInfo) -> tuple[int, int]:
    """Return the zero-based clause region authorized for guided completion."""

    line_start, end_offset, _lhs, _hole = _definition_prefix(source, goal)
    return line_start, end_offset


def declaration_name_at_goal(source: str, goal: GoalInfo) -> str:
    """Return the declaration head owning a reconstructable interaction hole."""

    _line_start, _end_offset, lhs, _hole = _definition_prefix(source, goal)
    parts = lhs.split()
    if not parts:
        raise ValueError("selected goal has no declaration name")
    return parts[0]


def reconstruct_guided_completion(
    source: str,
    goal: GoalInfo,
    replacement: str,
    *,
    formatter: FormattedProof | None = None,
) -> dict[str, Any]:
    """Build a completed one-or-more-clause edit for guided source-state search."""

    line_start, end_offset = guided_clause_region(source, goal)
    if not replacement.strip():
        raise ValueError("guided reconstruction is empty")
    if re.search(r"\{![\s\S]*?!\}|\?", replacement):
        raise ValueError("guided reconstruction still contains proof holes")
    return _source_edit(
        source,
        start_offset=line_start,
        end_offset=end_offset,
        replacement=replacement,
        style="guided-clauses",
        binders=(),
        body=replacement,
        formatter=formatter,
    )


def reconstruct_checked_clause_completion(
    source: str,
    goal: GoalInfo,
    *,
    binders: Iterable[str],
    body: str,
) -> dict[str, Any]:
    """Reconstruct a complete clause from kernel-produced introduction names."""

    names = tuple(binders)
    if not body.strip() or re.search(r"\{![\s\S]*?!\}|(?<![\w?])\?(?![\w?])", body):
        raise ValueError("checked clause body is empty or contains a proof hole")
    if not all(_valid_clause_binder(name) for name in names):
        raise ValueError("checked clause contains an invalid binder")
    _line_start, _end_offset, lhs, _hole = _definition_prefix(source, goal)
    head = f"{lhs} {' '.join(names)}" if names else lhs
    formatted, replacement, _layout = _format_clause_body(
        lhs=lhs,
        head=head,
        body=body,
    )
    return reconstruct_guided_completion(
        source,
        goal,
        replacement,
        formatter=formatted,
    )


def reconstruct_joint_completion(
    source: str,
    *,
    start_offset: int,
    end_offset: int,
    replacement: str,
    target_goal_count: int,
    cutoff_position: int,
    steps: Iterable[dict[str, Any]],
) -> dict[str, Any]:
    """Build one atomic edit containing a jointly solved goal prefix."""

    if not 0 <= start_offset < end_offset <= len(source):
        raise ValueError("joint reconstruction range is out of bounds")
    if target_goal_count <= 0:
        raise ValueError("joint reconstruction must cover at least one goal")
    if not start_offset < cutoff_position <= end_offset:
        raise ValueError("joint reconstruction cutoff is outside its source range")
    if _replacement_has_holes(source, start_offset, end_offset, replacement):
        raise ValueError("joint reconstruction contains unresolved target holes")
    step_list = [dict(step) for step in steps]
    if not step_list:
        raise ValueError("joint reconstruction has no structured edit trace")
    edit = _source_edit(
        source,
        start_offset=start_offset,
        end_offset=end_offset,
        replacement=replacement,
        style="joint-clauses",
        binders=(),
        body=replacement,
    )
    edit.update(
        {
            "target_goal_count": target_goal_count,
            "cutoff_position": cutoff_position,
            "steps": step_list,
        }
    )
    return edit


def reconstruct_native_batch(
    source: str, goals: tuple[GoalInfo, ...], entries: list[dict[str, Any]]
) -> dict[str, Any]:
    """One atomic patch from native exports against the unchanged source."""
    if (
        not isinstance(entries, list)
        or any(
            not isinstance(e, dict)
            or type(e.get("goal_id")) is not int
            or not isinstance(e.get("source"), dict)
            for e in entries
        )
        or [entry.get("goal_id") for entry in entries] != [g.goal_id for g in goals]
    ):
        raise ValueError("native export changed the selected goal order")
    edits = [
        reconstruct_native_completion(source, goal, entry["source"])
        for goal, entry in zip(goals, entries, strict=True)
    ]
    if len(edits) == 1:
        return edits[0]
    edits.sort(key=lambda edit: edit["source_range"][0])
    if not edits or any(
        a["source_range"][1] > b["source_range"][0]
        for a, b in zip(edits, edits[1:], strict=False)
    ):
        raise ValueError("native source exports overlap or are empty")
    start, end = edits[0]["source_range"][0] - 1, edits[-1]["source_range"][1] - 1
    candidate = source
    for edit in reversed(edits):
        candidate = apply_source_edit(candidate, edit)
    delta = sum(len(e["replacement"]) - len(e["original"]) for e in edits)
    return reconstruct_joint_completion(
        source,
        start_offset=start,
        end_offset=end,
        replacement=candidate[start : end + delta],
        target_goal_count=len(goals),
        cutoff_position=end,
        steps=reversed(edits),
    )


def apply_source_edit(source: str, edit: dict[str, Any]) -> str:
    """Apply EDIT only when its version, range, and original text all match."""

    if edit.get("schema_version") != RECONSTRUCTION_SCHEMA_VERSION:
        raise ValueError("unsupported reconstruction schema version")
    source_range = edit.get("source_range")
    if not (
        isinstance(source_range, list)
        and len(source_range) == 2
        and all(isinstance(value, int) for value in source_range)
    ):
        raise ValueError("invalid reconstruction source range")
    start, end = source_range
    if start <= 0 or end <= start or end - 1 > len(source):
        raise ValueError("reconstruction source range is out of bounds")
    original = edit.get("original")
    replacement = edit.get("replacement")
    if not isinstance(original, str) or not isinstance(replacement, str):
        raise ValueError("reconstruction text must be strings")
    _validate_edit_shape(
        edit, original, replacement, source=source, start=start - 1, end=end - 1
    )
    if edit.get("style") == "joint-clauses":
        cutoff_position = edit.get("cutoff_position")
        if not (isinstance(cutoff_position, int) and start <= cutoff_position < end):
            raise ValueError("joint reconstruction cutoff is outside its range")
        _validate_joint_steps(
            original,
            replacement,
            joint_start=start,
            steps=edit.get("steps"),
        )
    if source[start - 1 : end - 1] != original:
        raise ValueError("source changed before reconstruction could be applied")
    return source[: start - 1] + replacement + source[end - 1 :]


def _validate_edit_shape(
    edit: dict[str, Any],
    original: str,
    replacement: str,
    *,
    source: str,
    start: int,
    end: int,
) -> None:
    style = edit.get("style")
    binders = edit.get("binders")
    body = edit.get("body")
    if not isinstance(binders, list) or not all(
        isinstance(binder, str) and _valid_clause_binder(binder) for binder in binders
    ):
        raise ValueError("invalid reconstruction binders")
    if not isinstance(body, str):
        raise ValueError("invalid reconstruction body")
    if "formatter" in edit:
        formatter = edit["formatter"]
        validate_formatter_metadata(
            formatter,
            output_text=body if style in {"term", "clause"} else None,
        )
    if style == "term":
        if binders or replacement != body or not _is_hole(original):
            raise ValueError("malformed term reconstruction")
        return
    if style == "case-split":
        if binders or replacement != body:
            raise ValueError("malformed case-split reconstruction")
        if not re.search(r"\{![\s\S]*?!\}|\?", original):
            raise ValueError("case split does not select a clause with a hole")
        return
    if style == "guided-clauses":
        if binders or replacement != body:
            raise ValueError("malformed guided-clause reconstruction")
        equals = original.rfind("=")
        if equals < 0 or not _is_hole(original[equals + 1 :].strip()):
            raise ValueError("guided reconstruction does not select one root hole")
        if re.search(r"\{![\s\S]*?!\}|\?", replacement):
            raise ValueError("guided reconstruction contains unresolved holes")
        return
    if style == "joint-clauses":
        target_goal_count = edit.get("target_goal_count")
        cutoff_position = edit.get("cutoff_position")
        steps = edit.get("steps")
        if binders or replacement != body:
            raise ValueError("malformed joint reconstruction")
        if not isinstance(target_goal_count, int) or target_goal_count <= 0:
            raise ValueError("joint reconstruction has an invalid target count")
        if not isinstance(cutoff_position, int) or cutoff_position <= 0:
            raise ValueError("joint reconstruction has an invalid cutoff")
        if (
            not isinstance(steps, list)
            or not steps
            or not all(isinstance(step, dict) for step in steps)
        ):
            raise ValueError("joint reconstruction has an invalid edit trace")
        if not re.search(r"\{![\s\S]*?!\}|\?", original):
            raise ValueError("joint reconstruction selects no proof holes")
        if _replacement_has_holes(source, start, end, replacement):
            raise ValueError("joint reconstruction contains unresolved target holes")
        return
    if style not in {"clause", "clause-intro"} or not binders:
        raise ValueError(f"unsupported reconstruction style: {style!r}")
    equals = original.rfind("=")
    if equals < 0:
        raise ValueError("clause reconstruction has no equals sign")
    lhs = original[:equals].rstrip()
    hole = original[equals + 1 :].strip()
    if not lhs or not _is_hole(hole):
        raise ValueError("clause reconstruction does not select a proof hole")
    expected_body = hole if style == "clause-intro" else body
    layout = edit.get("layout", "inline")
    if style == "clause-intro" and layout != "inline":
        raise ValueError("clause introduction cannot use a block body")
    if layout == "inline":
        expected = f"{lhs} {' '.join(binders)} = {expected_body}"
    elif layout == "next-line" and style == "clause":
        matched = re.match(r"[ \t]*", lhs)
        leading = matched.group(0) if matched is not None else ""
        continuation = " " * (len(leading.expandtabs()) + 2)
        expected = f"{lhs} {' '.join(binders)} =\n{continuation}{expected_body}"
    else:
        raise ValueError("clause reconstruction has an invalid layout")
    if replacement != expected:
        raise ValueError(
            "reconstruction replacement does not match its structured fields"
        )


def _is_hole(value: str) -> bool:
    return (value.startswith("{!") and value.endswith("!}")) or value == "?"


def _validate_joint_steps(
    original: str,
    replacement: str,
    *,
    joint_start: int,
    steps: object,
) -> None:
    """Replay a joint patch's structured transitions inside its local region."""

    if not isinstance(steps, list):
        raise ValueError("joint reconstruction has no edit trace")
    working = original
    for step in steps:
        if not isinstance(step, dict) or step.get("style") == "joint-clauses":
            raise ValueError("joint reconstruction contains an invalid nested edit")
        source_range = step.get("source_range")
        if not (
            isinstance(source_range, list)
            and len(source_range) == 2
            and all(isinstance(value, int) for value in source_range)
        ):
            raise ValueError("joint reconstruction step has an invalid range")
        localized = dict(step)
        localized["source_range"] = [
            source_range[0] - joint_start + 1,
            source_range[1] - joint_start + 1,
        ]
        working = apply_source_edit(working, localized)
    if working != replacement:
        raise ValueError(
            "joint reconstruction does not match its structured edit trace"
        )
