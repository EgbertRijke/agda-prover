"""Bounded exact graph search for proof-producing symbolic relation paths."""

from __future__ import annotations

import heapq
from collections.abc import Sequence


def bounded_shortest_path(
    node_count: int,
    edges: Sequence[tuple[int, int, int]],
    start: int,
    goal: int,
    max_cost: int,
) -> tuple[int, ...] | None:
    """Return the least-cost path, breaking ties by exact edge-index tuples."""

    if not (0 <= start < node_count and 0 <= goal < node_count):
        raise ValueError("relation endpoint is outside its graph")
    adjacency: list[list[tuple[int, int, int]]] = [[] for _ in range(node_count)]
    for index, (left, right, cost) in enumerate(edges):
        if not (0 <= left < node_count and 0 <= right < node_count and cost > 0):
            raise ValueError("invalid relation edge")
        adjacency[left].append((index, right, cost))
    queue: list[tuple[int, tuple[int, ...], int]] = [(0, (), start)]
    best: dict[int, tuple[int, tuple[int, ...]]] = {start: (0, ())}
    while queue:
        cost, path, node = heapq.heappop(queue)
        if best.get(node) != (cost, path):
            continue
        if node == goal:
            return path
        for edge, next_node, edge_cost in adjacency[node]:
            next_cost = cost + edge_cost
            next_path = path + (edge,)
            candidate = (next_cost, next_path)
            if next_cost <= max_cost and candidate < best.get(next_node, (2**63, ())):
                best[next_node] = candidate
                heapq.heappush(queue, (next_cost, next_path, next_node))
    return None


__all__ = ["bounded_shortest_path"]
