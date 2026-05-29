#!/usr/bin/env python3
"""Render Lean dependency TSV output as an image.

This script is designed to work with the TSV emitted by
`DeclDependencies.lean`, where each relevant line is one of:

    NODE<TAB>declaration_name<TAB>kind
    EDGE<TAB>source_declaration<TAB>target_declaration

Example TSV input:

    NODE\tPi.dual_le_dual_iff\ttheorem
    NODE\tChromosome.dual_le_dual_iff\ttheorem
    EDGE\tPi.dual_le_dual_iff\tChromosome.dual_le_dual_iff

Typical usage with the uv virtual environment:

    .venv/bin/python render_dependency_graph.py graph.tsv -o graph.svg

Read TSV from stdin:

    .venv/bin/python render_dependency_graph.py -o graph.svg < graph.tsv

Run `lake build DeclDependencies`, extract `#eval` TSV output, and render it:

    .venv/bin/python render_dependency_graph.py \
        --build-target DeclDependencies \
        --output graph.svg

Export Graphviz source instead of an image:

    .venv/bin/python render_dependency_graph.py graph.tsv -o graph.dot --format dot
"""

from __future__ import annotations

import argparse
import csv
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path

try:
    import pygraphviz as pgv
except ImportError as exc:  # pragma: no cover - depends on interpreter environment
    raise SystemExit(
        "pygraphviz is not available in this Python environment. "
        "Please run this script with `.venv/bin/python`."
    ) from exc

@dataclass(frozen=True)
class NodeRecord:
    name: str
    kind: str = "unknown"


@dataclass(frozen=True)
class EdgeRecord:
    src: str
    dst: str


NODE_STYLES: dict[str, dict[str, str]] = {
    "theorem": {"shape": "box", "style": "filled", "fillcolor": "#dbeafe"},
    "def": {"shape": "ellipse", "style": "filled", "fillcolor": "#dcfce7"},
    "opaque": {"shape": "ellipse", "style": "filled", "fillcolor": "#fae8ff"},
    "axiom": {"shape": "diamond", "style": "filled", "fillcolor": "#fee2e2"},
    "inductive": {"shape": "folder", "style": "filled", "fillcolor": "#fef3c7"},
    "ctor": {"shape": "component", "style": "filled", "fillcolor": "#fde68a"},
    "recursor": {"shape": "hexagon", "style": "filled", "fillcolor": "#e0e7ff"},
    "quot": {"shape": "octagon", "style": "filled", "fillcolor": "#f3f4f6"},
    "unknown": {"shape": "ellipse", "style": "filled", "fillcolor": "#f3f4f6"},
}


def parse_args() -> argparse.Namespace:
    """Parse CLI arguments for TSV input selection and graph rendering options."""
    parser = argparse.ArgumentParser(
        description="Render Lean dependency TSV as a graph image using pygraphviz."
    )
    parser.add_argument(
        "input",
        nargs="?",
        help="Path to TSV file. If omitted, read from stdin unless --build-target is used.",
    )
    parser.add_argument(
        "--build-target",
        help="Run `lake build <target>` and extract TSV lines from its output.",
    )
    parser.add_argument(
        "--project-root",
        default=".",
        help="Project root used when running `lake build`.",
    )
    parser.add_argument(
        "-o",
        "--output",
        default="dependency-graph.svg",
        help="Output file path. Suffix determines format unless --format is set.",
    )
    parser.add_argument(
        "--format",
        choices=["svg", "png", "pdf", "dot"],
        help="Override output format.",
    )
    parser.add_argument(
        "--layout",
        default="dot",
        choices=["dot", "neato", "fdp", "sfdp", "twopi", "circo"],
        help="Graphviz layout program.",
    )
    parser.add_argument(
        "--label-mode",
        default="full",
        choices=["full", "tail"],
        help="Use full declaration names or only the last segment as labels.",
    )
    parser.add_argument(
        "--rankdir",
        default="LR",
        choices=["LR", "RL", "TB", "BT"],
        help="Graph direction for Graphviz.",
    )
    parser.add_argument(
        "--node-fontsize",
        type=int,
        default=10,
        help="Node label font size.",
    )
    parser.add_argument(
        "--edge-fontsize",
        type=int,
        default=9,
        help="Edge label font size.",
    )
    return parser.parse_args()


def read_tsv_lines(path: str | None) -> list[list[str]]:
    """Read TSV rows from a file path or from stdin when `path` is `None`."""
    if path is None:
        return extract_tsv_rows(sys.stdin.read())
    return extract_tsv_rows(Path(path).read_text(encoding="utf-8"))


def extract_tsv_rows(text: str) -> list[list[str]]:
    """Extract only `NODE`/`EDGE` TSV rows from arbitrary text output."""
    rows: list[list[str]] = []
    for raw_line in text.splitlines():
        line = raw_line.strip()
        if not line or line.startswith("#"):
            continue
        if not (line.startswith("NODE\t") or line.startswith("EDGE\t")):
            continue
        rows.append(next(csv.reader([line], delimiter="\t")))
    return rows


def read_tsv_lines_from_lake_build(build_target: str, project_root: str) -> list[list[str]]:
    """Run `lake build` and extract TSV rows from the combined build output."""
    result = subprocess.run(
        ["lake", "build", build_target],
        cwd=project_root,
        text=True,
        capture_output=True,
        check=False,
    )
    output = result.stdout
    if result.stderr:
        output = f"{output}\n{result.stderr}"
    if result.returncode != 0:
        raise RuntimeError(
            f"`lake build {build_target}` failed with exit code {result.returncode}.\n{output}"
        )
    rows = extract_tsv_rows(output)
    if not rows:
        raise RuntimeError(
            "No NODE/EDGE TSV lines were found in `lake build` output. "
            "Please uncomment a `#eval` in `DeclDependencies.lean` first."
        )
    return rows


def parse_rows(rows: list[list[str]]) -> tuple[dict[str, NodeRecord], list[EdgeRecord]]:
    """Parse raw TSV rows into node and edge records."""
    nodes: dict[str, NodeRecord] = {}
    edges: list[EdgeRecord] = []
    for row in rows:
        tag = row[0]
        if tag == "NODE":
            if len(row) < 3:
                raise ValueError(f"Malformed NODE row: {row}")
            name, kind = row[1], row[2]
            nodes[name] = NodeRecord(name=name, kind=kind)
        elif tag == "EDGE":
            if len(row) < 3:
                raise ValueError(f"Malformed EDGE row: {row}")
            src, dst = row[1], row[2]
            edges.append(EdgeRecord(src=src, dst=dst))
            nodes.setdefault(src, NodeRecord(name=src))
            nodes.setdefault(dst, NodeRecord(name=dst))
        else:
            raise ValueError(f"Unknown TSV tag {tag!r} in row: {row}")
    return nodes, edges


def format_label(name: str, mode: str) -> str:
    """Format a node label using either the full name or only the last segment."""
    if mode == "full":
        return name
    return name.split(".")[-1]


def build_graph(
    nodes: dict[str, NodeRecord],
    edges: list[EdgeRecord],
    *,
    label_mode: str,
    rankdir: str,
    node_fontsize: int,
    edge_fontsize: int,
) -> pgv.AGraph:
    """Build a styled directed graph from parsed node and edge records."""
    graph = pgv.AGraph(strict=False, directed=True)
    graph.graph_attr.update(rankdir=rankdir, splines="true", overlap="false")
    graph.node_attr.update(fontname="Helvetica", fontsize=str(node_fontsize))
    graph.edge_attr.update(fontname="Helvetica", fontsize=str(edge_fontsize), color="#64748b")

    for node in sorted(nodes.values(), key=lambda item: item.name):
        attrs = NODE_STYLES.get(node.kind, NODE_STYLES["unknown"]).copy()
        attrs["label"] = format_label(node.name, label_mode)
        attrs["tooltip"] = f"{node.name} ({node.kind})"
        graph.add_node(node.name, **attrs)

    for edge in edges:
        graph.add_edge(edge.src, edge.dst)

    return graph


def write_graph(graph: pgv.AGraph, output_path: Path, layout: str, fmt: str) -> None:
    """Write the graph to disk as `dot`, `svg`, `png`, or `pdf`."""
    if fmt == "dot":
        graph.write(output_path)
        return
    graph.layout(prog=layout)
    graph.draw(output_path, format=fmt)


def main() -> int:
    """CLI entry point."""
    args = parse_args()
    output_path = Path(args.output)
    fmt = args.format or output_path.suffix.lstrip(".") or "svg"
    if fmt not in {"svg", "png", "pdf", "dot"}:
        raise ValueError(f"Unsupported output format: {fmt}")

    if args.build_target is not None:
        rows = read_tsv_lines_from_lake_build(args.build_target, args.project_root)
    else:
        rows = read_tsv_lines(args.input)
    nodes, edges = parse_rows(rows)
    graph = build_graph(
        nodes,
        edges,
        label_mode=args.label_mode,
        rankdir=args.rankdir,
        node_fontsize=args.node_fontsize,
        edge_fontsize=args.edge_fontsize,
    )

    output_path.parent.mkdir(parents=True, exist_ok=True)
    write_graph(graph, output_path, args.layout, fmt)

    print(
        f"Wrote {output_path} with {len(nodes)} nodes and {len(edges)} edges "
        f"using layout={args.layout} format={fmt}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
