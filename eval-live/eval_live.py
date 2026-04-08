"""eval_live – lightweight library for registering visualizations.

Decorate functions with @graph to register graph functions, and @table to
register computed summary tables.

Each @graph function receives the data dict and returns a matplotlib Figure.
Each @table function receives the data dict and returns a list of row dicts.

A @table function can also have a .filter_source companion that maps
(filtered_computed_rows, original_data) -> filtered_data. When the user
filters a computed table, eval-live calls filter_source to propagate the
filter back to the raw data tables. Multiple computed table filters compose
by chaining.

Usage:

    from eval_live import graph, table

    @table("Summary")
    def summary(data):
        return [{"treatment": t, "mean": ...} for t in treatments]

    @summary.filter_source
    def _(filtered_rows, data):
        treatments = {r["treatment"] for r in filtered_rows}
        return {
            **data,
            "timings": [r for r in data["timings"]
                        if r["treatment"] in treatments],
        }

    @graph("My Graph")
    def my_graph(data):
        ...
        return fig
"""
import io
import base64

_graph_registry = []
_table_registry = []  # list of _TableRegistration


class _TableRegistration:
    __slots__ = ("name", "fn", "_filter_source_fn")

    def __init__(self, name, fn):
        self.name = name
        self.fn = fn
        self._filter_source_fn = None

    def filter_source(self, fn):
        """Decorator to register a filter_source companion."""
        self._filter_source_fn = fn
        return fn


def graph(name):
    """Decorator to register a graphing function."""
    def decorator(fn):
        _graph_registry.append((name, fn))
        return fn
    return decorator


def table(name):
    """Decorator to register a computed table function.

    The decorated function gains a .filter_source decorator attribute.
    """
    def decorator(fn):
        reg = _TableRegistration(name, fn)
        _table_registry.append(reg)
        # Attach filter_source decorator to the original function
        fn.filter_source = reg.filter_source
        fn._table_reg = reg
        return fn
    return decorator


def run_graphs(data):
    """Run all registered graph functions and return list of {name, src} dicts."""
    import matplotlib
    matplotlib.use("AGG")
    import matplotlib.pyplot as plt

    results = []
    for name, fn in _graph_registry:
        fig = fn(data)
        buf = io.BytesIO()
        fig.savefig(buf, format="png", dpi=150)
        plt.close(fig)
        buf.seek(0)
        b64 = base64.b64encode(buf.read()).decode()
        results.append({"name": name, "src": f"data:image/png;base64,{b64}"})
    return results


def run_tables(data):
    """Run all registered table functions.

    Returns list of {name, rows, has_filter_source} dicts.
    """
    results = []
    for reg in _table_registry:
        rows = reg.fn(data)
        results.append({
            "name": reg.name,
            "rows": rows,
            "has_filter_source": reg._filter_source_fn is not None,
        })
    return results


def apply_table_filters(table_filters, data):
    """Chain filter_source functions for all computed tables.

    table_filters: list of {"name": str, "filtered_rows": list}
    Returns new filtered data dict.
    """
    filtered_data = data
    for reg in _table_registry:
        if reg._filter_source_fn is None:
            continue
        for tf in table_filters:
            if tf["name"] == reg.name:
                filtered_data = reg._filter_source_fn(tf["filtered_rows"], filtered_data)
                break
    return filtered_data
