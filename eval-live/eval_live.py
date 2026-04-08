"""eval_live – lightweight library for registering visualizations.

Decorate functions with @graph to register them.  Each function receives
the JSON data dict and must return a matplotlib Figure.

Usage (inside a Pyodide-executed script):

    from eval_live import graph, run_graphs

    @graph("Timing Distribution")
    def timing_dist(data):
        import matplotlib.pyplot as plt
        fig, ax = plt.subplots()
        timings = [r["timing_list"][0] for r in data["timings"]]
        ax.hist(timings)
        ax.set_title("Timing Distribution")
        return fig
"""
import io
import base64

_registry = []


def graph(name):
    """Decorator to register a graphing function."""
    def decorator(fn):
        _registry.append((name, fn))
        return fn
    return decorator


def run_graphs(data):
    """Run all registered graph functions and return list of {name, src} dicts."""
    import matplotlib
    matplotlib.use("AGG")
    import matplotlib.pyplot as plt

    results = []
    for name, fn in _registry:
        fig = fn(data)
        buf = io.BytesIO()
        fig.savefig(buf, format="png", dpi=150)
        plt.close(fig)
        buf.seek(0)
        b64 = base64.b64encode(buf.read()).decode()
        results.append({"name": name, "src": f"data:image/png;base64,{b64}"})
    return results
