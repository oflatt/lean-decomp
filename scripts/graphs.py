"""Sample graph script for eval-live. Runs in the browser via Pyodide."""
from eval_live import graph


@graph("Timings by Treatment")
def timings_by_treatment(data):
    import matplotlib.pyplot as plt
    from collections import defaultdict

    # Group timings by (file, grind_line) -> {treatment: [times]}
    by_key = defaultdict(lambda: defaultdict(list))
    for row in data.get("timings", []):
        key = (row.get("file"), row.get("grind_line"))
        treatment = row.get("treatment", "unknown")
        by_key[key][treatment].extend(row.get("timing_list", []))

    all_treatments = set()
    for treatments in by_key.values():
        all_treatments.update(treatments.keys())

    # Only include keys where every treatment has data
    complete_keys = [k for k, ts in by_key.items() if ts.keys() == all_treatments]

    by_treatment = defaultdict(list)
    for k in complete_keys:
        for treatment, times in by_key[k].items():
            by_treatment[treatment].extend(times)

    fig, ax = plt.subplots(figsize=(8, 4))
    treatments = sorted(by_treatment.keys())
    avgs = [sum(by_treatment[t]) / len(by_treatment[t]) if by_treatment[t] else 0 for t in treatments]
    ax.bar(treatments, avgs, color="#5b8def")
    ax.set_ylabel("Avg time (s)")
    ax.set_title(f"Average Timing by Treatment ({len(complete_keys)} complete benchmarks)")
    plt.tight_layout()
    return fig


@graph("Error Count by Treatment")
def error_count_by_treatment(data):
    import matplotlib.pyplot as plt
    from collections import Counter

    counts = Counter(row.get("treatment", "unknown") for row in data.get("errors", []))
    fig, ax = plt.subplots(figsize=(8, 4))
    treatments = sorted(counts.keys())
    ax.bar(treatments, [counts[t] for t in treatments], color="#e56b6f")
    ax.set_ylabel("Error count")
    ax.set_title("Errors by Treatment")
    plt.tight_layout()
    return fig
