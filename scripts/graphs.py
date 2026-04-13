"""Graph and table definitions for eval-live. Runs in the browser via Pyodide."""
import eval_live


def timings_by_treatment(data):
    import matplotlib.pyplot as plt
    from collections import defaultdict

    by_key = defaultdict(lambda: defaultdict(list))
    for row in data.get("timings", []):
        key = (row.get("file"), row.get("grind_line"))
        treatment = row.get("treatment", "unknown")
        by_key[key][treatment].extend(row.get("timing_list", []))

    all_treatments = set()
    for treatments in by_key.values():
        all_treatments.update(treatments.keys())

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


def mean_timing(data):
    """Pivot table: one row per (file, grind_line) with treatment means as columns."""
    from collections import defaultdict

    by_key = defaultdict(dict)
    suggestions_by_key = defaultdict(dict)
    for row in data.get("timings", []):
        key = (row.get("file", ""), row.get("grind_line", ""))
        treatment = row.get("treatment", "unknown")
        times = row.get("timing_list", [])
        mean = sum(times) / len(times) if times else 0
        by_key[key][treatment] = round(mean, 6)
        suggestion = row.get("applied_suggestion")
        if suggestion:
            suggestions_by_key[key][treatment] = suggestion

    all_treatments = sorted({t for ts in by_key.values() for t in ts})

    result = []
    for (file, grind_line), treatments in by_key.items():
        row = {"file": file, "grind_line": grind_line}
        for t in all_treatments:
            row[t] = treatments.get(t, "")
        applied = suggestions_by_key.get((file, grind_line), {})
        # Each entry is the suggestion applied at this specific grind call line.
        row["applied_suggestion"] = "\n\n---\n\n".join(
            f"{t}:\n{applied[t]}" for t in sorted(applied)
        )
        result.append(row)
    return result


def mean_timing_filter(filtered_rows, data):
    """Filter raw timings to rows matching the visible computed rows by primary key."""
    keys = {(r["file"], r["grind_line"]) for r in filtered_rows}
    return {
        **data,
        "timings": [r for r in data.get("timings", [])
                     if (r.get("file"), r.get("grind_line")) in keys],
    }


# Register everything
reg = eval_live.Registry()
reg.graph("Timings by Treatment", timings_by_treatment)
reg.graph("Error Count by Treatment", error_count_by_treatment)
reg.table("Mean Timing per Treatment", mean_timing, filter_source=mean_timing_filter)
eval_live.registry = reg
