"""SQLite-backed results database for grind benchmarks."""
import json
import sqlite3
from pathlib import Path


class BenchDB:
    """SQLite-backed results database with two tables: timings and errors."""

    def __init__(self):
        self.conn = sqlite3.connect(":memory:")
        self.conn.execute("""
            CREATE TABLE timings (
                file TEXT NOT NULL,
                grind_line INTEGER NOT NULL,
                treatment TEXT NOT NULL,
                timing_list TEXT NOT NULL,
                PRIMARY KEY (file, grind_line, treatment)
            )
        """)
        self.conn.execute("""
            CREATE TABLE errors (
                file TEXT NOT NULL,
                grind_line INTEGER NOT NULL,
                treatment TEXT NOT NULL,
                error TEXT NOT NULL,
                PRIMARY KEY (file, grind_line, treatment)
            )
        """)

    def add_timing(self, file, grind_line, treatment, timings):
        self.conn.execute(
            "INSERT OR REPLACE INTO timings VALUES (?, ?, ?, ?)",
            (file, grind_line, treatment, json.dumps(timings)),
        )

    def add_error(self, file, grind_line, treatment, error):
        self.conn.execute(
            "INSERT OR REPLACE INTO errors VALUES (?, ?, ?, ?)",
            (file, grind_line, treatment, error),
        )

    def to_dict(self):
        timings = [
            {"file": r[0], "grind_line": r[1], "treatment": r[2],
             "timing_list": json.loads(r[3])}
            for r in self.conn.execute("SELECT * FROM timings")
        ]
        errors = [
            {"file": r[0], "grind_line": r[1], "treatment": r[2],
             "error": r[3]}
            for r in self.conn.execute("SELECT * FROM errors")
        ]
        return {"timings": timings, "errors": errors}

    def save_json(self, path):
        Path(path).write_text(json.dumps(self.to_dict(), indent=2))
