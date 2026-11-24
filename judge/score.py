"""Rank verified snapshots in the order GitHub received them."""
# Read from the protected base revision at intake, including on a rerun.
SCORING_OPEN = False
OPENING = {"lower-bound": 99, "construction": 756}


def standings(entries):
    records = dict(OPENING)
    teams = {track: {} for track in OPENING}
    decisions = []
    for entry in sorted(entries, key=lambda row: row["run"]):
        track, team, bound = entry["track"], entry["team"], entry["bound_bytes"]
        previous = records[track]
        delta = None if previous is None else (
            bound - previous if track == "lower-bound" else previous - bound)
        improved = delta is None or delta > 0
        decisions.append({**entry, "previous": previous, "delta": delta, "record": improved})
        if improved:
            records[track] = bound
            teams[track][team] = decisions[-1]
    rankings = {}
    for track, results in teams.items():
        direction = -1 if track == "lower-bound" else 1
        rankings[track] = sorted(results.values(),
                                 key=lambda row: (direction * row["bound_bytes"], row["run"]))
    return {"opening": OPENING, "best": records, "rankings": rankings, "history": decisions}
