"""Producer options, read from producer/config.json; an environment variable overrides each.

  filter_unifiers   (CONPANNA_FILTER=1 or 0)
      Compute a problem's unifiers with Maude's filtered variant unification, which drops
      unifiers that are instances of others: fewer answers, still complete. Otherwise
      plain unification, Maude's full list. Lean is not affected: it certifies whatever
      list it is given.
"""
import json, os, pathlib

CONFIG = pathlib.Path(__file__).resolve().parents[1] / "config.json"


def filter_unifiers() -> bool:
    env = os.environ.get("CONPANNA_FILTER")
    if env is not None:
        return env.strip().lower() not in ("", "0", "false", "no")
    return bool(CONFIG.exists() and json.loads(CONFIG.read_text()).get("filter_unifiers", False))
