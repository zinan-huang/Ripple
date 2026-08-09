#!/usr/bin/env python3
"""Playbook §3.1 acceptance audit for Ripple's public Tri library.

Mechanises group A (points 1-7) and the mechanisable part of group B
(point 10: Prop-valued defs that are carried as hypotheses but never produced).

Group C (points 11-17) is semantic and cannot be mechanised; this script only
prints the worklist for it.

Usage:  python3 scripts/audit_tri.py
Exit code 0 iff every mechanical point passes.
"""
import re
import subprocess
import sys

print = __import__("functools").partial(print, flush=True)  # long run: never buffer
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN = sorted((ROOT / "Tri").rglob("*.lean")) + [ROOT / "Tri.lean"]

FAILURES = []
NOTES = []


def read(p):
    return p.read_text(encoding="utf-8", errors="replace")


def strip_comments(src):
    """Remove block comments and line comments so greps do not hit prose."""
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    src = re.sub(r"--[^\n]*", "", src)
    return src


def _strip_groups(text):
    """Remove balanced (), [], {} groups -- i.e. all binders -- from a header."""
    out, depth = [], 0
    for ch in text:
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0:
            out.append(ch)
    return "".join(out)


def _theorem_headers(src):
    """Every theorem's full header: binders AND conclusion, up to `:=`.

    Unlike `_theorem_conclusions`, binders are KEPT -- a hidden ℕ-truncation in
    a hypothesis weakens a theorem just as much as one in the conclusion.
    """
    heads = []
    for m in re.finditer(r"\btheorem\s+[\w.'’]+", src):
        rest = src[m.end():]
        stop = rest.find(":=")
        heads.append(rest if stop < 0 else rest[:stop])
    return heads


def _theorem_conclusions(src):
    """The conclusion of every theorem: the text after the top-level `:`.

    Binders are stripped first, so a colon inside `(n : ℕ)` cannot be
    mistaken for the one that introduces the conclusion.
    """
    concls = []
    for m in re.finditer(r"\btheorem\s+[\w.'’]+", src):
        rest = src[m.end():]
        stop = rest.find(":=")
        header = rest if stop < 0 else rest[:stop]
        bare = _strip_groups(header)
        idx = bare.find(":")
        if idx >= 0:
            concls.append(bare[idx + 1:])
    return concls


def point(n, desc):
    print(f"\n[{n}] {desc}")


def ok(msg):
    print(f"    PASS  {msg}")


def fail(n, msg):
    print(f"    FAIL  {msg}")
    FAILURES.append((n, msg))


# ---------------------------------------------------------------- group A
def group_a():
    bodies = {p: strip_comments(read(p)) for p in LEAN}

    for n, desc, pat in [
        (1, "0 sorry", r"\bsorry\b"),
        (2, "0 admit / unsafe", r"\badmit\b|\bunsafe\b"),
        (3, "0 custom axiom", r"^\s*axiom\s"),
        (4, "0 native_decide", r"native_decide"),
    ]:
        point(n, desc)
        hits = []
        for p, b in bodies.items():
            for m in re.finditer(pat, b, flags=re.M):
                line = b[: m.start()].count("\n") + 1
                hits.append(f"{p.relative_to(ROOT)}:{line}")
        if hits:
            for h in hits[:10]:
                fail(n, h)
        else:
            ok(f"no matches for /{pat}/ in {len(LEAN)} files (comments stripped)")

    # point 6 — every Prop-valued def must either be a PREDICATE (takes a state
    # argument and is used as a target/region) or be discharged by a theorem.
    point(6, "no `def/abbrev : Prop` impersonating a theorem")
    propdefs = {}
    for p, b in bodies.items():
        for m in re.finditer(r"(?:def|abbrev)\s+([A-Za-z_][\w.'’]*)[^=]*?:\s*Prop\b", b, flags=re.S):
            propdefs[m.group(1)] = p.relative_to(ROOT)
    all_src = "\n".join(bodies.values())
    conclusions = _theorem_conclusions(all_src)
    carried, produced, predicate = [], [], []
    for name, loc in sorted(propdefs.items()):
        # produced: some theorem's CONCLUSION mentions `Name`.
        # Binders must be stripped first -- an earlier version matched with
        # `[^:]*?`, which cannot cross the colon in a binder like `(n : ℕ)`,
        # so every parameterised theorem was missed and the worklist was 57
        # false positives deep.
        prod = any(re.search(rf"\b{re.escape(name)}\b", c) for c in conclusions)
        # carried: appears as a named hypothesis `(h... : Name ...)`
        carr = re.search(rf"\(\s*h[\w'’]*\s*:\s*{re.escape(name)}\b", all_src)
        if prod:
            produced.append(name)
        elif carr:
            carried.append((name, loc))
        else:
            predicate.append(name)
    ok(f"{len(propdefs)} Prop-valued defs: {len(produced)} discharged by a theorem, "
       f"{len(predicate)} used as predicates/targets, {len(carried)} carried as hypotheses")
    for name, loc in carried:
        NOTES.append(f"point 10 worklist: `{name}` ({loc}) is CARRIED as a hypothesis and "
                     f"never produced — confirm it is an honest state ②/③ premise, not the "
                     f"conclusion's hard half")
    if carried:
        print(f"    NOTE  {len(carried)} carried-but-unproduced Prop defs -> group-B worklist")


# ------------------------------------------------- point 6b (ℕ-subtraction)
def nat_subtraction_defs():
    """ℕ-valued defs whose body contains a subtraction.

    The hard rule bans ℕ-subtraction in STATEMENTS.  A ℕ-valued *def* that
    contains one is not itself a violation -- but if that def appears in a
    statement, the truncation is hidden behind a name and the statement can be
    silently weaker than intended unless a room hypothesis makes the
    subtraction exact.

    This check cannot decide whether the guard is present; it produces the
    worklist so a human can confirm each one.  It is reported as a NOTE, never
    a failure, because the pattern is legitimate and widespread here (band
    arithmetic).
    """
    point("6b", "ℕ-valued defs containing subtraction (worklist, not a failure)")
    pat = (r"(?:noncomputable\s+)?def\s+([\w.'’]+)([^=]*?):\s*ℕ\s*:=\s*"
           r"((?:.|\n)*?)(?=\n(?:noncomputable\s+)?(?:def|theorem|abbrev|instance|end|/-)|\Z)")
    found = []
    for p_ in LEAN:
        body = strip_comments(read(p_))
        for m in re.finditer(pat, body):
            name, defbody = m.group(1), m.group(3)
            if re.search(r"\w\s*-\s*[\w(]", defbody):
                found.append((name, p_.relative_to(ROOT)))
    # A def containing subtraction is only risky if it reaches a STATEMENT --
    # binders included, since a hidden truncation in a hypothesis weakens the
    # theorem just as much as one in the conclusion.  Defs used only inside
    # proof terms are harmless and are filtered out here.
    all_src = "\n".join(strip_comments(read(p_)) for p_ in LEAN)
    headers = "\n".join(_theorem_headers(all_src))
    in_stmt = [(n, l) for n, l in found
               if re.search(rf"\b{re.escape(n)}\b", headers)]
    ok(f"{len(found)} ℕ-valued defs contain a subtraction; "
       f"{len(in_stmt)} of them reach a theorem statement")
    for name, loc in in_stmt:
        # Short names are matched by bare identifier, so "reaches a statement"
        # is unreliable for them -- `y` matches every bound variable named y.
        caveat = ("  [NAME TOO SHORT to match reliably -- verify by hand]"
                  if len(name) <= 2 else "")
        NOTES.append(f"point 6b worklist: `{name}` ({loc}) is a ℕ-valued def "
                     f"containing subtraction AND reaches a theorem statement -- "
                     f"confirm the subtraction is exact, ideally by carrying the "
                     f"guard in a SUBSET TYPE (see `Tri/ByzantineKernel.lean`'s "
                     f"`y`, whose guard is the state invariant `s.2`, so no "
                     f"call-site hypothesis is ever needed){caveat}")
    return in_stmt


# ---------------------------------------------------------------- group A.7
def full_build():
    point(7, "default public build")
    # The default target checks Ripple's public import closure and all of Tri.
    # The optional compute-from-scratch Sturm/CRT certificates remain available
    # through the dedicated `SturmCRT` target (and the exhaustive `Ripple`
    # target), but intentionally do not impose a multi-hour cold-build cost on
    # ordinary users.
    r = subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True, timeout=7200)
    if r.returncode == 0 and "Build completed successfully" in (r.stdout + r.stderr):
        tail = [l for l in (r.stdout + r.stderr).splitlines() if "Build completed" in l]
        ok(tail[-1] if tail else "build ok")
    else:
        fail(7, "lake build did not complete successfully")
    return r.stdout + r.stderr


# ---------------------------------------------------------------- point 5
def axiom_audit(buildlog):
    point(5, "#print axioms = the core three, per theorem")
    # The default build also checks Ripple's public import closure.  Restrict
    # this audit's statistics to diagnostics emitted by source files in Tri.
    # Preserve continuation lines: Lean wraps a few long declaration names
    # before printing the complete axiom list.
    tri_blocks = []
    current = None
    for line in buildlog.splitlines():
        if re.match(r"(?:info|warning): ", line):
            if current is not None:
                tri_blocks.append("\n".join(current))
            current = [line] if re.match(
                r"(?:info|warning): Tri(?:/|\.lean:)", line
            ) else None
        elif current is not None:
            current.append(line)
    if current is not None:
        tri_blocks.append("\n".join(current))
    tri_log = "\n".join(tri_blocks)
    printed = re.findall(r"'([\w.'’]+)' depends on axioms: \[([^\]]*)\]", tri_log)
    if not printed:
        fail(5, "no `#print axioms` output captured (was the build fully cached?)")
        return
    bad = [(n, a) for n, a in printed
           if set(x.strip() for x in a.split(",")) - {"propext", "Classical.choice", "Quot.sound"}]
    noaxiom = re.findall(r"'([\w.'’]+)' does not depend on any axioms", tri_log)
    if bad:
        for n, a in bad[:10]:
            fail(5, f"{n} depends on [{a}]")
    else:
        ok(f"{len(printed)} theorems print exactly the core three; "
           f"{len(noaxiom)} print no axioms at all")


def main():
    print("=" * 72)
    print("Lean-playbook §3.1 acceptance audit —", ROOT)
    print("=" * 72)
    group_a()
    nat_subtraction_defs()
    log = full_build()
    axiom_audit(log)

    print("\n" + "=" * 72)
    if NOTES:
        print("GROUP-B / GROUP-C WORKLIST (not mechanically decidable):")
        for n in NOTES:
            print("  - " + n)
    print("=" * 72)
    if FAILURES:
        print(f"MECHANICAL AUDIT: {len(FAILURES)} FAILURE(S)")
        return 1
    print("MECHANICAL AUDIT (points 1-7): ALL GREEN")
    print("Points 8-17 require manual signature and semantic review.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
