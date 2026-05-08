#!/usr/bin/env python3
"""Recurrence-based Phi_41 Sturm coefficient checker.

For

    Q_j(q) = E4(q)^(3j) * Delta(q)^(42-j)

the Ramanujan identities imply the formal recurrence

    E4 * q dQ_j/dq = (42 E2 E4 - j E6) * Q_j.

Since `Q_j` has leading term `q^(42-j)`, this determines all later
coefficients without building dense power tables.  The same recurrence is used
for the compressed q -> q^41 side at the smaller precision.

This is still an external exact checker, not a Lean proof.  Its purpose is to
be the algorithmic basis for a future generated Lean certificate.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import math
import shutil
import subprocess
import sys
import tempfile
from functools import lru_cache
from pathlib import Path
from typing import Optional


GP_TERMS = r"""
p = polmodular(41);
for(i = 0, 42, for(j = 0, 42, c = polcoef(polcoef(p, i, x), j, y); if(c != 0, printf("%Ps\t%ld\t%ld\n", c, i, j))));
quit;
"""


def run_gp_terms(stack: str) -> list[tuple[int, int, int]]:
    gp = shutil.which("gp")
    if gp is None:
        raise SystemExit("PARI/GP executable `gp` was not found on PATH")

    with tempfile.NamedTemporaryFile("w", suffix=".gp", delete=False) as handle:
        handle.write(GP_TERMS)
        gp_file = Path(handle.name)

    try:
        proc = subprocess.run(
            [gp, "-q", "-s", stack, str(gp_file)],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
    finally:
        gp_file.unlink(missing_ok=True)

    terms: list[tuple[int, int, int]] = []
    for raw in proc.stdout.splitlines():
        if not raw.strip():
            continue
        c, i, j = raw.split("\t")
        terms.append((int(c), int(i), int(j)))
    if len(terms) != 1766:
        raise SystemExit(f"unexpected Phi_41 term count: {len(terms)}")
    return terms


@lru_cache(maxsize=None)
def sigma_power(n: int, k: int) -> int:
    if n <= 0:
        return 0
    s = 0
    d = 1
    while d * d <= n:
        if n % d == 0:
            s += d**k
            e = n // d
            if e != d:
                s += e**k
        d += 1
    return s


def convolve(a: list[int], b: list[int], mod: Optional[int]) -> list[int]:
    n = len(a)
    out = [0] * n
    for i, ai in enumerate(a):
        if ai == 0:
            continue
        upto = n - i
        for j in range(upto):
            bj = b[j]
            if bj:
                out[i + j] += ai * bj
    if mod is not None:
        out = [x % mod for x in out]
    return out


def modular_series_data(n: int, mod: Optional[int]) -> tuple[list[int], list[int], list[int], list[int]]:
    e2 = [0] * n
    e4 = [0] * n
    e6 = [0] * n
    e2[0] = e4[0] = e6[0] = 1
    for k in range(1, n):
        e2[k] = -24 * sigma_power(k, 1)
        e4[k] = 240 * sigma_power(k, 3)
        e6[k] = -504 * sigma_power(k, 5)
    if mod is not None:
        e2 = [x % mod for x in e2]
        e4 = [x % mod for x in e4]
        e6 = [x % mod for x in e6]
    e2e4 = convolve(e2, e4, mod)
    return e2, e4, e6, e2e4


def q_family_coeffs(limit: int, mod: Optional[int]) -> list[list[int]]:
    """Return rows `j = 0..42` for `E4^(3j) Delta^(42-j)`."""
    _e2, e4, e6, e2e4 = modular_series_data(limit, mod)
    rows: list[list[int]] = []
    for j in range(43):
        valuation = 42 - j
        f = [0] * limit
        if valuation < limit:
            f[valuation] = 1 if mod is None else 1 % mod
        h = [0] * limit
        for n in range(limit):
            h[n] = 42 * e2e4[n] - j * e6[n]
        if mod is not None:
            h = [x % mod for x in h]
        for n in range(valuation + 1, limit):
            s = 0
            for a in range(1, n + 1):
                s += (h[a] - e4[a] * (n - a)) * f[n - a]
            denom = n - valuation
            if mod is None:
                if s % denom != 0:
                    raise ArithmeticError((j, n, s, denom))
                f[n] = s // denom
            else:
                f[n] = (s % mod) * pow(denom, -1, mod) % mod
        rows.append(f)
    return rows


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def is_prime_u64(n: int) -> bool:
    """Deterministic Miller-Rabin primality test for 64-bit positive integers."""
    if n < 2:
        return False
    small_primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
    for p in small_primes:
        if n == p:
            return True
        if n % p == 0:
            return False

    d = n - 1
    s = 0
    while d % 2 == 0:
        s += 1
        d //= 2

    def witness(a: int) -> bool:
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            return False
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                return False
        return True

    # Deterministic for n < 2^64.
    for a in [2, 3, 5, 7, 11, 13, 17]:
        if a % n and witness(a):
            return False
    return True


def parse_prime_list(raw: str) -> list[int]:
    primes = [int(p.strip()) for p in raw.split(",") if p.strip()]
    if not primes:
        raise SystemExit("no primes were parsed")
    if len(set(primes)) != len(primes):
        raise SystemExit("prime list contains duplicates")
    bad = [p for p in primes if p >= 2**64 or not is_prime_u64(p)]
    if bad:
        raise SystemExit(f"prime list contains non-prime or non-u64 values: {bad}")
    return primes


def previous_prime(n: int) -> int:
    if n < 2:
        raise ValueError("no prime below 2")
    if n == 2:
        return 2
    candidate = n if n % 2 else n - 1
    while candidate >= 3:
        if is_prime_u64(candidate):
            return candidate
        candidate -= 2
    return 2


def descending_primes(count: int, bits: int) -> list[int]:
    if count <= 0:
        raise SystemExit("--auto-prime-count must be positive")
    if bits < 2 or bits > 63:
        raise SystemExit("--auto-prime-bits must be between 2 and 63")
    out: list[int] = []
    candidate = (1 << bits) - 1
    while len(out) < count:
        p = previous_prime(candidate)
        out.append(p)
        candidate = p - 2
    return out


def resolve_primes(raw: str, auto_count: int, auto_bits: int) -> list[int]:
    if raw.strip():
        return parse_prime_list(raw)
    if auto_count:
        return descending_primes(auto_count, auto_bits)
    raise SystemExit("provide --primes or --auto-prime-count")


def resolve_primes_covering_bits(
    raw: str,
    auto_count: int,
    auto_bits: int,
    needed_bits: int,
) -> list[int]:
    """Resolve a prime list and extend it until its product has enough bits."""
    if auto_bits < 2 or auto_bits > 63:
        raise SystemExit("--auto-prime-bits must be between 2 and 63")
    if raw.strip():
        primes = parse_prime_list(raw)
    elif auto_count:
        primes = descending_primes(auto_count, auto_bits)
    else:
        primes = []

    used = set(primes)
    product = math.prod(primes)
    candidate = (1 << auto_bits) - 1
    if primes:
        candidate = min(candidate, min(primes) - 2)
    while product.bit_length() <= needed_bits:
        p = previous_prime(candidate)
        while p in used:
            candidate = p - 2
            p = previous_prime(candidate)
        primes.append(p)
        used.add(p)
        product *= p
        candidate = p - 2
    return primes


NEG_INF = float("-inf")


def log2_int(n: int) -> float:
    if n <= 0:
        return NEG_INF
    return math.log2(n)


def log2_add(a: float, b: float) -> float:
    if a == NEG_INF:
        return b
    if b == NEG_INF:
        return a
    if a < b:
        a, b = b, a
    return a + math.log2(1.0 + 2.0 ** (b - a))


def log2_sum(values) -> float:
    out = NEG_INF
    for value in values:
        out = log2_add(out, value)
    return out


def q_family_abs_bounds(limit: int) -> list[list[int]]:
    """Triangle-inequality bounds for rows `E4^(3j) Delta^(42-j)`.

    These are not tight.  They are intended to size a future CRT certificate:
    if enough prime moduli make every Sturm-range coefficient vanish and their
    product is larger than twice the bound below, the corresponding integer
    coefficient must be zero.
    """
    _e2, e4, e6, e2e4 = modular_series_data(limit, None)
    e4_abs = [abs(x) for x in e4]
    e6_abs = [abs(x) for x in e6]
    e2e4_abs = [abs(x) for x in e2e4]
    rows: list[list[int]] = []
    for j in range(43):
        valuation = 42 - j
        f = [0] * limit
        if valuation < limit:
            f[valuation] = 1
        h_abs = [42 * e2e4_abs[n] + j * e6_abs[n] for n in range(limit)]
        for n in range(valuation + 1, limit):
            s = 0
            for a in range(1, n + 1):
                s += (h_abs[a] + e4_abs[a] * (n - a)) * f[n - a]
            f[n] = ceil_div(s, n - valuation)
        rows.append(f)
    return rows


def q_family_log_bounds(limit: int) -> list[list[float]]:
    """Fast log2 triangle-inequality bounds for the recurrence rows.

    This is a sizing tool for CRT experiments, not a formal certificate.  The
    reported bit count includes a small safety margin for floating-point
    roundoff.
    """
    _e2, e4, e6, e2e4 = modular_series_data(limit, None)
    e4_log = [log2_int(abs(x)) for x in e4]
    e6_log = [log2_int(abs(x)) for x in e6]
    e2e4_log = [log2_int(abs(x)) for x in e2e4]
    rows: list[list[float]] = []
    for j in range(43):
        valuation = 42 - j
        f = [NEG_INF] * limit
        if valuation < limit:
            f[valuation] = 0.0
        h_log = [
            log2_add(log2_int(42) + e2e4_log[n], log2_int(j) + e6_log[n])
            for n in range(limit)
        ]
        for n in range(valuation + 1, limit):
            s_log = NEG_INF
            for a in range(1, n + 1):
                term_factor = log2_add(
                    h_log[a],
                    e4_log[a] + log2_int(n - a),
                )
                s_log = log2_add(s_log, term_factor + f[n - a])
            f[n] = s_log - log2_int(n - valuation)
        rows.append(f)
    return rows


def final_coeff_abs_bounds(bound: int, extra: int, stack: str) -> list[int]:
    precision = bound + extra
    small = (precision + 40) // 41
    terms = run_gp_terms(stack)
    q_rows = q_family_abs_bounds(precision)
    p_rows = q_family_abs_bounds(small)

    row_coeff_abs = [[0] * 43 for _ in range(43)]
    for c, i, j in terms:
        row_coeff_abs[i][j] += abs(c)

    q_parts = [[0] * precision for _ in range(43)]
    for x in range(43):
        for y in range(43):
            c = row_coeff_abs[x][y]
            if c == 0:
                continue
            qrow = q_rows[y]
            for n in range(precision):
                if qrow[n]:
                    q_parts[x][n] += c * qrow[n]

    bounds = [0] * precision
    for x in range(43):
        prow = p_rows[x]
        qpart = q_parts[x]
        for m, pm in enumerate(prow):
            if pm == 0:
                continue
            shift = 41 * m
            if shift >= precision:
                break
            for n in range(precision - shift):
                qn = qpart[n]
                if qn:
                    bounds[shift + n] += pm * qn
    return bounds


def final_coeff_log_bound_bits(bound: int, extra: int, stack: str, safety_bits: int) -> tuple[int, int]:
    precision = bound + extra
    small = (precision + 40) // 41
    terms = run_gp_terms(stack)
    q_rows = q_family_log_bounds(precision)
    p_rows = q_family_log_bounds(small)

    row_coeff_log = [[NEG_INF] * 43 for _ in range(43)]
    for c, i, j in terms:
        row_coeff_log[i][j] = log2_add(row_coeff_log[i][j], log2_int(abs(c)))

    q_parts = [[NEG_INF] * precision for _ in range(43)]
    for x in range(43):
        for y in range(43):
            c_log = row_coeff_log[x][y]
            if c_log == NEG_INF:
                continue
            qrow = q_rows[y]
            for n in range(precision):
                if qrow[n] != NEG_INF:
                    q_parts[x][n] = log2_add(q_parts[x][n], c_log + qrow[n])

    max_idx = 0
    max_log = NEG_INF
    for d in range(bound):
        coeff_log = NEG_INF
        for x in range(43):
            prow = p_rows[x]
            qpart = q_parts[x]
            for m, pm_log in enumerate(prow):
                if pm_log == NEG_INF:
                    continue
                shift = 41 * m
                if shift > d:
                    break
                qn_log = qpart[d - shift]
                if qn_log != NEG_INF:
                    coeff_log = log2_add(coeff_log, pm_log + qn_log)
        if coeff_log > max_log:
            max_log = coeff_log
            max_idx = d

    if max_log == NEG_INF:
        return 0, safety_bits
    return max_idx, math.ceil(max_log) + safety_bits


def final_coeffs_with_terms(
    bound: int,
    extra: int,
    mod: Optional[int],
    terms: list[tuple[int, int, int]],
) -> list[int]:
    _q_rows, _p_rows, _row_coeffs, _q_parts, contributions, coeffs = (
        final_coeffs_components_with_terms(bound, extra, mod, terms)
    )
    return coeffs


def final_coeffs_components_with_terms(
    bound: int,
    extra: int,
    mod: Optional[int],
    terms: list[tuple[int, int, int]],
) -> tuple[
    list[list[int]],
    list[list[int]],
    list[list[int]],
    list[list[int]],
    list[list[int]],
    list[int],
]:
    precision = bound + extra
    small = (precision + 40) // 41
    q_rows = q_family_coeffs(precision, mod)
    p_rows = q_family_coeffs(small, mod)

    row_coeffs = [[0] * 43 for _ in range(43)]
    for c, i, j in terms:
        if mod is not None:
            c %= mod
        row_coeffs[i][j] += c
        if mod is not None:
            row_coeffs[i][j] %= mod

    q_parts = [[0] * precision for _ in range(43)]
    for x in range(43):
        out = q_parts[x]
        for y in range(43):
            c = row_coeffs[x][y]
            if c == 0:
                continue
            qrow = q_rows[y]
            for n, qn in enumerate(qrow):
                if qn:
                    out[n] += c * qn

    contributions = [[0] * precision for _ in range(43)]
    for x in range(43):
        prow = p_rows[x]
        qpart = q_parts[x]
        contribution = contributions[x]
        for m, pm in enumerate(prow):
            if pm == 0:
                continue
            shift = 41 * m
            if shift >= precision:
                break
            scale = pm
            for n in range(precision - shift):
                qn = qpart[n]
                if qn:
                    contribution[shift + n] += scale * qn
    if mod is not None:
        contributions = [[x % mod for x in row] for row in contributions]
    coeffs = [0] * precision
    for contribution in contributions:
        for n, value in enumerate(contribution):
            coeffs[n] += value
    if mod is not None:
        coeffs = [x % mod for x in coeffs]
    return q_rows, p_rows, row_coeffs, q_parts, contributions, coeffs


def check_coeffs(bound: int, coeffs: list[int]) -> tuple[int, bool]:
    precision = len(coeffs)
    valuation = precision
    for idx, c in enumerate(coeffs):
        if c != 0:
            valuation = idx
            break
    return valuation, valuation >= bound


def check_with_terms(
    bound: int,
    extra: int,
    mod: Optional[int],
    terms: list[tuple[int, int, int]],
) -> tuple[int, bool]:
    coeffs = final_coeffs_with_terms(bound, extra, mod, terms)
    return check_coeffs(bound, coeffs)


def check(bound: int, extra: int, mod: Optional[int], stack: str) -> tuple[int, bool]:
    return check_with_terms(bound, extra, mod, run_gp_terms(stack))


def print_result(bound: int, extra: int, prime: int, valuation: int, ok: bool) -> None:
    print(f"BOUND\t{bound}", flush=True)
    print(f"PREC\t{bound + extra}", flush=True)
    print(f"SMALL_PREC\t{(bound + extra + 40) // 41}", flush=True)
    print(f"MOD_PRIME\t{prime}", flush=True)
    print(f"VALUATION\t{valuation}", flush=True)
    print(f"STURM_ZERO\t{1 if ok else 0}", flush=True)


def residue_hash(coeffs: list[int], modulus: int, bound: int) -> str:
    """Stable hash of the Sturm-range residues modulo one prime."""
    width = max(1, (modulus.bit_length() + 7) // 8)
    digest = hashlib.sha256()
    for coeff in coeffs[:bound]:
        digest.update((coeff % modulus).to_bytes(width, "big"))
    return digest.hexdigest()


def prime_manifest_row(bound: int, extra: int, prime: int, terms: list[tuple[int, int, int]]) -> dict:
    coeffs = final_coeffs_with_terms(bound, extra, prime, terms)
    valuation, ok = check_coeffs(bound, coeffs)
    return {
        "prime": prime,
        "valuation": valuation,
        "sturm_zero": ok,
        "sturm_residue_sha256": residue_hash(coeffs, prime, bound),
    }


def verify_prime_manifest_row(
    bound: int,
    extra: int,
    row: dict,
    terms: list[tuple[int, int, int]],
) -> tuple[bool, list[str]]:
    errors: list[str] = []
    prime = int(row["prime"])
    coeffs = final_coeffs_with_terms(bound, extra, prime, terms)
    valuation, ok = check_coeffs(bound, coeffs)
    expected_hash = residue_hash(coeffs, prime, bound)
    if row.get("valuation") != valuation:
        errors.append(
            f"prime {prime}: valuation expected {valuation}, got {row.get('valuation')}"
        )
    if row.get("sturm_zero") != ok:
        errors.append(
            f"prime {prime}: sturm_zero expected {ok}, got {row.get('sturm_zero')}"
        )
    if row.get("sturm_residue_sha256") != expected_hash:
        errors.append(f"prime {prime}: residue hash mismatch")
    return ok, errors


def write_json_file(path: str, payload: dict) -> None:
    target = Path(path)
    tmp = target.with_name(target.name + ".tmp")
    with open(tmp, "w", encoding="utf-8") as handle:
        handle.write(json.dumps(payload, indent=2, sort_keys=True))
        handle.write("\n")
    tmp.replace(target)


def partial_crt_manifest(
    bound: int,
    extra: int,
    primes: list[int],
    prime_results: list[dict],
) -> dict:
    return {
        "format": "phi41-recurrence-crt-manifest-v1",
        "partial": True,
        "bound": bound,
        "extra": extra,
        "precision": bound + extra,
        "small_precision": (bound + extra + 40) // 41,
        "planned_prime_count": len(primes),
        "planned_primes": primes,
        "prime_count": len(prime_results),
        "prime_results": prime_results,
    }


def crt_manifest(
    bound: int,
    extra: int,
    primes: list[int],
    stack: str,
    exact_bound: bool,
    log_bound: bool,
    safety_bits: int,
    existing_manifest: Optional[dict] = None,
    precomputed_log_bound: Optional[tuple[int, int]] = None,
    checkpoint_path: str = "",
    jobs: int = 1,
) -> dict:
    terms = run_gp_terms(stack)
    product = math.prod(primes)
    cached_rows: dict[int, dict] = {}
    if existing_manifest is not None:
        if existing_manifest.get("format") != "phi41-recurrence-crt-manifest-v1":
            raise ValueError("resume manifest has unexpected format")
        if int(existing_manifest.get("bound", -1)) != bound:
            raise ValueError("resume manifest bound does not match requested bound")
        if int(existing_manifest.get("extra", -1)) != extra:
            raise ValueError("resume manifest extra does not match requested extra")
        for row in existing_manifest.get("prime_results", []):
            cached_rows[int(row["prime"])] = row

    rows_by_prime: dict[int, dict] = {}
    for prime in primes:
        if prime in cached_rows:
            row = dict(cached_rows[prime])
            rows_by_prime[prime] = row
            print(
                f"CRT_RESUME\t{prime}\tVALUATION\t{int(row['valuation'])}",
                file=sys.stderr,
                flush=True,
            )

    missing_primes = [prime for prime in primes if prime not in rows_by_prime]
    if jobs <= 1 or len(missing_primes) <= 1:
        for prime in missing_primes:
            print(f"CRT_COMPUTE\t{prime}", file=sys.stderr, flush=True)
            row = prime_manifest_row(bound, extra, prime, terms)
            rows_by_prime[prime] = row
            print(
                f"CRT_DONE\t{prime}\tVALUATION\t{int(row['valuation'])}",
                file=sys.stderr,
                flush=True,
            )
            if checkpoint_path:
                partial_rows = [rows_by_prime[p] for p in primes if p in rows_by_prime]
                write_json_file(
                    checkpoint_path,
                    partial_crt_manifest(bound, extra, primes, partial_rows),
                )
    else:
        print(
            f"CRT_PARALLEL_JOBS\t{jobs}\tMISSING_PRIMES\t{len(missing_primes)}",
            file=sys.stderr,
            flush=True,
        )
        with concurrent.futures.ProcessPoolExecutor(max_workers=jobs) as executor:
            future_to_prime = {
                executor.submit(prime_manifest_row, bound, extra, prime, terms): prime
                for prime in missing_primes
            }
            for future in concurrent.futures.as_completed(future_to_prime):
                prime = future_to_prime[future]
                row = future.result()
                rows_by_prime[prime] = row
                print(
                    f"CRT_DONE\t{prime}\tVALUATION\t{int(row['valuation'])}",
                    file=sys.stderr,
                    flush=True,
                )
                if checkpoint_path:
                    partial_rows = [rows_by_prime[p] for p in primes if p in rows_by_prime]
                    write_json_file(
                        checkpoint_path,
                        partial_crt_manifest(bound, extra, primes, partial_rows),
                    )

    prime_results = [rows_by_prime[prime] for prime in primes]
    all_sturm_zero = all(bool(row["sturm_zero"]) for row in prime_results)

    manifest = {
        "format": "phi41-recurrence-crt-manifest-v1",
        "bound": bound,
        "extra": extra,
        "precision": bound + extra,
        "small_precision": (bound + extra + 40) // 41,
        "prime_count": len(primes),
        "primes_distinct": len(set(primes)) == len(primes),
        "primes_verified_u64_miller_rabin": all(is_prime_u64(p) for p in primes),
        "prime_product_bits": product.bit_length(),
        "prime_product": str(product),
        "all_sturm_zero": all_sturm_zero,
        "prime_results": prime_results,
    }

    if exact_bound:
        bounds = final_coeff_abs_bounds(bound, extra, stack)
        sturm_bounds = bounds[:bound]
        max_bound = max(sturm_bounds) if sturm_bounds else 0
        max_idx = sturm_bounds.index(max_bound) if sturm_bounds else 0
        manifest["exact_bound"] = {
            "max_bound_index": max_idx,
            "max_bound_bits": max_bound.bit_length(),
            "crt_product_bits_needed": max_bound.bit_length() + 1,
            "max_bound": str(max_bound),
            "product_gt_max_bound": product > max_bound,
        }

    if log_bound:
        if precomputed_log_bound is None:
            max_idx, max_bits = final_coeff_log_bound_bits(
                bound, extra, stack, safety_bits
            )
        else:
            max_idx, max_bits = precomputed_log_bound
        manifest["log_bound"] = {
            "max_log_bound_index": max_idx,
            "safety_bits": safety_bits,
            "max_log_bound_bits": max_bits,
            "crt_product_bits_needed": max_bits + 1,
            "product_bits_gt_needed": product.bit_length() > max_bits + 1,
        }

    return manifest


def lean_prime_list_snippet(primes: list[int], name: str) -> str:
    list_literal = "[" + ", ".join(str(p) for p in primes) + "]"
    rcases = " | ".join(["rfl"] * len(primes))
    return "\n".join(
        [
            f"def {name} : List ℕ := {list_literal}",
            "",
            f"theorem {name}_nodup : {name}.Nodup := by",
            f"  simp [{name}]",
            "",
            f"theorem {name}_prime : ∀ p ∈ {name}, Nat.Prime p := by",
            "  intro p hp",
            f"  simp [{name}] at hp",
            f"  rcases hp with {rcases} <;> norm_num",
            "",
        ]
    )


def lean_int_array_literal(values: list[int]) -> str:
    return "#[" + ", ".join(str(v) for v in values) + "]"


def lean_row_table_literal(rows: list[list[int]]) -> str:
    return "#[" + ",\n  ".join(lean_int_array_literal(row) for row in rows) + "]"


def lean_row_table_data(
    bound: int,
    prime: int,
    name: str,
    terms: Optional[list[tuple[int, int, int]]] = None,
    prefixes: bool = False,
    coeffs_only: bool = False,
) -> str:
    """Emit Lean array literals for the modular recurrence row tables."""
    if prime <= bound:
        warning = (
            f"/- WARNING: prime {prime} is not larger than bound {bound}; "
            "row-table recurrence cancellation will need a larger modulus. -/"
        )
    else:
        warning = ""
    small = (bound + 40) // 41
    qe2, qe4, qe6, qe2e4 = modular_series_data(bound, prime)
    pe2, pe4, pe6, pe2e4 = modular_series_data(small, prime)
    q_rows = [] if coeffs_only else q_family_coeffs(bound, prime)
    p_rows = [] if coeffs_only else q_family_coeffs(small, prime)
    q_parts = None
    contributions = None
    final_coeffs = None
    qpart_prefixes = None
    contribution_prefixes = None
    final_prefix = None
    if terms is not None:
        if coeffs_only:
            raise SystemExit("--lean-row-table-data-coeffs-only cannot be combined with final data")
        _q_rows, _p_rows, row_coeffs, q_parts, contributions, final_coeffs = (
            final_coeffs_components_with_terms(bound, 0, prime, terms)
        )
        if prefixes:
            qpart_prefixes = []
            for x in range(43):
                row = [0] * (44 * bound)
                for y in range(43):
                    coeff = row_coeffs[x][y]
                    for n in range(bound):
                        prev = row[y * bound + n]
                        term = coeff * q_rows[y][n]
                        row[(y + 1) * bound + n] = (prev + term) % prime
                qpart_prefixes.append(row)

            contribution_prefixes = []
            for x in range(43):
                row = [0] * ((small + 1) * bound)
                for m in range(small):
                    for n in range(bound):
                        prev = row[m * bound + n]
                        if 41 * m <= n:
                            term = p_rows[x][m] * q_parts[x][n - 41 * m]
                        else:
                            term = 0
                        row[(m + 1) * bound + n] = (prev + term) % prime
                contribution_prefixes.append(row)

            final_prefix = [0] * (44 * bound)
            for x in range(43):
                for n in range(bound):
                    final_prefix[(x + 1) * bound + n] = (
                        final_prefix[x * bound + n] + contributions[x][n]
                    ) % prime
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxRecDepth 100000")
    lines.append("set_option maxHeartbeats 50000000")
    lines.append("")
    if warning:
        lines.append(warning)
        lines.append("")
    lines.append(f"def {name}Prime : ℕ := {prime}")
    lines.append("")
    lines.append(f"def {name}QE4 : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(qe4))
    lines.append("")
    lines.append(f"def {name}QE2 : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(qe2))
    lines.append("")
    lines.append(f"def {name}QE6 : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(qe6))
    lines.append("")
    lines.append(f"def {name}QE2E4 : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(qe2e4))
    lines.append("")
    lines.append(f"def {name}PE4 : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(pe4))
    lines.append("")
    lines.append(f"def {name}PE2 : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(pe2))
    lines.append("")
    lines.append(f"def {name}PE6 : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(pe6))
    lines.append("")
    lines.append(f"def {name}PE2E4 : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(pe2e4))
    lines.append("")
    if not coeffs_only:
        lines.append(f"def {name}QRows : Array (Array ℤ) :=")
        lines.append("  " + lean_row_table_literal(q_rows).replace("\n", "\n  "))
        lines.append("")
        lines.append(f"def {name}PCompressedRows : Array (Array ℤ) :=")
        lines.append("  " + lean_row_table_literal(p_rows).replace("\n", "\n  "))
        lines.append("")
    if final_coeffs is not None:
        lines.append(f"def {name}QParts : Array (Array ℤ) :=")
        lines.append("  " + lean_row_table_literal(q_parts).replace("\n", "\n  "))
        lines.append("")
        lines.append(f"def {name}Contributions : Array (Array ℤ) :=")
        lines.append("  " + lean_row_table_literal(contributions).replace("\n", "\n  "))
        lines.append("")
        lines.append(f"def {name}Final : Array ℤ :=")
        lines.append("  " + lean_int_array_literal(final_coeffs))
        lines.append("")
    if qpart_prefixes is not None:
        lines.append("set_option maxRecDepth 100000")
        lines.append("set_option maxHeartbeats 1000000")
        lines.append("")
        lines.append(f"def {name}QPartPrefixes : Array (Array ℤ) :=")
        lines.append("  " + lean_row_table_literal(qpart_prefixes).replace("\n", "\n  "))
        lines.append("")
        lines.append(f"def {name}ContributionPrefixes : Array (Array ℤ) :=")
        lines.append("  " + lean_row_table_literal(contribution_prefixes).replace("\n", "\n  "))
        lines.append("")
        lines.append(f"def {name}FinalPrefix : Array ℤ :=")
        lines.append("  " + lean_int_array_literal(final_prefix))
        lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_row_residue_literal_chunk_data(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    side: str = "both",
    row_start: int = 0,
    row_stop: int = 43,
) -> str:
    """Emit modular recurrence rows as row/chunk literals."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    if row_start < 0 or row_stop < row_start or row_stop > 43:
        raise SystemExit("--lean-row-table-proof-row-start/stop must define a subrange of 0..43")
    if side not in {"p", "q", "both"}:
        raise SystemExit("--lean-row-table-recurrence-side must be one of: p, q, both")

    small = (bound + 40) // 41
    specs: list[tuple[str, int, list[list[int]]]] = []
    if side in {"q", "both"}:
        specs.append(("QRows", bound, q_family_coeffs(bound, prime)))
    if side in {"p", "both"}:
        specs.append(("PCompressedRows", small, q_family_coeffs(small, prime)))

    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxRecDepth 100000")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("")
    for label, N, rows in specs:
        num_chunks = ceil_div(N, chunk_size)
        for j in range(row_start, row_stop):
            for c in range(num_chunks):
                start = c * chunk_size
                chunk_values = rows[j][start : min(N, start + chunk_size)]
                lines.append(f"def {name}{label}R_row{j}_chunk{c} : Array ℤ :=")
                lines.append("  " + lean_int_array_literal(chunk_values))
                lines.append("")
        lines.append(f"def {name}{label}RChunk : ℕ → ℕ → Array ℤ")
        for j in range(row_start, row_stop):
            for c in range(num_chunks):
                lines.append(
                    f"  | {j}, {c} => {name}{label}R_row{j}_chunk{c}"
                )
        lines.append("  | _, _ => #[]")
        lines.append("")
        lines.append(f"def {name}{label}R (j n : ℕ) : ℤ :=")
        lines.append(f"  truncCoeffChunkFn {chunk_size} ({name}{label}RChunk j) n")
        lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_intermediate_proofs(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    row_start: int = 0,
    row_stop: int = 43,
    entry_mode: bool = False,
) -> str:
    """Emit Lean proof snippets for row/chunk intermediate residue checks.

    The snippets assume the corresponding `lean_row_table_data(...,
    terms=...)` definitions are already available in the same namespace.
    Proofs use definitional equality only (`rfl`), so they do not rely on
    `native_decide`.
    """
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    if row_start < 0 or row_stop < row_start or row_stop > 43:
        raise SystemExit("--lean-row-table-proof-row-start/stop must define a subrange of 0..43")
    q_num_chunks = ceil_div(bound, chunk_size)
    small = (bound + 40) // 41
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("set_option maxRecDepth 10000")
    lines.append("set_option linter.unnecessarySeqFocus false")
    lines.append("set_option linter.unusedTactic false")
    lines.append("set_option linter.unreachableTactic false")
    lines.append("")
    qpart_names: list[list[str]] = []
    contrib_names: list[list[str]] = []
    for x in range(row_start, row_stop):
        qpart_row: list[str] = []
        contrib_row: list[str] = []
        for c in range(q_num_chunks):
            start = c * chunk_size
            qname = f"{name}QParts_row{x}_chunk{c}"
            cname = f"{name}Contributions_row{x}_chunk{c}"
            qpart_row.append(qname)
            contrib_row.append(cname)
            lines.extend(
                [
                    f"theorem {qname} :",
                    "    phi41QPartTableFromRowsModEqRowChunk",
                    f"      {bound} {prime} {x} {start} {chunk_size}",
                    f"      {name}QRows {name}QParts = true := by",
                ]
            )
            if entry_mode:
                lines.extend(
                    [
                        "  apply phi41QPartTableFromRowsModEqRowChunk_of_entries",
                        "  intro offset hoffset",
                        "  interval_cases offset <;> rfl",
                        "",
                    ]
                )
            else:
                lines.extend(["  rfl", ""])
            lines.extend(
                [
                    f"theorem {cname} :",
                    "    phi41ContributionTableFromQPartsModEqRowChunk",
                    f"      {bound} {small} {prime} {x} {start} {chunk_size}",
                    f"      {name}PCompressedRows {name}QParts {name}Contributions = true := by",
                ]
            )
            if entry_mode:
                lines.extend(
                    [
                        "  apply phi41ContributionTableFromQPartsModEqRowChunk_of_entries",
                        "  intro offset hoffset",
                        "  interval_cases offset <;> rfl",
                        "",
                    ]
                )
            else:
                lines.extend(["  rfl", ""])
        qpart_names.append(qpart_row)
        contrib_names.append(contrib_row)

    final_names: list[str] = []
    zero_names: list[str] = []
    if row_start == 0:
        for c in range(q_num_chunks):
            start = c * chunk_size
            fname = f"{name}Final_chunk{c}"
            zname = f"{name}Zero_chunk{c}"
            final_names.append(fname)
            zero_names.append(zname)
            lines.extend(
                [
                    f"theorem {fname} :",
                    "    phi41FinalFromContributionsModEqChunk",
                    f"      {bound} {prime} {start} {chunk_size}",
                    f"      {name}Contributions {name}Final = true := by",
                ]
            )
            if entry_mode:
                lines.extend(
                    [
                        "  apply phi41FinalFromContributionsModEqChunk_of_entries",
                        "  intro offset hoffset",
                        "  interval_cases offset <;> rfl",
                        "",
                    ]
                )
            else:
                lines.extend(["  rfl", ""])
            lines.extend(
                [
                    f"theorem {zname} :",
                    "    truncCoeffArrayFirstZeroModChunk",
                    f"      {bound} {prime} {start} {chunk_size} {name}Final = true := by",
                ]
            )
            if entry_mode:
                lines.extend(
                    [
                        "  apply truncCoeffArrayFirstZeroModChunk_of_entries",
                        "  intro offset hoffset",
                        "  interval_cases offset <;> rfl",
                        "",
                    ]
                )
            else:
                lines.extend(["  rfl", ""])

    def emit_row_chunk_aggregator(
        theorem_name: str,
        predicate_lines: list[str],
        fact_names: list[list[str]],
    ) -> None:
        lines.append(f"theorem {theorem_name} :")
        lines.append("    ∀ x : ℕ, x ≤ 42 → ∀ c : ℕ, c < " + str(q_num_chunks) + " →")
        lines.extend(predicate_lines)
        lines.append("      = true := by")
        lines.append("  intro x hx c hc")
        lines.append("  interval_cases x")
        for x in range(43):
            lines.append("  · interval_cases c")
            for c in range(q_num_chunks):
                lines.append(f"    · exact {fact_names[x][c]}")
        lines.append("")

    if row_start == 0 and row_stop == 43:
        emit_row_chunk_aggregator(
            f"{name}QParts_chunks",
            [
                "      phi41QPartTableFromRowsModEqRowChunk",
                f"        {bound} {prime} x (c * {chunk_size}) {chunk_size}",
                f"        {name}QRows {name}QParts",
            ],
            qpart_names,
        )
        emit_row_chunk_aggregator(
            f"{name}Contributions_chunks",
            [
                "      phi41ContributionTableFromQPartsModEqRowChunk",
                f"        {bound} {small} {prime} x (c * {chunk_size}) {chunk_size}",
                f"        {name}PCompressedRows {name}QParts {name}Contributions",
            ],
            contrib_names,
        )
    else:
        for idx, x in enumerate(range(row_start, row_stop)):
            lines.append(f"theorem {name}QParts_row{x}_chunks :")
            lines.append("    ∀ c : ℕ, c < " + str(q_num_chunks) + " →")
            lines.append("      phi41QPartTableFromRowsModEqRowChunk")
            lines.append(f"        {bound} {prime} {x} (c * {chunk_size}) {chunk_size}")
            lines.append(f"        {name}QRows {name}QParts = true := by")
            lines.append("  intro c hc")
            lines.append("  interval_cases c")
            for qname in qpart_names[idx]:
                lines.append(f"  · exact {qname}")
            lines.append("")
            lines.append(f"theorem {name}Contributions_row{x}_chunks :")
            lines.append("    ∀ c : ℕ, c < " + str(q_num_chunks) + " →")
            lines.append("      phi41ContributionTableFromQPartsModEqRowChunk")
            lines.append(f"        {bound} {small} {prime} {x} (c * {chunk_size}) {chunk_size}")
            lines.append(f"        {name}PCompressedRows {name}QParts {name}Contributions = true := by")
            lines.append("  intro c hc")
            lines.append("  interval_cases c")
            for cname in contrib_names[idx]:
                lines.append(f"  · exact {cname}")
            lines.append("")

    if row_start == 0:
        lines.append(f"theorem {name}Final_chunks :")
        lines.append("    ∀ c : ℕ, c < " + str(q_num_chunks) + " →")
        lines.append("      phi41FinalFromContributionsModEqChunk")
        lines.append(f"        {bound} {prime} (c * {chunk_size}) {chunk_size}")
        lines.append(f"        {name}Contributions {name}Final = true := by")
        lines.append("  intro c hc")
        lines.append("  interval_cases c")
        for fname in final_names:
            lines.append(f"  · exact {fname}")
        lines.append("")

        lines.append(f"theorem {name}Zero_chunks :")
        lines.append("    ∀ c : ℕ, c < " + str(q_num_chunks) + " →")
        lines.append("      truncCoeffArrayFirstZeroModChunk")
        lines.append(f"        {bound} {prime} (c * {chunk_size}) {chunk_size}")
        lines.append(f"        {name}Final = true := by")
        lines.append("  intro c hc")
        lines.append("  interval_cases c")
        for zname in zero_names:
            lines.append(f"  · exact {zname}")
        lines.append("")

    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_recurrence_proofs(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    row_start: int = 0,
    row_stop: int = 43,
    side: str = "both",
) -> str:
    """Emit Lean proof snippets for P/Q modular recurrence row chunks.

    These snippets assume the corresponding `lean_row_table_data(...)`
    definitions are already available in the same namespace.
    """
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    if row_start < 0 or row_stop < row_start or row_stop > 43:
        raise SystemExit("--lean-row-table-proof-row-start/stop must define a subrange of 0..43")
    if side not in {"p", "q", "both"}:
        raise SystemExit("--lean-row-table-recurrence-side must be one of: p, q, both")

    specs: list[tuple[str, str, int, str, str, str, str]] = []
    small = (bound + 40) // 41
    if side in {"q", "both"}:
        specs.append(("Q", "Q", bound, f"{name}QE4", f"{name}QE6", f"{name}QE2E4", f"{name}QRows"))
    if side in {"p", "both"}:
        specs.append(("P", "P", small, f"{name}PE4", f"{name}PE6", f"{name}PE2E4", f"{name}PCompressedRows"))

    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("set_option maxRecDepth 10000")
    lines.append("")

    for label, theorem_prefix, N, e4_name, e6_name, e2e4_name, rows_name in specs:
        num_chunks = ceil_div(N, chunk_size)
        chunk_names: list[list[str]] = []
        for j in range(row_start, row_stop):
            row_names: list[str] = []
            for c in range(num_chunks):
                start = c * chunk_size
                theorem_name = f"{name}{theorem_prefix}Rec_row{j}_chunk{c}"
                row_names.append(theorem_name)
                lines.extend(
                    [
                        f"theorem {theorem_name} :",
                        "    phi41QRecurrenceRowModCertificateChunk",
                        f"      {N} {prime} {j} {start} {chunk_size}",
                        f"      {e4_name} {e6_name} {e2e4_name}",
                        f"      ({rows_name}.getD {j} (zeroTruncCoeffArray {N})) = true := by",
                        "  rfl",
                        "",
                    ]
                )
            chunk_names.append(row_names)

        for idx, j in enumerate(range(row_start, row_stop)):
            lines.append(f"theorem {name}{theorem_prefix}Rec_row{j}_chunks :")
            lines.append("    ∀ c : ℕ, c < " + str(num_chunks) + " →")
            lines.append("      phi41QRecurrenceRowModCertificateChunk")
            lines.append(f"        {N} {prime} {j} (c * {chunk_size}) {chunk_size}")
            lines.append(f"        {e4_name} {e6_name} {e2e4_name}")
            lines.append(f"        ({rows_name}.getD {j} (zeroTruncCoeffArray {N})) = true := by")
            lines.append("  intro c hc")
            lines.append("  interval_cases c")
            for theorem_name in chunk_names[idx]:
                lines.append(f"  · exact {theorem_name}")
            lines.append("")

        if row_start == 0 and row_stop == 43:
            lines.append(f"theorem {name}{theorem_prefix}RecurrenceCertificate :")
            lines.append("    phi41QRecurrenceRowsModCertificateChunkedWithCoeffArrays")
            lines.append(f"      {N} {prime} {chunk_size} {num_chunks}")
            lines.append(f"      {e4_name} {e6_name} {e2e4_name} {rows_name} = true := by")
            lines.append("  unfold phi41QRecurrenceRowsModCertificateChunkedWithCoeffArrays")
            lines.append("  apply List.all_eq_true.mpr")
            lines.append("  intro j hj")
            lines.append("  have hjlt : j < 43 := List.mem_range.mp hj")
            lines.append("  interval_cases j")
            for j in range(43):
                lines.append("  · apply List.all_eq_true.mpr")
                lines.append("    intro c hc")
                lines.append("    have hclt : c < " + str(num_chunks) + " := List.mem_range.mp hc")
                lines.append("    interval_cases c")
                for theorem_name in chunk_names[j]:
                    lines.append(f"    · exact {theorem_name}")
            lines.append("")

    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_fn_recurrence_proofs(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    row_start: int = 0,
    row_stop: int = 43,
    side: str = "both",
) -> str:
    """Emit function-valued recurrence proofs for row/chunk literals."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    if row_start < 0 or row_stop < row_start or row_stop > 43:
        raise SystemExit("--lean-row-table-proof-row-start/stop must define a subrange of 0..43")
    if side not in {"p", "q", "both"}:
        raise SystemExit("--lean-row-table-recurrence-side must be one of: p, q, both")

    small = (bound + 40) // 41
    specs: list[tuple[str, int, str, str, str, str]] = []
    if side in {"q", "both"}:
        specs.append(("Q", bound, "Q", "QRows", "QE", "q"))
    if side in {"p", "both"}:
        specs.append(("P", small, "P", "PCompressedRows", "PE", "p"))

    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("set_option maxRecDepth 10000")
    lines.append("")

    for theorem_prefix, N, side_label, rows_label, coeff_prefix, _side_key in specs:
        num_chunks = ceil_div(N, chunk_size)
        e4_fn = f"truncCoeffChunkFn {chunk_size} {name}{coeff_prefix}4RChunk"
        e6_fn = f"truncCoeffChunkFn {chunk_size} {name}{coeff_prefix}6RChunk"
        e2e4_fn = f"truncCoeffChunkFn {chunk_size} {name}{coeff_prefix}2E4RChunk"
        rows_fn = f"{name}{rows_label}R"
        chunk_names: list[list[str]] = []
        for j in range(row_start, row_stop):
            row_names: list[str] = []
            for c in range(num_chunks):
                start = c * chunk_size
                theorem_name = f"{name}{theorem_prefix}FnRec_row{j}_chunk{c}"
                row_names.append(theorem_name)
                lines.extend(
                    [
                        f"theorem {theorem_name} :",
                        "    phi41QRecurrenceRowFnModCertificateChunk",
                        f"      {N} {prime} {j} {start} {chunk_size}",
                        f"      ({e4_fn}) ({e6_fn}) ({e2e4_fn})",
                        f"      ({rows_fn} {j}) = true := by",
                        "  rfl",
                        "",
                    ]
                )
            chunk_names.append(row_names)

        for idx, j in enumerate(range(row_start, row_stop)):
            lines.append(f"theorem {name}{theorem_prefix}FnRec_row{j}_chunks :")
            lines.append("    ∀ c : ℕ, c < " + str(num_chunks) + " →")
            lines.append("      phi41QRecurrenceRowFnModCertificateChunk")
            lines.append(f"        {N} {prime} {j} (c * {chunk_size}) {chunk_size}")
            lines.append(f"        ({e4_fn}) ({e6_fn}) ({e2e4_fn})")
            lines.append(f"        ({rows_fn} {j}) = true := by")
            lines.append("  intro c hc")
            lines.append("  interval_cases c")
            for theorem_name in chunk_names[idx]:
                lines.append(f"  · exact {theorem_name}")
            lines.append("")

        if row_start == 0 and row_stop == 43:
            lines.append(f"theorem {name}{theorem_prefix}FnRecurrenceTableCertificate")
            lines.append("    (hE4 : ∀ n : ℕ, n < " + str(N) + " →")
            lines.append(f"      truncCoeffArrayAt (E4TruncCoeffArray {N}) n ≡")
            lines.append(f"        ({e4_fn}) n [ZMOD ({prime} : ℤ)])")
            lines.append("    (hE6 : ∀ n : ℕ, n < " + str(N) + " →")
            lines.append(f"      truncCoeffArrayAt (E6TruncCoeffArray {N}) n ≡")
            lines.append(f"        ({e6_fn}) n [ZMOD ({prime} : ℤ)])")
            lines.append("    (hE2E4 : ∀ n : ℕ, n < " + str(N) + " →")
            lines.append(f"      truncCoeffArrayAt (E2E4TruncCoeffArray {N}) n ≡")
            lines.append(f"        ({e2e4_fn}) n [ZMOD ({prime} : ℤ)])")
            lines.append("    (hderiv : ∀ j : ℕ, j ≤ 42 →")
            lines.append("      E4ZSeries *")
            lines.append("          (PowerSeries.X * PowerSeries.derivative ℤ")
            lines.append("            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) =")
            lines.append("        (PowerSeries.C (42 : ℤ) * (E2ZSeries * E4ZSeries) -")
            lines.append("          PowerSeries.C (j : ℤ) * E6ZSeries) *")
            lines.append("            ((E4ZSeries ^ 3) ^ j * deltaEulerSeriesZ ^ (42 - j))) :")
            lines.append("    TruncCoeffArrayTableModEq")
            lines.append(f"      {N} 42 {prime} (phi41QRecurrenceRowsArray {N})")
            lines.append(f"      (phi41QRecurrenceRowsArrayOfFn {N} {rows_fn}) := by")
            lines.append("  apply TruncCoeffArrayTableModEq.phi41QRecurrenceRows_of_fn_mod_certificate_chunks")
            lines.append(f"    (N := {N}) (p := {prime})")
            lines.append(f"    (chunkSize := {chunk_size}) (numChunks := {num_chunks})")
            lines.append(f"    (E4M := ({e4_fn})) (E6M := ({e6_fn}))")
            lines.append(f"    (E2E4M := ({e2e4_fn})) (rowsM := {rows_fn})")
            lines.append("  · norm_num")
            lines.append("  · norm_num")
            lines.append("  · norm_num")
            lines.append("  · exact hE4")
            lines.append("  · exact hE6")
            lines.append("  · exact hE2E4")
            lines.append("  · intro j hj c hc")
            lines.append("    interval_cases j")
            for row_names in chunk_names:
                lines.append("    · interval_cases c")
                for theorem_name in row_names:
                    lines.append(f"      · exact {theorem_name}")
            lines.append("  · exact hderiv")
            lines.append("")

    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_coeff_proofs(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    side: str = "both",
    labels: Optional[set[str]] = None,
) -> str:
    """Emit Lean proof snippets for generated E4/E6/E2E4 coefficient arrays."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    if side not in {"p", "q", "both"}:
        raise SystemExit("--lean-row-table-coeff-side must be one of: p, q, both")

    small = (bound + 40) // 41
    specs: list[tuple[str, str, int, str, str, str]] = []
    if side in {"q", "both"}:
        specs.extend(
            [
                ("QE2", "modEq", bound, f"E2TruncCoeffArray {bound}", f"{name}QE2", ""),
                ("QE4", "modEq", bound, f"E4TruncCoeffArray {bound}", f"{name}QE4", ""),
                ("QE6", "modEq", bound, f"E6TruncCoeffArray {bound}", f"{name}QE6", ""),
                (
                    "QE2E4DerivRelation",
                    "deriv",
                    bound,
                    f"{name}QE4",
                    f"{name}QE6",
                    f"{name}QE2E4",
                ),
            ]
        )
    if side in {"p", "both"}:
        specs.extend(
            [
                ("PE2", "modEq", small, f"E2TruncCoeffArray {small}", f"{name}PE2", ""),
                ("PE4", "modEq", small, f"E4TruncCoeffArray {small}", f"{name}PE4", ""),
                ("PE6", "modEq", small, f"E6TruncCoeffArray {small}", f"{name}PE6", ""),
                (
                    "PE2E4DerivRelation",
                    "deriv",
                    small,
                    f"{name}PE4",
                    f"{name}PE6",
                    f"{name}PE2E4",
                ),
            ]
        )
    if labels is not None:
        unknown = labels.difference(label for label, _, _, _, _, _ in specs)
        if unknown:
            raise SystemExit(
                "--lean-row-table-coeff-labels contains labels not selected by "
                f"--lean-row-table-coeff-side: {', '.join(sorted(unknown))}"
            )
        specs = [spec for spec in specs if spec[0] in labels]
    else:
        specs = [spec for spec in specs if spec[0] not in {"QE2", "PE2"}]

    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("set_option maxRecDepth 10000")
    lines.append("set_option linter.unnecessarySeqFocus false")
    lines.append("set_option linter.unusedTactic false")
    lines.append("set_option linter.unreachableTactic false")
    lines.append("")

    for label, mode, N, arg1, arg2, arg3 in specs:
        num_chunks = ceil_div(N, chunk_size)
        chunk_names: list[str] = []
        for c in range(num_chunks):
            start = c * chunk_size
            theorem_name = f"{name}{label}Coeff_chunk{c}"
            chunk_names.append(theorem_name)
            if mode == "modEq":
                true_array = arg1
                literal_array = arg2
                lines.extend(
                    [
                        f"theorem {theorem_name} :",
                        "    truncCoeffArrayModEqFirstChunk",
                        f"      {N} {prime} {start} {chunk_size}",
                        f"      ({true_array}) {literal_array} = true := by",
                        "  apply truncCoeffArrayModEqFirstChunk_of_entries",
                        "  intro offset hoffset",
                        "  interval_cases offset <;>",
                        "    (norm_num [intCoeffModEq, intCoeffZeroMod,",
                        "      E2E4TruncCoeffArray, E2TruncCoeffArray, E4TruncCoeffArray, E6TruncCoeffArray,",
                        "      E2CoeffZ, E4CoeffZ, E6CoeffZ, mulTruncCoeffArray,",
                        "      truncCoeffArrayAt, truncCoeffArrayOfFn, truncCoeffList, sumRangeFromZ,",
                        "      ArithmeticFunction.sigma, Nat.divisors,",
                        f"      {name}QE2, {name}QE4, {name}QE6, {name}QE2E4,",
                        f"      {name}PE2, {name}PE4, {name}PE6, {name}PE2E4] <;> decide)",
                        "",
                    ]
                )
            else:
                e4_array = arg1
                e6_array = arg2
                e2e4_array = arg3
                lines.extend(
                    [
                        f"theorem {theorem_name} :",
                        "    truncCoeffArrayE2E4DerivRelationChunk",
                        f"      {N} {prime} {start} {chunk_size}",
                        f"      {e4_array} {e6_array} {e2e4_array} = true := by",
                        "  apply truncCoeffArrayE2E4DerivRelationChunk_of_entries",
                        "  intro offset hoffset",
                        "  interval_cases offset <;>",
                        "    norm_num [intCoeffModEq, intCoeffZeroMod,",
                        "      truncCoeffArrayAt,",
                        f"      {name}QE4, {name}QE6, {name}QE2E4,",
                        f"      {name}PE4, {name}PE6, {name}PE2E4]",
                        "",
                    ]
                )

        lines.append(f"theorem {name}{label}CoeffCertificate :")
        if mode == "modEq":
            lines.append("    truncCoeffArrayModEqFirstChunked")
            lines.append(f"      {N} {prime} {chunk_size} {num_chunks}")
            lines.append(f"      ({arg1}) {arg2} = true := by")
            lines.append("  unfold truncCoeffArrayModEqFirstChunked")
        else:
            lines.append("    truncCoeffArrayE2E4DerivRelationChunked")
            lines.append(f"      {N} {prime} {chunk_size} {num_chunks}")
            lines.append(f"      {arg1} {arg2} {arg3} = true := by")
            lines.append("  unfold truncCoeffArrayE2E4DerivRelationChunked")
        lines.append("  apply List.all_eq_true.mpr")
        lines.append("  intro c hc")
        lines.append("  have hclt : c < " + str(num_chunks) + " := List.mem_range.mp hc")
        lines.append("  interval_cases c")
        for theorem_name in chunk_names:
            lines.append(f"  · exact {theorem_name}")
        lines.append("")

    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_exact_coeff_data(bound: int, name: str) -> str:
    """Emit exact integer E4/E6 coefficient arrays for Q/P precisions."""
    small = (bound + 40) // 41
    _qe2, qe4, qe6, _qe2e4 = modular_series_data(bound, None)
    _pe2, pe4, pe6, _pe2e4 = modular_series_data(small, None)
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxRecDepth 100000")
    lines.append("set_option maxHeartbeats 50000000")
    lines.append("")
    lines.append(f"def {name}QE4Z : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(qe4))
    lines.append("")
    lines.append(f"def {name}QE6Z : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(qe6))
    lines.append("")
    lines.append(f"def {name}PE4Z : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(pe4))
    lines.append("")
    lines.append(f"def {name}PE6Z : Array ℤ :=")
    lines.append("  " + lean_int_array_literal(pe6))
    lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_exact_coeff_proofs(
    bound: int,
    name: str,
    chunk_size: int,
    side: str = "both",
    labels: Optional[set[str]] = None,
) -> str:
    """Emit exact equality proofs for generated integer E4/E6 arrays."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    if side not in {"p", "q", "both"}:
        raise SystemExit("--lean-row-table-coeff-side must be one of: p, q, both")
    small = (bound + 40) // 41
    specs: list[tuple[str, int, str, str]] = []
    if side in {"q", "both"}:
        specs.extend(
            [
                ("QE4Exact", bound, f"E4TruncCoeffArray {bound}", f"{name}QE4Z"),
                ("QE6Exact", bound, f"E6TruncCoeffArray {bound}", f"{name}QE6Z"),
            ]
        )
    if side in {"p", "both"}:
        specs.extend(
            [
                ("PE4Exact", small, f"E4TruncCoeffArray {small}", f"{name}PE4Z"),
                ("PE6Exact", small, f"E6TruncCoeffArray {small}", f"{name}PE6Z"),
            ]
        )
    if labels is not None:
        unknown = labels.difference(label for label, _, _, _ in specs)
        if unknown:
            raise SystemExit(
                "--lean-row-table-coeff-labels contains labels not selected by "
                f"--lean-row-table-coeff-side: {', '.join(sorted(unknown))}"
            )
        specs = [spec for spec in specs if spec[0] in labels]

    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("set_option maxRecDepth 10000")
    lines.append("set_option linter.unnecessarySeqFocus false")
    lines.append("set_option linter.unusedTactic false")
    lines.append("set_option linter.unreachableTactic false")
    lines.append("")
    for label, N, true_array, literal_array in specs:
        num_chunks = ceil_div(N, chunk_size)
        chunk_names: list[str] = []
        for c in range(num_chunks):
            start = c * chunk_size
            theorem_name = f"{name}{label}_chunk{c}"
            chunk_names.append(theorem_name)
            lines.extend(
                [
                    f"theorem {theorem_name} :",
                    "    truncCoeffArrayEqFirstChunk",
                    f"      {N} {start} {chunk_size}",
                    f"      ({true_array}) {literal_array} = true := by",
                    "  apply truncCoeffArrayEqFirstChunk_of_entries",
                    "  intro offset hoffset",
                    "  interval_cases offset <;>",
                    "    (norm_num [",
                    "      E4TruncCoeffArray, E6TruncCoeffArray, E4CoeffZ, E6CoeffZ,",
                    "      truncCoeffArrayAt, truncCoeffArrayOfFn,",
                    "      ArithmeticFunction.sigma, Nat.divisors,",
                    f"      {name}QE4Z, {name}QE6Z, {name}PE4Z, {name}PE6Z] <;> decide)",
                    "",
                ]
            )
        lines.append(f"theorem {name}{label}Certificate :")
        lines.append("    truncCoeffArrayEqFirstChunked")
        lines.append(f"      {N} {chunk_size} {num_chunks}")
        lines.append(f"      ({true_array}) {literal_array} = true := by")
        lines.append("  unfold truncCoeffArrayEqFirstChunked")
        lines.append("  apply List.all_eq_true.mpr")
        lines.append("  intro c hc")
        lines.append("  have hclt : c < " + str(num_chunks) + " := List.mem_range.mp hc")
        lines.append("  interval_cases c")
        for theorem_name in chunk_names:
            lines.append(f"  · exact {theorem_name}")
        lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_exact_mod_proofs(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    side: str = "both",
    labels: Optional[set[str]] = None,
) -> str:
    """Emit modular congruence proofs from exact E4/E6 arrays to residue arrays."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    if side not in {"p", "q", "both"}:
        raise SystemExit("--lean-row-table-coeff-side must be one of: p, q, both")
    small = (bound + 40) // 41
    specs: list[tuple[str, int, str, str]] = []
    if side in {"q", "both"}:
        specs.extend(
            [
                ("QE4Mod", bound, f"{name}QE4Z", f"{name}QE4"),
                ("QE6Mod", bound, f"{name}QE6Z", f"{name}QE6"),
            ]
        )
    if side in {"p", "both"}:
        specs.extend(
            [
                ("PE4Mod", small, f"{name}PE4Z", f"{name}PE4"),
                ("PE6Mod", small, f"{name}PE6Z", f"{name}PE6"),
            ]
        )
    if labels is not None:
        unknown = labels.difference(label for label, _, _, _ in specs)
        if unknown:
            raise SystemExit(
                "--lean-row-table-coeff-labels contains labels not selected by "
                f"--lean-row-table-coeff-side: {', '.join(sorted(unknown))}"
            )
        specs = [spec for spec in specs if spec[0] in labels]

    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("set_option maxRecDepth 10000")
    lines.append("")
    for label, N, exact_array, residue_array in specs:
        num_chunks = ceil_div(N, chunk_size)
        chunk_names: list[str] = []
        for c in range(num_chunks):
            start = c * chunk_size
            theorem_name = f"{name}{label}_chunk{c}"
            chunk_names.append(theorem_name)
            lines.extend(
                [
                    f"theorem {theorem_name} :",
                    "    truncCoeffArrayModEqFirstChunk",
                    f"      {N} {prime} {start} {chunk_size}",
                    f"      {exact_array} {residue_array} = true := by",
                    "  apply truncCoeffArrayModEqFirstChunk_of_entries",
                    "  intro offset hoffset",
                    "  interval_cases offset <;>",
                    "    norm_num [intCoeffModEq, intCoeffZeroMod,",
                    "      truncCoeffArrayAt,",
                    f"      {name}QE4Z, {name}QE6Z, {name}PE4Z, {name}PE6Z,",
                    f"      {name}QE4, {name}QE6, {name}PE4, {name}PE6]",
                    "",
                ]
            )
        lines.append(f"theorem {name}{label}Certificate :")
        lines.append("    truncCoeffArrayModEqFirstChunked")
        lines.append(f"      {N} {prime} {chunk_size} {num_chunks}")
        lines.append(f"      {exact_array} {residue_array} = true := by")
        lines.append("  unfold truncCoeffArrayModEqFirstChunked")
        lines.append("  apply List.all_eq_true.mpr")
        lines.append("  intro c hc")
        lines.append("  have hclt : c < " + str(num_chunks) + " := List.mem_range.mp hc")
        lines.append("  interval_cases c")
        for theorem_name in chunk_names:
            lines.append(f"  · exact {theorem_name}")
        lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def exact_coeff_literal_specs(bound: int, side: str) -> list[tuple[str, int, str, list[int], str]]:
    if side not in {"p", "q", "both"}:
        raise SystemExit("--lean-row-table-coeff-side must be one of: p, q, both")
    small = (bound + 40) // 41
    _qe2, qe4, qe6, _qe2e4 = modular_series_data(bound, None)
    _pe2, pe4, pe6, _pe2e4 = modular_series_data(small, None)
    specs: list[tuple[str, int, str, list[int], str]] = []
    if side in {"q", "both"}:
        specs.extend(
            [
                ("QE4", bound, f"E4TruncCoeffArray {bound}", qe4, "E4"),
                ("QE6", bound, f"E6TruncCoeffArray {bound}", qe6, "E6"),
            ]
        )
    if side in {"p", "both"}:
        specs.extend(
            [
                ("PE4", small, f"E4TruncCoeffArray {small}", pe4, "E4"),
                ("PE6", small, f"E6TruncCoeffArray {small}", pe6, "E6"),
            ]
        )
    return specs


def filter_literal_specs(
    specs: list[tuple[str, int, str, list[int], str]],
    labels: Optional[set[str]],
) -> list[tuple[str, int, str, list[int], str]]:
    if labels is None:
        return specs
    allowed = {f"{label}Literal" for label, _, _, _, _ in specs}
    allowed.update(label for label, _, _, _, _ in specs)
    unknown = labels.difference(allowed)
    if unknown:
        raise SystemExit(
            "--lean-row-table-coeff-labels contains labels not selected by "
            f"--lean-row-table-coeff-side: {', '.join(sorted(unknown))}"
        )
    return [
        spec for spec in specs
        if spec[0] in labels or f"{spec[0]}Literal" in labels
    ]


def lean_row_table_exact_literal_chunk_data(
    bound: int,
    name: str,
    chunk_size: int,
    side: str = "both",
    labels: Optional[set[str]] = None,
) -> str:
    """Emit exact E4/E6 coefficients as many small chunk literals."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    specs = filter_literal_specs(exact_coeff_literal_specs(bound, side), labels)
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxRecDepth 100000")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("")
    for label, N, _true_array, values, _kind in specs:
        num_chunks = ceil_div(N, chunk_size)
        for c in range(num_chunks):
            start = c * chunk_size
            chunk_values = values[start : min(N, start + chunk_size)]
            lines.append(f"def {name}{label}Z_chunk{c} : Array ℤ :=")
            lines.append("  " + lean_int_array_literal(chunk_values))
            lines.append("")
        lines.append(f"def {name}{label}ZChunk : ℕ → Array ℤ")
        for c in range(num_chunks):
            lines.append(f"  | {c} => {name}{label}Z_chunk{c}")
        lines.append("  | _ => #[]")
        lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_exact_literal_mod_proofs(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    side: str = "both",
    labels: Optional[set[str]] = None,
) -> str:
    """Prove true E4/E6 arrays congruent to residue arrays via exact chunks."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    specs = filter_literal_specs(exact_coeff_literal_specs(bound, side), labels)
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("set_option maxRecDepth 10000")
    lines.append("set_option linter.unnecessarySeqFocus false")
    lines.append("set_option linter.unusedTactic false")
    lines.append("set_option linter.unreachableTactic false")
    lines.append("")
    for label, N, true_array, _values, kind in specs:
        num_chunks = ceil_div(N, chunk_size)
        exact_names: list[str] = []
        mod_names: list[str] = []
        residue_array = f"{name}{label}"
        for c in range(num_chunks):
            start = c * chunk_size
            exact_name = f"{name}{label}LiteralExact_chunk{c}"
            mod_name = f"{name}{label}LiteralMod_chunk{c}"
            exact_names.append(exact_name)
            mod_names.append(mod_name)
            coeff_def = "E4CoeffZ" if kind == "E4" else "E6CoeffZ"
            trunc_def = "E4TruncCoeffArray" if kind == "E4" else "E6TruncCoeffArray"
            lines.extend(
                [
                    f"theorem {exact_name} :",
                    "    truncCoeffFnEqLiteralChunk",
                    f"      {N} {start} {chunk_size}",
                    f"      {coeff_def} {name}{label}Z_chunk{c} = true := by",
                    "  apply truncCoeffFnEqLiteralChunk_of_entries",
                    "  intro offset hoffset",
                    "  interval_cases offset <;>",
                    "    (norm_num [",
                    f"      {coeff_def},",
                    "      truncCoeffArrayAt,",
                    "      ArithmeticFunction.sigma, Nat.divisors,",
                    f"      {name}{label}Z_chunk{c}] <;> decide)",
                    "",
                    f"theorem {mod_name} :",
                    "    truncCoeffArrayModEqLiteralChunk",
                    f"      {N} {prime} {start} {chunk_size}",
                    f"      {name}{label}Z_chunk{c} {residue_array} = true := by",
                    "  apply truncCoeffArrayModEqLiteralChunk_of_entries",
                    "  intro offset hoffset",
                    "  interval_cases offset <;>",
                    "    norm_num [intCoeffModEq, intCoeffZeroMod,",
                    "      truncCoeffArrayAt,",
                    f"      {name}{label}Z_chunk{c}, {residue_array}]",
                    "",
                ]
            )
        lines.append(f"theorem {name}{label}LiteralModEq :")
        lines.append(f"    TruncCoeffArrayModEq {N} {prime} ({true_array}) {residue_array} := by")
        lines.append(f"  change TruncCoeffArrayModEq {N} {prime}")
        lines.append(f"    (truncCoeffArrayOfFn {N} {coeff_def}) {residue_array}")
        lines.append("  refine TruncCoeffArrayModEq.of_fn_literal_chunks")
        lines.append(f"    (K := {N}) (p := {prime})")
        lines.append(f"    (chunkSize := {chunk_size}) (numChunks := {num_chunks})")
        lines.append(f"    (f := {coeff_def})")
        lines.append(f"    (hcover := by norm_num) (chunk := {name}{label}ZChunk) ?_ ?_")
        lines.append("  · intro c hc")
        lines.append("    interval_cases c")
        for theorem_name in exact_names:
            lines.append(f"    · simpa [{name}{label}ZChunk] using {theorem_name}")
        lines.append("  · intro c hc")
        lines.append("    interval_cases c")
        for theorem_name in mod_names:
            lines.append(f"    · simpa [{name}{label}ZChunk] using {theorem_name}")
        lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def residue_coeff_literal_specs(
    bound: int,
    prime: int,
    side: str,
) -> list[tuple[str, int, list[int]]]:
    if side not in {"p", "q", "both"}:
        raise SystemExit("--lean-row-table-coeff-side must be one of: p, q, both")
    small = (bound + 40) // 41
    _qe2, qe4, qe6, _qe2e4 = modular_series_data(bound, prime)
    _pe2, pe4, pe6, _pe2e4 = modular_series_data(small, prime)
    specs: list[tuple[str, int, list[int]]] = []
    if side in {"q", "both"}:
        specs.extend([("QE4", bound, qe4), ("QE6", bound, qe6)])
    if side in {"p", "both"}:
        specs.extend([("PE4", small, pe4), ("PE6", small, pe6)])
    return specs


def e2e4_residue_literal_specs(
    bound: int,
    prime: int,
    side: str,
) -> list[tuple[str, int, list[int]]]:
    if side not in {"p", "q", "both"}:
        raise SystemExit("--lean-row-table-coeff-side must be one of: p, q, both")
    small = (bound + 40) // 41
    _qe2, _qe4, _qe6, qe2e4 = modular_series_data(bound, prime)
    _pe2, _pe4, _pe6, pe2e4 = modular_series_data(small, prime)
    specs: list[tuple[str, int, list[int]]] = []
    if side in {"q", "both"}:
        specs.append(("QE2E4", bound, qe2e4))
    if side in {"p", "both"}:
        specs.append(("PE2E4", small, pe2e4))
    return specs


def filter_e2e4_specs(
    specs: list[tuple[str, int, list[int]]],
    labels: Optional[set[str]],
) -> list[tuple[str, int, list[int]]]:
    if labels is None:
        return specs
    allowed = {f"{label}Residue" for label, _, _ in specs}
    allowed.update(label for label, _, _ in specs)
    allowed.update({
        "QE2E4DerivRelation",
        "PE2E4DerivRelation",
    })
    unknown = labels.difference(allowed)
    if unknown:
        raise SystemExit(
            "--lean-row-table-coeff-labels contains labels not selected by "
            f"--lean-row-table-coeff-side: {', '.join(sorted(unknown))}"
        )
    selected: list[tuple[str, int, list[int]]] = []
    for spec in specs:
        label = spec[0]
        if (
            label in labels
            or f"{label}Residue" in labels
            or f"{label}DerivRelation" in labels
        ):
            selected.append(spec)
    return selected


def filter_residue_specs(
    specs: list[tuple[str, int, list[int]]],
    labels: Optional[set[str]],
) -> list[tuple[str, int, list[int]]]:
    if labels is None:
        return specs
    allowed = {f"{label}Residue" for label, _, _ in specs}
    allowed.update(label for label, _, _ in specs)
    unknown = labels.difference(allowed)
    if unknown:
        raise SystemExit(
            "--lean-row-table-coeff-labels contains labels not selected by "
            f"--lean-row-table-coeff-side: {', '.join(sorted(unknown))}"
        )
    return [
        spec for spec in specs
        if spec[0] in labels or f"{spec[0]}Residue" in labels
    ]


def lean_row_table_residue_literal_chunk_data(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    side: str = "both",
    labels: Optional[set[str]] = None,
) -> str:
    """Emit modular E4/E6 residues as many small chunk literals."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    specs = filter_residue_specs(
        residue_coeff_literal_specs(bound, prime, side), labels
    )
    specs_e2e4 = filter_e2e4_specs(
        e2e4_residue_literal_specs(bound, prime, side), labels
    )
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxRecDepth 100000")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("")
    for label, N, values in specs:
        num_chunks = ceil_div(N, chunk_size)
        for c in range(num_chunks):
            start = c * chunk_size
            chunk_values = values[start : min(N, start + chunk_size)]
            lines.append(f"def {name}{label}R_chunk{c} : Array ℤ :=")
            lines.append("  " + lean_int_array_literal(chunk_values))
            lines.append("")
        lines.append(f"def {name}{label}RChunk : ℕ → Array ℤ")
        for c in range(num_chunks):
            lines.append(f"  | {c} => {name}{label}R_chunk{c}")
        lines.append("  | _ => #[]")
        lines.append("")
    for label, N, values in specs_e2e4:
        num_chunks = ceil_div(N, chunk_size)
        for c in range(num_chunks):
            start = c * chunk_size
            chunk_values = values[start : min(N, start + chunk_size)]
            lines.append(f"def {name}{label}R_chunk{c} : Array ℤ :=")
            lines.append("  " + lean_int_array_literal(chunk_values))
            lines.append("")
        lines.append(f"def {name}{label}RChunk : ℕ → Array ℤ")
        for c in range(num_chunks):
            lines.append(f"  | {c} => {name}{label}R_chunk{c}")
        lines.append("  | _ => #[]")
        lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_exact_to_residue_fn_proofs(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    side: str = "both",
    labels: Optional[set[str]] = None,
) -> str:
    """Prove true E4/E6 arrays congruent to residue chunk functions."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    specs = filter_literal_specs(exact_coeff_literal_specs(bound, side), labels)
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("set_option maxRecDepth 10000")
    lines.append("set_option linter.unnecessarySeqFocus false")
    lines.append("set_option linter.unusedTactic false")
    lines.append("set_option linter.unreachableTactic false")
    lines.append("")
    for label, N, true_array, _values, kind in specs:
        num_chunks = ceil_div(N, chunk_size)
        exact_names: list[str] = []
        mod_names: list[str] = []
        coeff_def = "E4CoeffZ" if kind == "E4" else "E6CoeffZ"
        trunc_def = "E4TruncCoeffArray" if kind == "E4" else "E6TruncCoeffArray"
        for c in range(num_chunks):
            start = c * chunk_size
            exact_name = f"{name}{label}FnExact_chunk{c}"
            mod_name = f"{name}{label}FnResidue_chunk{c}"
            exact_names.append(exact_name)
            mod_names.append(mod_name)
            lines.extend(
                [
                    f"theorem {exact_name} :",
                    "    truncCoeffFnEqLiteralChunk",
                    f"      {N} {start} {chunk_size}",
                    f"      {coeff_def} {name}{label}Z_chunk{c} = true := by",
                    "  apply truncCoeffFnEqLiteralChunk_of_entries",
                    "  intro offset hoffset",
                    "  interval_cases offset <;>",
                    "    (norm_num [",
                    f"      {coeff_def},",
                    "      truncCoeffArrayAt,",
                    "      ArithmeticFunction.sigma, Nat.divisors,",
                    f"      {name}{label}Z_chunk{c}] <;> decide)",
                    "",
                    f"theorem {mod_name} :",
                    "    truncCoeffLiteralChunksModEqChunk",
                    f"      {N} {prime} {start} {chunk_size}",
                    f"      {name}{label}Z_chunk{c} {name}{label}R_chunk{c} = true := by",
                    "  apply truncCoeffLiteralChunksModEqChunk_of_entries",
                    "  intro offset hoffset",
                    "  interval_cases offset <;>",
                    "    norm_num [intCoeffModEq, intCoeffZeroMod,",
                    "      truncCoeffArrayAt,",
                    f"      {name}{label}Z_chunk{c}, {name}{label}R_chunk{c}]",
                    "",
                ]
            )
        lines.append(f"theorem {name}{label}FnResidueModEq :")
        lines.append(f"    TruncCoeffArrayModEq {N} {prime} ({true_array})")
        lines.append(f"      (truncCoeffArrayOfFn {N} (truncCoeffChunkFn {chunk_size} {name}{label}RChunk)) := by")
        lines.append(f"  change TruncCoeffArrayModEq {N} {prime}")
        lines.append(f"    (truncCoeffArrayOfFn {N} {coeff_def})")
        lines.append(f"    (truncCoeffArrayOfFn {N} (truncCoeffChunkFn {chunk_size} {name}{label}RChunk))")
        lines.append("  refine TruncCoeffArrayModEq.of_fn_literal_chunk_functions")
        lines.append(f"    (K := {N}) (p := {prime})")
        lines.append(f"    (chunkSize := {chunk_size}) (numChunks := {num_chunks})")
        lines.append(f"    (f := {coeff_def})")
        lines.append(f"    (hcover := by norm_num)")
        lines.append(f"    (exactChunk := {name}{label}ZChunk)")
        lines.append(f"    (residueChunk := {name}{label}RChunk) ?_ ?_")
        lines.append("  · intro c hc")
        lines.append("    interval_cases c")
        for theorem_name in exact_names:
            lines.append(f"    · simpa [{name}{label}ZChunk] using {theorem_name}")
        lines.append("  · intro c hc")
        lines.append("    interval_cases c")
        for theorem_name in mod_names:
            lines.append(f"    · simpa [{name}{label}ZChunk, {name}{label}RChunk] using {theorem_name}")
        lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_row_table_e2e4_residue_fn_proofs(
    bound: int,
    prime: int,
    name: str,
    chunk_size: int,
    side: str = "both",
    labels: Optional[set[str]] = None,
) -> str:
    """Emit E2E4 derivative-relation proofs for residue chunk functions."""
    if chunk_size <= 0:
        raise SystemExit("--lean-row-table-proof-chunk-size must be positive")
    specs = filter_e2e4_specs(e2e4_residue_literal_specs(bound, prime, side), labels)
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    lines.append("set_option maxHeartbeats 1000000")
    lines.append("set_option maxRecDepth 10000")
    lines.append("set_option linter.unnecessarySeqFocus false")
    lines.append("set_option linter.unusedTactic false")
    lines.append("set_option linter.unreachableTactic false")
    lines.append("")
    for label, N, _values in specs:
        prefix = label.removesuffix("E2E4")
        e4_fn = f"truncCoeffChunkFn {chunk_size} {name}{prefix}E4RChunk"
        e6_fn = f"truncCoeffChunkFn {chunk_size} {name}{prefix}E6RChunk"
        e2e4_fn = f"truncCoeffChunkFn {chunk_size} {name}{label}RChunk"
        num_chunks = ceil_div(N, chunk_size)
        chunk_names: list[str] = []
        for c in range(num_chunks):
            start = c * chunk_size
            theorem_name = f"{name}{label}FnDeriv_chunk{c}"
            chunk_names.append(theorem_name)
            lines.extend(
                [
                    f"theorem {theorem_name} :",
                    "    truncCoeffE2E4DerivRelationLiteralChunk",
                    f"      {N} {prime} {start} {chunk_size}",
                    f"      {name}{prefix}E4R_chunk{c}",
                    f"      {name}{prefix}E6R_chunk{c}",
                    f"      {name}{label}R_chunk{c} = true := by",
                    "  apply truncCoeffE2E4DerivRelationLiteralChunk_of_entries",
                    "  intro offset hoffset",
                    "  interval_cases offset <;>",
                    "    norm_num [intCoeffModEq, intCoeffZeroMod,",
                    "      truncCoeffArrayAt,",
                    f"      {name}{prefix}E4R_chunk{c}, {name}{prefix}E6R_chunk{c},",
                    f"      {name}{label}R_chunk{c}]",
                    "",
                ]
            )
        lines.append(f"theorem {name}{label}FnDerivCertificate :")
        lines.append(f"    ∀ n : ℕ, n < {N} →")
        lines.append(f"      ({e2e4_fn}) n ≡")
        lines.append(f"        ({e6_fn}) n + (3 : ℤ) * (n : ℤ) * ({e4_fn}) n")
        lines.append(f"        [ZMOD ({prime} : ℤ)] := by")
        lines.append("  exact")
        lines.append("    truncCoeffE2E4DerivRelationFn_of_literal_chunks")
        lines.append(f"      (K := {N}) (p := {prime})")
        lines.append(f"      (chunkSize := {chunk_size}) (numChunks := {num_chunks})")
        lines.append("      (by norm_num)")
        lines.append(f"      {name}{prefix}E4RChunk {name}{prefix}E6RChunk {name}{label}RChunk")
        lines.append("      (by")
        lines.append("        intro c hc")
        lines.append("        interval_cases c")
        for theorem_name in chunk_names:
            lines.append(f"        · exact {theorem_name}")
        lines.append("      )")
        lines.append("")
    lines.append("end Modular")
    lines.append("end Number")
    lines.append("end Ripple")
    lines.append("")
    return "\n".join(lines)


def lean_crt_skeleton(manifest: dict, theorem_name: str, primes_name: str) -> str:
    bound = int(manifest["bound"])
    if bound != 3528:
        warning = (
            f"/- WARNING: manifest bound is {bound}, not the project Sturm bound 3528. "
            "This skeleton targets the project theorem shape and is for interface testing. -/"
        )
    else:
        warning = ""
    primes = [int(row["prime"]) for row in manifest["prime_results"]]
    if "exact_bound" in manifest:
        bound_literal = manifest["exact_bound"]["max_bound"]
        product_gt_bound = bool(manifest["exact_bound"]["product_gt_max_bound"])
    else:
        bound_literal = "0"
        product_gt_bound = False
    product_literal = manifest.get("prime_product", str(math.prod(primes)))
    lines = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    if warning:
        lines.append(warning)
        lines.append("")
    lines.append(lean_prime_list_snippet(primes, primes_name).rstrip())
    lines.extend(
        [
            "",
            f"def {theorem_name}Bound : ℕ := {bound_literal}",
            "",
            f"def {theorem_name}PrimeProduct : ℕ := {product_literal}",
            "",
            f"theorem {primes_name}_prod_eq :",
            f"    {primes_name}.prod = {theorem_name}PrimeProduct := by",
            f"  norm_num [{primes_name}, {theorem_name}PrimeProduct]",
            "",
        ]
    )
    if product_gt_bound:
        lines.extend(
            [
                f"theorem {theorem_name}Bound_lt_primeProduct :",
                f"    ({theorem_name}Bound : ℤ) < ({primes_name}.prod : ℤ) := by",
                f"  rw [{primes_name}_prod_eq]",
                f"  norm_num [{theorem_name}Bound, {theorem_name}PrimeProduct]",
                "",
            ]
        )
    lines.extend(
        [
            f"theorem {theorem_name}",
            "    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →",
            "      |truncCoeffArrayAt",
            "        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤",
            f"          ({theorem_name}Bound : ℤ))",
        ]
    )
    if not product_gt_bound:
        lines.append(
            f"    (hB : ({theorem_name}Bound : ℤ) < ({primes_name}.prod : ℤ))"
        )
    lines.extend(
        [
            f"    (hmods : ∀ p ∈ {primes_name},",
            "      truncCoeffArrayFirstZeroMod phi41Level41SturmBound p",
            "        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) = true) :",
            "    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by",
            "  exact phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_mod_certificate",
        ]
    )
    if product_gt_bound:
        lines.append(
            f"    {primes_name}_nodup {primes_name}_prime hbound "
            f"{theorem_name}Bound_lt_primeProduct hmods"
        )
    else:
        lines.append(f"    {primes_name}_nodup {primes_name}_prime hbound hB hmods")
    lines.extend(
        [
            "",
            "end Modular",
            "end Number",
            "end Ripple",
            "",
        ]
    )
    return "\n".join(lines)


def lean_function_crt_skeleton(manifest: dict, theorem_name: str, primes_name: str) -> str:
    """Emit a Lean scaffold for the function-valued CRT certificate exit."""
    bound = int(manifest["bound"])
    if bound != 3528:
        warning = (
            f"/- WARNING: manifest bound is {bound}, not the project Sturm bound 3528. "
            "This skeleton targets the project theorem shape and is for interface testing. -/"
        )
    else:
        warning = ""
    primes = [int(row["prime"]) for row in manifest["prime_results"]]
    if "exact_bound" in manifest:
        bound_literal = manifest["exact_bound"]["max_bound"]
        product_gt_bound = bool(manifest["exact_bound"]["product_gt_max_bound"])
    else:
        bound_literal = "0"
        product_gt_bound = False
    product_literal = manifest.get("prime_product", str(math.prod(primes)))
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    if warning:
        lines.append(warning)
        lines.append("")
    lines.append(lean_prime_list_snippet(primes, primes_name).rstrip())
    lines.extend(
        [
            "",
            f"def {theorem_name}Bound : ℕ := {bound_literal}",
            "",
            f"def {theorem_name}PrimeProduct : ℕ := {product_literal}",
            "",
            f"theorem {primes_name}_prod_eq :",
            f"    {primes_name}.prod = {theorem_name}PrimeProduct := by",
            f"  norm_num [{primes_name}, {theorem_name}PrimeProduct]",
            "",
        ]
    )
    if product_gt_bound:
        lines.extend(
            [
                f"theorem {theorem_name}Bound_lt_primeProduct :",
                f"    ({theorem_name}Bound : ℤ) < ({primes_name}.prod : ℤ) := by",
                f"  rw [{primes_name}_prod_eq]",
                f"  norm_num [{theorem_name}Bound, {theorem_name}PrimeProduct]",
                "",
            ]
        )
    lines.extend(
        [
            f"theorem {theorem_name}",
            "    (ys : ℕ → ℕ → ℤ)",
            "    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →",
            "      |truncCoeffArrayAt",
            "        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤",
            f"          ({theorem_name}Bound : ℤ))",
        ]
    )
    if not product_gt_bound:
        lines.append(
            f"    (hB : ({theorem_name}Bound : ℤ) < ({primes_name}.prod : ℤ))"
        )
    lines.extend(
        [
            f"    (hrel : ∀ p ∈ {primes_name}, ∀ n : ℕ, n < phi41Level41SturmBound →",
            "      truncCoeffArrayAt",
            "          (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n ≡",
            "        ys p n [ZMOD (p : ℤ)])",
            f"    (hzero : ∀ p ∈ {primes_name}, ∀ n : ℕ, n < phi41Level41SturmBound →",
            "      ys p n ≡ 0 [ZMOD (p : ℤ)]) :",
            "    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by",
            "  exact",
            "    phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_function_certificate",
        ]
    )
    if product_gt_bound:
        lines.append(
            f"      {primes_name}_nodup {primes_name}_prime hbound "
            f"{theorem_name}Bound_lt_primeProduct ys hrel hzero"
        )
    else:
        lines.append(
            f"      {primes_name}_nodup {primes_name}_prime hbound hB ys hrel hzero"
        )
    lines.extend(
        [
            "",
            "end Modular",
            "end Number",
            "end Ripple",
            "",
        ]
    )
    return "\n".join(lines)


def lean_row_table_crt_skeleton(manifest: dict, theorem_name: str, primes_name: str) -> str:
    """Emit a Lean scaffold for the chunked Bool row-table CRT interface."""
    bound = int(manifest["bound"])
    if bound != 3528:
        warning = (
            f"/- WARNING: manifest bound is {bound}, not the project Sturm bound 3528. "
            "This scaffold targets the project theorem shape and is for interface testing. -/"
        )
    else:
        warning = ""
    primes = [int(row["prime"]) for row in manifest["prime_results"]]
    lines: list[str] = []
    lines.append("namespace Ripple")
    lines.append("namespace Number")
    lines.append("namespace Modular")
    lines.append("")
    if warning:
        lines.append(warning)
        lines.append("")
    lines.append(lean_prime_list_snippet(primes, primes_name).rstrip())
    lines.extend(
        [
            "",
            f"theorem {theorem_name}",
            "    {B pChunkSize pNumChunks qChunkSize qNumChunks : ℕ}",
            "    (hlarge : ∀ p ∈ " + primes_name + ", phi41Level41SturmBound < p)",
            "    (hbound : ∀ n : ℕ, n < phi41Level41SturmBound →",
            "      |truncCoeffArrayAt",
            "        (phi41Level41RecurrenceCoeffArray phi41Level41SturmBound) n| ≤",
            "          (B : ℤ))",
            f"    (hB : (B : ℤ) < ({primes_name}.prod : ℤ))",
            "    (hPcover :",
            "      (phi41Level41SturmBound + 40) / 41 ≤ pChunkSize * pNumChunks)",
            "    (hQcover :",
            "      phi41Level41SturmBound ≤ qChunkSize * qNumChunks)",
            "    (PE4Z PE6Z QE4Z QE6Z : Array ℤ)",
            "    (PE4M PE6M PE2E4M QE4M QE6M QE2E4M : ℕ → Array ℤ)",
            "    (PCompressedM QM : ℕ → Array (Array ℤ))",
            "    (hPE4Exact :",
            "      truncCoeffArrayEqFirstChunked",
            "        ((phi41Level41SturmBound + 40) / 41) pChunkSize pNumChunks",
            "        (E4TruncCoeffArray ((phi41Level41SturmBound + 40) / 41))",
            "        PE4Z = true)",
            "    (hPE6Exact :",
            "      truncCoeffArrayEqFirstChunked",
            "        ((phi41Level41SturmBound + 40) / 41) pChunkSize pNumChunks",
            "        (E6TruncCoeffArray ((phi41Level41SturmBound + 40) / 41))",
            "        PE6Z = true)",
            "    (hQE4Exact :",
            "      truncCoeffArrayEqFirstChunked",
            "        phi41Level41SturmBound qChunkSize qNumChunks",
            "        (E4TruncCoeffArray phi41Level41SturmBound) QE4Z = true)",
            "    (hQE6Exact :",
            "      truncCoeffArrayEqFirstChunked",
            "        phi41Level41SturmBound qChunkSize qNumChunks",
            "        (E6TruncCoeffArray phi41Level41SturmBound) QE6Z = true)",
            f"    (hPE4Mod : ∀ p ∈ {primes_name},",
            "      truncCoeffArrayModEqFirstChunked",
            "        ((phi41Level41SturmBound + 40) / 41) p pChunkSize pNumChunks",
            "        PE4Z (PE4M p) = true)",
            f"    (hPE6Mod : ∀ p ∈ {primes_name},",
            "      truncCoeffArrayModEqFirstChunked",
            "        ((phi41Level41SturmBound + 40) / 41) p pChunkSize pNumChunks",
            "        PE6Z (PE6M p) = true)",
            f"    (hPE2E4Deriv : ∀ p ∈ {primes_name},",
            "      truncCoeffArrayE2E4DerivRelationChunked",
            "        ((phi41Level41SturmBound + 40) / 41) p pChunkSize pNumChunks",
            "        (PE4M p) (PE6M p) (PE2E4M p) = true)",
            f"    (hQE4Mod : ∀ p ∈ {primes_name},",
            "      truncCoeffArrayModEqFirstChunked",
            "        phi41Level41SturmBound p qChunkSize qNumChunks",
            "        QE4Z (QE4M p) = true)",
            f"    (hQE6Mod : ∀ p ∈ {primes_name},",
            "      truncCoeffArrayModEqFirstChunked",
            "        phi41Level41SturmBound p qChunkSize qNumChunks",
            "        QE6Z (QE6M p) = true)",
            f"    (hQE2E4Deriv : ∀ p ∈ {primes_name},",
            "      truncCoeffArrayE2E4DerivRelationChunked",
            "        phi41Level41SturmBound p qChunkSize qNumChunks",
            "        (QE4M p) (QE6M p) (QE2E4M p) = true)",
            f"    (hPcert : ∀ p ∈ {primes_name},",
            "      phi41QRecurrenceRowsModCertificateChunkedWithCoeffArrays",
            "        ((phi41Level41SturmBound + 40) / 41) p pChunkSize pNumChunks",
            "        (PE4M p) (PE6M p) (PE2E4M p)",
            "        (PCompressedM p) = true)",
            f"    (hQcert : ∀ p ∈ {primes_name},",
            "      phi41QRecurrenceRowsModCertificateChunkedWithCoeffArrays",
            "        phi41Level41SturmBound p qChunkSize qNumChunks",
            "        (QE4M p) (QE6M p) (QE2E4M p)",
            "        (QM p) = true)",
            "    (QPartsM ContributionsM : ℕ → Array (Array ℤ))",
            "    (FinalM : ℕ → Array ℤ)",
            f"    (hQParts : ∀ p ∈ {primes_name},",
            "      ∀ x : ℕ, x ≤ 42 → ∀ c : ℕ, c < qNumChunks →",
            "        phi41QPartTableFromRowsModEqRowChunk",
            "          phi41Level41SturmBound p x (c * qChunkSize) qChunkSize",
            "          (QM p) (QPartsM p) = true)",
            f"    (hContributions : ∀ p ∈ {primes_name},",
            "      ∀ x : ℕ, x ≤ 42 → ∀ c : ℕ, c < qNumChunks →",
            "        phi41ContributionTableFromQPartsModEqRowChunk",
            "          phi41Level41SturmBound",
            "          ((phi41Level41SturmBound + 40) / 41)",
            "          p x (c * qChunkSize) qChunkSize",
            "          (PCompressedM p) (QPartsM p) (ContributionsM p) = true)",
            f"    (hFinal : ∀ p ∈ {primes_name},",
            "      ∀ c : ℕ, c < qNumChunks →",
            "      phi41FinalFromContributionsModEqChunk",
            "        phi41Level41SturmBound p (c * qChunkSize) qChunkSize",
            "        (ContributionsM p) (FinalM p) = true)",
            f"    (hzero : ∀ p ∈ {primes_name},",
            "      truncCoeffArrayFirstZeroModChunked",
            "        phi41Level41SturmBound p qChunkSize qNumChunks",
            "        (FinalM p) = true) :",
            "    phi41Level41RecurrenceCoeffArrayFirstZero phi41Level41SturmBound = true := by",
            "  refine",
            "    phi41Level41RecurrenceCoeffArrayFirstZero_of_prime_crt_bounded_row_table_bools_with_final",
            f"      {primes_name}_nodup {primes_name}_prime hlarge hbound hB",
            "      PE4M PE6M PE2E4M QE4M QE6M QE2E4M",
            "      PCompressedM QM FinalM",
            "      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_",
            "  · intro p hp",
            "    exact",
            "      (TruncCoeffArrayModEq.of_eqFirst",
            "        (truncCoeffArrayEqFirst_of_chunked hPcover hPE4Exact)).trans",
            "        (TruncCoeffArrayModEq.of_modEqFirstChunked hPcover",
            "          (hPE4Mod p hp))",
            "  · intro p hp",
            "    exact",
            "      (TruncCoeffArrayModEq.of_eqFirst",
            "        (truncCoeffArrayEqFirst_of_chunked hPcover hPE6Exact)).trans",
            "        (TruncCoeffArrayModEq.of_modEqFirstChunked hPcover",
            "          (hPE6Mod p hp))",
            "  · intro p hp",
            "    exact",
            "      TruncCoeffArrayModEq.E2E4_of_E4_deriv_relation",
            "        ((TruncCoeffArrayModEq.of_eqFirst",
            "          (truncCoeffArrayEqFirst_of_chunked hPcover hPE4Exact)).trans",
            "          (TruncCoeffArrayModEq.of_modEqFirstChunked hPcover",
            "            (hPE4Mod p hp)))",
            "        ((TruncCoeffArrayModEq.of_eqFirst",
            "          (truncCoeffArrayEqFirst_of_chunked hPcover hPE6Exact)).trans",
            "          (TruncCoeffArrayModEq.of_modEqFirstChunked hPcover",
            "            (hPE6Mod p hp)))",
            "        (truncCoeffArrayE2E4DerivRelation_of_chunked",
            "          hPcover (hPE2E4Deriv p hp))",
            "  · intro p hp",
            "    exact",
            "      (TruncCoeffArrayModEq.of_eqFirst",
            "        (truncCoeffArrayEqFirst_of_chunked hQcover hQE4Exact)).trans",
            "        (TruncCoeffArrayModEq.of_modEqFirstChunked hQcover",
            "          (hQE4Mod p hp))",
            "  · intro p hp",
            "    exact",
            "      (TruncCoeffArrayModEq.of_eqFirst",
            "        (truncCoeffArrayEqFirst_of_chunked hQcover hQE6Exact)).trans",
            "        (TruncCoeffArrayModEq.of_modEqFirstChunked hQcover",
            "          (hQE6Mod p hp))",
            "  · intro p hp",
            "    exact",
            "      TruncCoeffArrayModEq.E2E4_of_E4_deriv_relation",
            "        ((TruncCoeffArrayModEq.of_eqFirst",
            "          (truncCoeffArrayEqFirst_of_chunked hQcover hQE4Exact)).trans",
            "          (TruncCoeffArrayModEq.of_modEqFirstChunked hQcover",
            "            (hQE4Mod p hp)))",
            "        ((TruncCoeffArrayModEq.of_eqFirst",
            "          (truncCoeffArrayEqFirst_of_chunked hQcover hQE6Exact)).trans",
            "          (TruncCoeffArrayModEq.of_modEqFirstChunked hQcover",
            "            (hQE6Mod p hp)))",
            "        (truncCoeffArrayE2E4DerivRelation_of_chunked",
            "          hQcover (hQE2E4Deriv p hp))",
            "  · intro p hp",
            "    exact",
            "      phi41QRecurrenceRowsModCertificateWithCoeffArrays_of_chunked",
            "        hPcover (hPcert p hp)",
            "  · intro p hp",
            "    exact",
            "      phi41QRecurrenceRowsModCertificateWithCoeffArrays_of_chunked",
            "        hQcover (hQcert p hp)",
            "  · intro p hp",
            "    exact",
            "      TruncCoeffArrayModEq.phi41Level41RecurrenceCoeffArrayFromRows_of_intermediate",
            "        (by rfl)",
            "        (TruncCoeffArrayTableModEq.of_phi41QPartTableFromRowsModEqRowChunks",
            "          hQcover (hQParts p hp))",
            "        (TruncCoeffArrayTableModEq.of_phi41ContributionTableFromQPartsModEqRowChunks",
            "          hQcover (hContributions p hp))",
            "        (TruncCoeffArrayModEq.of_phi41FinalFromContributionsModEqChunks",
            "          hQcover",
            "          (hFinal p hp))",
            "  · intro p hp",
            "    exact truncCoeffArrayFirstZeroMod_of_chunked hQcover (hzero p hp)",
            "  · intro j hj",
            "    exact phi41LevelOneDenseRow_derivative_identity_of_base",
            "      j hj",
            "      (E4ZSeries_cubed_derivative_identity_of_E4_derivative_identity",
            "        E4ZSeries_derivative_identity)",
            "      deltaEulerSeriesZ_derivative_identity",
            "",
            "end Modular",
            "end Number",
            "end Ripple",
            "",
        ]
    )
    return "\n".join(lines)


def verify_crt_manifest(manifest: dict, stack: str, jobs: int = 1) -> dict:
    errors: list[str] = []
    if manifest.get("format") != "phi41-recurrence-crt-manifest-v1":
        errors.append("unexpected manifest format")

    try:
        bound = int(manifest["bound"])
        extra = int(manifest["extra"])
        prime_results = manifest["prime_results"]
        primes = [int(row["prime"]) for row in prime_results]
    except (KeyError, TypeError, ValueError) as exc:
        return {"ok": False, "errors": [f"malformed manifest: {exc}"]}

    if len(set(primes)) != len(primes):
        errors.append("prime_results contains duplicate primes")
    if not all(is_prime_u64(p) for p in primes):
        errors.append("prime_results contains non-prime or non-u64 values")

    product = math.prod(primes)
    expected_scalars = {
        "precision": bound + extra,
        "small_precision": (bound + extra + 40) // 41,
        "prime_count": len(primes),
        "prime_product_bits": product.bit_length(),
        "prime_product": str(product),
        "primes_distinct": len(set(primes)) == len(primes),
        "primes_verified_u64_miller_rabin": all(is_prime_u64(p) for p in primes),
    }
    for key, expected in expected_scalars.items():
        if manifest.get(key) != expected:
            errors.append(f"{key}: expected {expected!r}, got {manifest.get(key)!r}")

    terms = run_gp_terms(stack)
    all_sturm_zero = True
    if jobs <= 1 or len(prime_results) <= 1:
        for row in prime_results:
            ok, row_errors = verify_prime_manifest_row(bound, extra, row, terms)
            all_sturm_zero = all_sturm_zero and ok
            errors.extend(row_errors)
    else:
        print(
            f"CRT_VERIFY_PARALLEL_JOBS\t{jobs}\tPRIMES\t{len(prime_results)}",
            file=sys.stderr,
            flush=True,
        )
        with concurrent.futures.ProcessPoolExecutor(max_workers=jobs) as executor:
            futures = [
                executor.submit(verify_prime_manifest_row, bound, extra, row, terms)
                for row in prime_results
            ]
            for future in concurrent.futures.as_completed(futures):
                ok, row_errors = future.result()
                all_sturm_zero = all_sturm_zero and ok
                errors.extend(row_errors)

    if manifest.get("all_sturm_zero") != all_sturm_zero:
        errors.append(
            f"all_sturm_zero: expected {all_sturm_zero}, got {manifest.get('all_sturm_zero')}"
        )

    if "exact_bound" in manifest:
        bounds = final_coeff_abs_bounds(bound, extra, stack)
        sturm_bounds = bounds[:bound]
        max_bound = max(sturm_bounds) if sturm_bounds else 0
        max_idx = sturm_bounds.index(max_bound) if sturm_bounds else 0
        expected_exact = {
            "max_bound_index": max_idx,
            "max_bound_bits": max_bound.bit_length(),
            "crt_product_bits_needed": max_bound.bit_length() + 1,
            "max_bound": str(max_bound),
            "product_gt_max_bound": product > max_bound,
        }
        exact = manifest["exact_bound"]
        for key, expected in expected_exact.items():
            if exact.get(key) != expected:
                errors.append(
                    f"exact_bound.{key}: expected {expected!r}, got {exact.get(key)!r}"
                )

    if "log_bound" in manifest:
        log = manifest["log_bound"]
        safety_bits = int(log.get("safety_bits", 8))
        max_idx, max_bits = final_coeff_log_bound_bits(bound, extra, stack, safety_bits)
        expected_log = {
            "max_log_bound_index": max_idx,
            "safety_bits": safety_bits,
            "max_log_bound_bits": max_bits,
            "crt_product_bits_needed": max_bits + 1,
            "product_bits_gt_needed": product.bit_length() > max_bits + 1,
        }
        for key, expected in expected_log.items():
            if log.get(key) != expected:
                errors.append(
                    f"log_bound.{key}: expected {expected!r}, got {log.get(key)!r}"
                )

    return {"ok": not errors, "errors": errors}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--bound", type=int, default=3528)
    parser.add_argument("--extra", type=int, default=128)
    parser.add_argument("--prime", type=int, default=0)
    parser.add_argument(
        "--primes",
        default="",
        help="comma-separated primes; reuses the Phi_41 sparse term list across runs",
    )
    parser.add_argument(
        "--auto-prime-count",
        type=int,
        default=0,
        help="choose this many descending primes automatically",
    )
    parser.add_argument(
        "--auto-prime-bits",
        type=int,
        default=61,
        help="bit size used by --auto-prime-count",
    )
    parser.add_argument(
        "--auto-prime-cover-log-bound",
        action="store_true",
        help="choose enough descending primes to beat the --bound-log-bits CRT size",
    )
    parser.add_argument(
        "--bound-bits",
        action="store_true",
        help="estimate absolute coefficient bounds for sizing a CRT certificate",
    )
    parser.add_argument(
        "--bound-log-bits",
        action="store_true",
        help="fast floating-point log2 bound estimate for CRT sizing",
    )
    parser.add_argument(
        "--safety-bits",
        type=int,
        default=8,
        help="extra bits added to --bound-log-bits for floating-point slack",
    )
    parser.add_argument(
        "--prime-bits",
        type=int,
        default=61,
        help="nominal prime size used when reporting --bound-log-bits CRT counts",
    )
    parser.add_argument(
        "--crt-json",
        action="store_true",
        help="emit a JSON CRT manifest for the primes in --primes",
    )
    parser.add_argument(
        "--crt-json-out",
        default="",
        help="write --crt-json output to this file instead of stdout",
    )
    parser.add_argument(
        "--crt-json-resume",
        default="",
        help="reuse prime rows from an existing manifest with matching bound/extra",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="parallel worker processes for missing --crt-json prime rows",
    )
    parser.add_argument(
        "--crt-json-exact-bound",
        action="store_true",
        help="include exact triangle-inequality bounds in --crt-json",
    )
    parser.add_argument(
        "--crt-json-log-bound",
        action="store_true",
        help="include fast log2 bound sizing in --crt-json",
    )
    parser.add_argument(
        "--lean-prime-list",
        action="store_true",
        help="emit Lean definitions/proofs for the primes in --primes",
    )
    parser.add_argument(
        "--lean-prime-list-name",
        default="phi41CRTPrimes",
        help="definition name used by --lean-prime-list",
    )
    parser.add_argument(
        "--verify-crt-json",
        default="",
        help="recompute and verify an existing CRT manifest JSON file",
    )
    parser.add_argument(
        "--lean-crt-skeleton",
        default="",
        help="emit a Lean theorem scaffold from an existing CRT manifest JSON file",
    )
    parser.add_argument(
        "--lean-function-crt-skeleton",
        default="",
        help="emit a Lean theorem scaffold for the function-valued CRT certificate interface",
    )
    parser.add_argument(
        "--lean-row-table-crt-skeleton",
        default="",
        help="emit a Lean theorem scaffold for the row-table CRT certificate interface",
    )
    parser.add_argument(
        "--lean-row-table-data",
        action="store_true",
        help="emit Lean array literals for modular recurrence P/Q row tables",
    )
    parser.add_argument(
        "--lean-row-table-data-final",
        action="store_true",
        help="also emit the folded final residue array; requires PARI/GP",
    )
    parser.add_argument(
        "--lean-row-table-data-prefixes",
        action="store_true",
        help="also emit prefix-sum arrays for QParts, Contributions, and Final",
    )
    parser.add_argument(
        "--lean-row-table-data-coeffs-only",
        action="store_true",
        help="emit only P/Q E-series coefficient arrays, omitting recurrence row tables",
    )
    parser.add_argument(
        "--lean-row-table-data-name",
        default="phi41RowTableData",
        help="definition prefix used by --lean-row-table-data",
    )
    parser.add_argument(
        "--lean-row-table-intermediate-proofs",
        action="store_true",
        help="emit rfl proof snippets for generated QParts/Contributions/Final chunks",
    )
    parser.add_argument(
        "--lean-row-table-recurrence-proofs",
        action="store_true",
        help="emit rfl proof snippets for generated P/Q modular recurrence chunks",
    )
    parser.add_argument(
        "--lean-row-table-row-residue-literal-chunk-data",
        action="store_true",
        help="emit modular P/Q recurrence row chunk literals",
    )
    parser.add_argument(
        "--lean-row-table-fn-recurrence-proofs",
        action="store_true",
        help="emit function-valued recurrence proofs for generated P/Q row chunks",
    )
    parser.add_argument(
        "--lean-row-table-coeff-proofs",
        action="store_true",
        help="emit rfl proof snippets for generated P/Q E4/E6/E2E4 coefficient arrays",
    )
    parser.add_argument(
        "--lean-row-table-exact-coeff-data",
        action="store_true",
        help="emit exact integer P/Q E4/E6 coefficient arrays",
    )
    parser.add_argument(
        "--lean-row-table-exact-coeff-proofs",
        action="store_true",
        help="emit exact equality proofs for generated P/Q E4/E6 coefficient arrays",
    )
    parser.add_argument(
        "--lean-row-table-exact-mod-proofs",
        action="store_true",
        help="emit modular proofs from exact P/Q E4/E6 arrays to residue arrays",
    )
    parser.add_argument(
        "--lean-row-table-exact-literal-chunk-data",
        action="store_true",
        help="emit exact P/Q E4/E6 coefficient chunk literals",
    )
    parser.add_argument(
        "--lean-row-table-exact-literal-mod-proofs",
        action="store_true",
        help="prove true P/Q E4/E6 arrays congruent to residue arrays via exact chunks",
    )
    parser.add_argument(
        "--lean-row-table-residue-literal-chunk-data",
        action="store_true",
        help="emit modular P/Q E4/E6 residue coefficient chunk literals",
    )
    parser.add_argument(
        "--lean-row-table-exact-to-residue-fn-proofs",
        action="store_true",
        help="prove true P/Q E4/E6 arrays congruent to residue chunk functions",
    )
    parser.add_argument(
        "--lean-row-table-e2e4-residue-fn-proofs",
        action="store_true",
        help="emit E2E4 derivative-relation proofs for residue chunk functions",
    )
    parser.add_argument(
        "--lean-row-table-recurrence-side",
        choices=["p", "q", "both"],
        default="both",
        help="which recurrence side to emit for --lean-row-table-recurrence-proofs",
    )
    parser.add_argument(
        "--lean-row-table-coeff-side",
        choices=["p", "q", "both"],
        default="both",
        help="which coefficient-array side to emit for --lean-row-table-coeff-proofs",
    )
    parser.add_argument(
        "--lean-row-table-coeff-labels",
        default="",
        help=(
            "comma-separated coefficient proof labels to emit, e.g. "
            "QE4,QE6,QE2E4DerivRelation"
        ),
    )
    parser.add_argument(
        "--lean-row-table-proof-chunk-size",
        type=int,
        default=64,
        help="coefficient chunk size used by --lean-row-table-intermediate-proofs",
    )
    parser.add_argument(
        "--lean-row-table-proof-row-start",
        type=int,
        default=0,
        help="first row emitted by --lean-row-table-intermediate-proofs",
    )
    parser.add_argument(
        "--lean-row-table-proof-row-stop",
        type=int,
        default=43,
        help="exclusive row stop emitted by --lean-row-table-intermediate-proofs",
    )
    parser.add_argument(
        "--lean-row-table-proof-entry-mode",
        action="store_true",
        help="prove generated chunks through entry-to-chunk bridges; experimental",
    )
    parser.add_argument(
        "--lean-crt-theorem-name",
        default="phi41Level41RecurrenceCoeffArrayFirstZero_from_crt_manifest",
        help="theorem name used by --lean-crt-skeleton",
    )
    parser.add_argument("--stack", default="512M")
    args = parser.parse_args()

    if args.lean_row_table_data:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-data expects exactly one prime")
            prime = primes[0]
        terms = run_gp_terms(args.stack) if args.lean_row_table_data_final else None
        if args.lean_row_table_data_prefixes and terms is None:
            raise SystemExit("--lean-row-table-data-prefixes requires --lean-row-table-data-final")
        print(
            lean_row_table_data(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                terms,
                args.lean_row_table_data_prefixes,
                args.lean_row_table_data_coeffs_only,
            ),
            end="",
        )
    elif args.lean_row_table_intermediate_proofs:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-intermediate-proofs expects exactly one prime")
            prime = primes[0]
        print(
            lean_row_table_intermediate_proofs(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_proof_row_start,
                args.lean_row_table_proof_row_stop,
                args.lean_row_table_proof_entry_mode,
            ),
            end="",
        )
    elif args.lean_row_table_recurrence_proofs:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-recurrence-proofs expects exactly one prime")
            prime = primes[0]
        print(
            lean_row_table_recurrence_proofs(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_proof_row_start,
                args.lean_row_table_proof_row_stop,
                args.lean_row_table_recurrence_side,
            ),
            end="",
        )
    elif args.lean_row_table_row_residue_literal_chunk_data:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-row-residue-literal-chunk-data expects exactly one prime")
            prime = primes[0]
        print(
            lean_row_table_row_residue_literal_chunk_data(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_recurrence_side,
                args.lean_row_table_proof_row_start,
                args.lean_row_table_proof_row_stop,
            ),
            end="",
        )
    elif args.lean_row_table_fn_recurrence_proofs:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-fn-recurrence-proofs expects exactly one prime")
            prime = primes[0]
        print(
            lean_row_table_fn_recurrence_proofs(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_proof_row_start,
                args.lean_row_table_proof_row_stop,
                args.lean_row_table_recurrence_side,
            ),
            end="",
        )
    elif args.lean_row_table_coeff_proofs:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-coeff-proofs expects exactly one prime")
            prime = primes[0]
        coeff_labels = {
            label.strip()
            for label in args.lean_row_table_coeff_labels.split(",")
            if label.strip()
        }
        print(
            lean_row_table_coeff_proofs(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_coeff_side,
                coeff_labels or None,
            ),
            end="",
        )
    elif args.lean_row_table_exact_coeff_data:
        print(
            lean_row_table_exact_coeff_data(
                args.bound,
                args.lean_row_table_data_name,
            ),
            end="",
        )
    elif args.lean_row_table_exact_coeff_proofs:
        coeff_labels = {
            label.strip()
            for label in args.lean_row_table_coeff_labels.split(",")
            if label.strip()
        }
        print(
            lean_row_table_exact_coeff_proofs(
                args.bound,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_coeff_side,
                coeff_labels or None,
            ),
            end="",
        )
    elif args.lean_row_table_exact_mod_proofs:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-exact-mod-proofs expects exactly one prime")
            prime = primes[0]
        coeff_labels = {
            label.strip()
            for label in args.lean_row_table_coeff_labels.split(",")
            if label.strip()
        }
        print(
            lean_row_table_exact_mod_proofs(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_coeff_side,
                coeff_labels or None,
            ),
            end="",
        )
    elif args.lean_row_table_exact_literal_chunk_data:
        coeff_labels = {
            label.strip()
            for label in args.lean_row_table_coeff_labels.split(",")
            if label.strip()
        }
        print(
            lean_row_table_exact_literal_chunk_data(
                args.bound,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_coeff_side,
                coeff_labels or None,
            ),
            end="",
        )
    elif args.lean_row_table_exact_literal_mod_proofs:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-exact-literal-mod-proofs expects exactly one prime")
            prime = primes[0]
        coeff_labels = {
            label.strip()
            for label in args.lean_row_table_coeff_labels.split(",")
            if label.strip()
        }
        print(
            lean_row_table_exact_literal_mod_proofs(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_coeff_side,
                coeff_labels or None,
            ),
            end="",
        )
    elif args.lean_row_table_residue_literal_chunk_data:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-residue-literal-chunk-data expects exactly one prime")
            prime = primes[0]
        coeff_labels = {
            label.strip()
            for label in args.lean_row_table_coeff_labels.split(",")
            if label.strip()
        }
        print(
            lean_row_table_residue_literal_chunk_data(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_coeff_side,
                coeff_labels or None,
            ),
            end="",
        )
    elif args.lean_row_table_exact_to_residue_fn_proofs:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-exact-to-residue-fn-proofs expects exactly one prime")
            prime = primes[0]
        coeff_labels = {
            label.strip()
            for label in args.lean_row_table_coeff_labels.split(",")
            if label.strip()
        }
        print(
            lean_row_table_exact_to_residue_fn_proofs(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_coeff_side,
                coeff_labels or None,
            ),
            end="",
        )
    elif args.lean_row_table_e2e4_residue_fn_proofs:
        prime = args.prime
        if prime == 0:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
            if len(primes) != 1:
                raise SystemExit("--lean-row-table-e2e4-residue-fn-proofs expects exactly one prime")
            prime = primes[0]
        coeff_labels = {
            label.strip()
            for label in args.lean_row_table_coeff_labels.split(",")
            if label.strip()
        }
        print(
            lean_row_table_e2e4_residue_fn_proofs(
                args.bound,
                prime,
                args.lean_row_table_data_name,
                args.lean_row_table_proof_chunk_size,
                args.lean_row_table_coeff_side,
                coeff_labels or None,
            ),
            end="",
        )
    elif args.lean_row_table_crt_skeleton:
        with open(args.lean_row_table_crt_skeleton, "r", encoding="utf-8") as handle:
            manifest = json.load(handle)
        print(
            lean_row_table_crt_skeleton(
                manifest,
                args.lean_crt_theorem_name,
                args.lean_prime_list_name,
            ),
            end="",
        )
    elif args.lean_function_crt_skeleton:
        with open(args.lean_function_crt_skeleton, "r", encoding="utf-8") as handle:
            manifest = json.load(handle)
        print(
            lean_function_crt_skeleton(
                manifest,
                args.lean_crt_theorem_name,
                args.lean_prime_list_name,
            ),
            end="",
        )
    elif args.lean_crt_skeleton:
        with open(args.lean_crt_skeleton, "r", encoding="utf-8") as handle:
            manifest = json.load(handle)
        print(
            lean_crt_skeleton(
                manifest,
                args.lean_crt_theorem_name,
                args.lean_prime_list_name,
            ),
            end="",
        )
    elif args.verify_crt_json:
        with open(args.verify_crt_json, "r", encoding="utf-8") as handle:
            manifest = json.load(handle)
        result = verify_crt_manifest(manifest, args.stack, args.jobs)
        print(json.dumps(result, indent=2, sort_keys=True), flush=True)
        if not result["ok"]:
            raise SystemExit(1)
    elif args.lean_prime_list:
        if args.auto_prime_cover_log_bound:
            _max_idx, max_bits = final_coeff_log_bound_bits(
                args.bound,
                args.extra,
                args.stack,
                args.safety_bits,
            )
            primes = resolve_primes_covering_bits(
                args.primes,
                args.auto_prime_count,
                args.auto_prime_bits,
                max_bits + 1,
            )
            print(
                "CRT_LOG_BOUND\t"
                f"{max_bits}\tCRT_PRODUCT_BITS_NEEDED\t{max_bits + 1}\t"
                f"PRIME_COUNT\t{len(primes)}",
                file=sys.stderr,
                flush=True,
            )
        else:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
        print(lean_prime_list_snippet(primes, args.lean_prime_list_name), end="")
    elif args.crt_json:
        precomputed_log_bound = None
        if args.auto_prime_cover_log_bound:
            precomputed_log_bound = final_coeff_log_bound_bits(
                args.bound,
                args.extra,
                args.stack,
                args.safety_bits,
            )
            _, max_bits = precomputed_log_bound
            primes = resolve_primes_covering_bits(
                args.primes,
                args.auto_prime_count,
                args.auto_prime_bits,
                max_bits + 1,
            )
            print(
                "CRT_LOG_BOUND\t"
                f"{max_bits}\tCRT_PRODUCT_BITS_NEEDED\t{max_bits + 1}\t"
                f"PRIME_COUNT\t{len(primes)}",
                file=sys.stderr,
                flush=True,
            )
        else:
            primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
        existing_manifest = None
        if args.crt_json_resume:
            with open(args.crt_json_resume, "r", encoding="utf-8") as handle:
                existing_manifest = json.load(handle)
        manifest = crt_manifest(
            args.bound,
            args.extra,
            primes,
            args.stack,
            args.crt_json_exact_bound,
            args.crt_json_log_bound or args.auto_prime_cover_log_bound,
            args.safety_bits,
            existing_manifest,
            precomputed_log_bound,
            args.crt_json_out,
            args.jobs,
        )
        payload = json.dumps(manifest, indent=2, sort_keys=True)
        if args.crt_json_out:
            write_json_file(args.crt_json_out, manifest)
        else:
            print(payload, flush=True)
    elif args.bound_bits:
        bounds = final_coeff_abs_bounds(args.bound, args.extra, args.stack)
        sturm_bounds = bounds[:args.bound]
        max_bound = max(sturm_bounds) if sturm_bounds else 0
        max_idx = sturm_bounds.index(max_bound) if sturm_bounds else 0
        print(f"BOUND\t{args.bound}", flush=True)
        print(f"PREC\t{args.bound + args.extra}", flush=True)
        print(f"SMALL_PREC\t{(args.bound + args.extra + 40) // 41}", flush=True)
        print(f"MAX_BOUND_INDEX\t{max_idx}", flush=True)
        print(f"MAX_BOUND_BITS\t{max_bound.bit_length()}", flush=True)
        print(f"CRT_PRODUCT_BITS_NEEDED\t{max_bound.bit_length() + 1}", flush=True)
    elif args.bound_log_bits:
        max_idx, max_bits = final_coeff_log_bound_bits(
            args.bound, args.extra, args.stack, args.safety_bits
        )
        print(f"BOUND\t{args.bound}", flush=True)
        print(f"PREC\t{args.bound + args.extra}", flush=True)
        print(f"SMALL_PREC\t{(args.bound + args.extra + 40) // 41}", flush=True)
        print(f"MAX_LOG_BOUND_INDEX\t{max_idx}", flush=True)
        print(f"SAFETY_BITS\t{args.safety_bits}", flush=True)
        print(f"MAX_LOG_BOUND_BITS\t{max_bits}", flush=True)
        print(f"CRT_PRODUCT_BITS_NEEDED\t{max_bits + 1}", flush=True)
        print(f"NOMINAL_PRIME_BITS\t{args.prime_bits}", flush=True)
        print(
            f"NOMINAL_PRIME_COUNT\t{ceil_div(max_bits + 1, args.prime_bits)}",
            flush=True,
        )
    elif args.primes.strip():
        primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
        terms = run_gp_terms(args.stack)
        product = math.prod(primes)
        print(f"PRIME_COUNT\t{len(primes)}", flush=True)
        print(f"PRIME_PRODUCT_BITS\t{product.bit_length()}", flush=True)
        for idx, prime in enumerate(primes):
            if idx:
                print("---", flush=True)
            valuation, ok = check_with_terms(args.bound, args.extra, prime, terms)
            print_result(args.bound, args.extra, prime, valuation, ok)
    elif args.auto_prime_count:
        primes = resolve_primes(args.primes, args.auto_prime_count, args.auto_prime_bits)
        terms = run_gp_terms(args.stack)
        product = math.prod(primes)
        print(f"PRIME_COUNT\t{len(primes)}", flush=True)
        print(f"PRIME_PRODUCT_BITS\t{product.bit_length()}", flush=True)
        for idx, prime in enumerate(primes):
            if idx:
                print("---", flush=True)
            valuation, ok = check_with_terms(args.bound, args.extra, prime, terms)
            print_result(args.bound, args.extra, prime, valuation, ok)
    else:
        mod = args.prime or None
        valuation, ok = check(args.bound, args.extra, mod, args.stack)
        print_result(args.bound, args.extra, args.prime, valuation, ok)


if __name__ == "__main__":
    main()
