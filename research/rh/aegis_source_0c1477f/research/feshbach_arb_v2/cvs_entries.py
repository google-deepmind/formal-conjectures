"""Vendored subset of harness/sdk/guinand_weil_arb.py (AEGIS-OMEGA branch agents/rh-proof-closure-swarm-v1,
git blob 0f0cc53d6c428b61df84308296708dc5fd1eb81e): exact Connes-van Suijlekom / CCM closed-form helpers
(arXiv:2607.02828v3).  Copied verbatim except the error class and the spec-bound sequence builder."""
from typing import Optional
from flint import arb, acb


class ArbGalerkinError(ValueError):
    def __init__(self, code: str):
        super().__init__(code)
        self.code = code


def prime_powers_up_to(c: int) -> tuple[tuple[int, int], ...]:
    """Return all ``(q, p)`` with q=p^a <= c, using exact integer arithmetic."""
    if isinstance(c, bool) or not isinstance(c, int) or c < 2:
        raise ArbGalerkinError("CUTOFF_INVALID")
    sieve = [True] * (c + 1)
    sieve[0] = sieve[1] = False
    primes: list[int] = []
    for p in range(2, c + 1):
        if not sieve[p]:
            continue
        primes.append(p)
        if p * p <= c:
            for multiple in range(p * p, c + 1, p):
                sieve[multiple] = False
    powers: list[tuple[int, int]] = []
    for p in primes:
        q = p
        while q <= c:
            powers.append((q, p))
            if q > c // p:
                break
            q *= p
    return tuple(sorted(powers))


def _trigamma(z: acb) -> acb:
    return z.polygamma(acb(1))


def _geometric_remainders(n: int, L: arb, prec_bits: int) -> tuple[arb, arb, arb, arb]:
    """Rigorous auxiliary sums with a bounded, explicit geometric tail."""
    pi = arb.pi()
    omega = 2 * pi * n / L
    omega_sq = omega * omega
    sums = [arb(0), arb(0), arb(0), arb(0)]
    threshold = arb(2) ** (-(prec_bits + 24))
    max_terms = max(96, 2 * prec_bits + 64)
    stop_k: Optional[int] = None

    for k in range(max_terms):
        ck = arb(2 * k) + arb("0.5")
        exp_term = (-ck * L).exp()
        denom = ck * ck + omega_sq
        sums[0] += exp_term / denom
        if n != 0:
            sums[1] += exp_term * omega_sq / (ck * denom)
        sums[2] += exp_term * ck / denom
        sums[3] += exp_term * (ck * ck - omega_sq) / (denom * denom)
        if k > 2 and exp_term < threshold:
            stop_k = k
            break

    if stop_k is None:
        raise ArbGalerkinError("GEOMETRIC_SERIES_BOUND_EXCEEDED")

    next_ck = arb(2 * (stop_k + 1)) + arb("0.5")
    geometric_den = 1 - (-2 * L).exp()
    tail = (-next_ck * L).exp() / geometric_den
    radius = arb(4) * tail
    return tuple(value + arb(0, radius) for value in sums)  # type: ignore[return-value]


def _J(L: arb) -> arb:
    u = (L / 2).exp()
    return -2 * (u + 1).log() + (u * u + 1).log() + 2 * u.atan() + arb(2).log() - arb.pi() / 2


def _kappa(L: arb) -> arb:
    e_l = L.exp()
    return (4 * arb.pi() * (e_l - 1) / (e_l + 1)).log() + arb.const_euler()


