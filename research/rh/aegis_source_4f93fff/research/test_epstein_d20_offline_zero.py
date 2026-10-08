import mpmath as mp


def _chi_minus4(n: int) -> int:
    if n % 2 == 0:
        return 0
    return 1 if n % 4 == 1 else -1


def _chi_5(n: int) -> int:
    residue = n % 5
    if residue == 0:
        return 0
    return 1 if residue in (1, 4) else -1


def _chi_minus20(n: int) -> int:
    return _chi_minus4(n) * _chi_5(n)


def _dirichlet_l_hurwitz(s: mp.mpc, modulus: int, character) -> mp.mpc:
    return mp.power(modulus, -s) * sum(
        mp.mpf(character(a)) * mp.zeta(s, mp.mpf(a) / modulus)
        for a in range(1, modulus + 1)
    )


def _components(s: mp.mpc) -> tuple[mp.mpc, mp.mpc]:
    a = mp.zeta(s) * _dirichlet_l_hurwitz(s, 20, _chi_minus20)
    b = _dirichlet_l_hurwitz(s, 4, _chi_minus4) * _dirichlet_l_hurwitz(
        s, 5, _chi_5
    )
    return a, b


def test_d20_principal_has_verified_numerical_offcritical_zero() -> None:
    mp.mp.dps = 70
    rho = mp.mpc(
        "0.8231873164780866676470730774243753825976015474266715777672808951",
        "44.000113180236897278062246953570634677914187577294800476462654179",
    )
    a, b = _components(rho)
    residual = abs(a + b)

    assert mp.re(rho) > mp.mpf("0.5")
    assert residual < mp.mpf("1e-60")
    assert abs(a) > mp.mpf("0.7")
    assert abs(b) > mp.mpf("0.7")
    assert abs(a / b + 1) < mp.mpf("1e-60")

    reflected = 1 - mp.conj(rho)
    ar, br = _components(reflected)
    assert abs(ar + br) < mp.mpf("1e-58")
