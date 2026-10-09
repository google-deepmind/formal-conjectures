from __future__ import annotations

import numpy as np

from harness.sdk.weil_prime_support_kernel import (
    assemble_prime_galerkin_closed_form,
    exact_sinc_gram_and_moment,
    sinc_product_cosine_integral,
)
from harness.sdk.weil_spectral_inertia_probe import SpectralProbeConfig, WeilSpectralInertiaProbe


def test_sinc_product_cosine_integral_has_exact_paley_wiener_support_cutoff() -> None:
    tau = 2.0
    scale = 1.0

    inside = sinc_product_cosine_integral(0, 0, 3.9, tau=tau, scale_factor=scale)
    boundary = sinc_product_cosine_integral(0, 0, 4.0, tau=tau, scale_factor=scale)
    outside = sinc_product_cosine_integral(0, 0, 4.1, tau=tau, scale_factor=scale)

    assert inside > 0.0
    assert boundary == 0.0
    assert outside == 0.0


def test_exact_infinite_domain_gram_and_moment_are_closed_form() -> None:
    k_indices = np.arange(-3, 4, dtype=int)
    gram, moment = exact_sinc_gram_and_moment(k_indices, tau=2.0, scale_factor=1.0)

    expected = 1.0 / 4.0
    assert np.max(np.abs(gram - expected * np.eye(len(k_indices)))) < 1e-15
    assert np.max(np.abs(moment - expected)) < 1e-15


def test_prime_galerkin_matrix_is_independent_of_cutoff_after_support_saturation() -> None:
    common = dict(tau=2.0, k_basis_dim=4, n_quad=512, t_bound=30.0)
    p100 = WeilSpectralInertiaProbe(SpectralProbeConfig(p_cutoff=100, **common))
    p20000 = WeilSpectralInertiaProbe(SpectralProbeConfig(p_cutoff=20000, **common))

    m100 = assemble_prime_galerkin_closed_form(p100, scale_factor=1.0)
    m20000 = assemble_prime_galerkin_closed_form(p20000, scale_factor=1.0)

    # For tau=2 and scale=1, products of sinc basis functions have Fourier
    # support in [-4, 4]. Every prime-power shift above 4 is exactly invisible.
    assert m100["support_radius"] == 4.0
    assert m20000["support_radius"] == 4.0
    assert m20000["discarded_prime_power_count"] > 0
    assert m100["active_prime_power_count"] == m20000["active_prime_power_count"]
    assert np.max(np.abs(m100["matrix"] - m20000["matrix"])) < 1e-12


def test_prime_support_kernel_is_diagnostic_only_and_cannot_promote_rh() -> None:
    probe = WeilSpectralInertiaProbe(
        SpectralProbeConfig(
            tau=2.0,
            p_cutoff=2000,
            k_basis_dim=3,
            n_quad=512,
            t_bound=30.0,
        )
    )
    receipt = assemble_prime_galerkin_closed_form(probe, scale_factor=1.0)

    assert receipt["authority"] == "T1_ANALYTIC_CLOSED_FORM_DIAGNOSTIC"
    assert receipt["support_localization_exact_formula"] is True
    assert receipt["infinite_prime_measure_constructed"] is False
    assert receipt["global_weil_positivity_proven"] is False
    assert receipt["rh_proven"] is False
