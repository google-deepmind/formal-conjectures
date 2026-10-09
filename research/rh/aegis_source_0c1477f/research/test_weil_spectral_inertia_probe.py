from __future__ import annotations

import math

import numpy as np

from harness.sdk.weil_levy_gap_probe import run_levy_gap_probe
from harness.sdk.weil_spectral_inertia_probe import (
    SpectralProbeConfig,
    WeilSpectralInertiaProbe,
    build_scale_controls,
    generalized_inertia,
    run_convergence_matrix,
    truncated_liouville_control,
    verify_reference_fixture,
)


def test_prime_cutoff_is_not_silently_replaced_by_tau_support_cutoff() -> None:
    unrestricted = WeilSpectralInertiaProbe(
        SpectralProbeConfig(
            tau=2.0,
            p_cutoff=2000,
            k_basis_dim=3,
            n_quad=512,
            t_bound=30.0,
            max_prime_shift=None,
        )
    )
    support_limited = WeilSpectralInertiaProbe(
        SpectralProbeConfig(
            tau=2.0,
            p_cutoff=2000,
            k_basis_dim=3,
            n_quad=512,
            t_bound=30.0,
            max_prime_shift=4.0,
        )
    )

    assert unrestricted.prime_power_count > support_limited.prime_power_count
    assert max(term.shift for term in unrestricted.prime_power_terms) > 4.0
    assert max(term.shift for term in support_limited.prime_power_terms) < 4.0


def test_moment_constraint_is_exact_nullspace_reduction_not_regularization() -> None:
    probe = WeilSpectralInertiaProbe(
        SpectralProbeConfig(
            tau=2.0,
            p_cutoff=100,
            k_basis_dim=4,
            n_quad=1024,
            t_bound=40.0,
        )
    )

    reduced = probe.assemble_moment_restricted(scale_factor=1.0)

    assert reduced.M.shape == (probe.dim - 1, probe.dim - 1)
    assert reduced.G.shape == (probe.dim - 1, probe.dim - 1)
    assert reduced.constraint_basis.shape == (probe.dim, probe.dim - 1)
    assert np.linalg.norm(reduced.moment_vector @ reduced.constraint_basis) < 1e-10
    assert float(np.min(np.linalg.eigvalsh(reduced.G))) > 0.0


def test_generalized_inertia_is_congruence_invariant_on_same_span() -> None:
    M = np.diag([-2.0, -0.5, 1.0, 3.0])
    G = np.diag([1.0, 2.0, 3.0, 4.0])
    S = np.array(
        [
            [1.0, 0.2, 0.0, 0.0],
            [0.0, 1.0, 0.1, 0.0],
            [0.0, 0.0, 1.0, 0.3],
            [0.1, 0.0, 0.0, 1.0],
        ]
    )

    original = generalized_inertia(M, G)
    transformed = generalized_inertia(S.T @ M @ S, S.T @ G @ S)

    assert original.nu_minus == transformed.nu_minus == 2
    assert original.nu_plus == transformed.nu_plus == 2
    assert original.nu_zero == transformed.nu_zero == 0


def test_phi_probe_is_t1_diagnostic_and_cannot_promote_weil_or_rh() -> None:
    probe = WeilSpectralInertiaProbe(
        SpectralProbeConfig(
            tau=2.0,
            p_cutoff=100,
            k_basis_dim=3,
            n_quad=1024,
            t_bound=40.0,
        )
    )

    phi = (1.0 + math.sqrt(5.0)) / 2.0
    receipt = probe.run_scale_probe({"uniform": 1.0, "phi": phi})

    assert receipt["authority"] == "T1_NUMERICAL_DIAGNOSTIC"
    assert receipt["phi_nonresonant_positivity_hypothesis"] in {
        "NOT_SUPPORTED",
        "REFUTED_AS_CLOSURE_MECHANISM_ON_TESTED_FINITE_SECTIONS",
    }
    assert receipt["global_weil_positivity_proven"] is False
    assert receipt["rh_proven"] is False
    assert set(receipt["results"]) == {"uniform", "phi"}


def test_liouville_control_is_explicitly_truncated_not_claimed_exact() -> None:
    control = truncated_liouville_control(terms=4)

    assert control["label"] == "TRUNCATED_LIOUVILLE_APPROXIMATION"
    assert control["is_exact_liouville_number"] is False
    assert 0.0 < control["value"] < 1.0


def test_scale_controls_do_not_label_finite_decimal_as_liouville_number() -> None:
    controls = build_scale_controls()

    assert set(controls) == {"uniform", "phi", "sqrt2", "sqrt3", "e", "pi", "liouville_trunc4"}
    assert controls["phi"] == (1.0 + math.sqrt(5.0)) / 2.0
    assert controls["liouville_trunc4"] == truncated_liouville_control(4)["value"]


def test_convergence_matrix_is_t1_and_makes_no_liminf_claim() -> None:
    configs = {
        "coarse": SpectralProbeConfig(
            tau=2.0,
            p_cutoff=50,
            k_basis_dim=3,
            n_quad=512,
            t_bound=30.0,
        ),
        "refined_quad": SpectralProbeConfig(
            tau=2.0,
            p_cutoff=50,
            k_basis_dim=3,
            n_quad=1024,
            t_bound=30.0,
        ),
    }
    result = run_convergence_matrix(configs, scale_factor=(1.0 + math.sqrt(5.0)) / 2.0)

    assert result["authority"] == "T1_NUMERICAL_DIAGNOSTIC"
    assert result["liminf_proven"] is False
    assert set(result["cases"]) == {"coarse", "refined_quad"}
    assert all(case["rh_proven"] is False for case in result["cases"].values())


def test_reference_fixture_requires_integer_inertia_and_lambda_interval_match() -> None:
    observed = {
        "authority": "T1_NUMERICAL_DIAGNOSTIC",
        "global_weil_positivity_proven": False,
        "rh_proven": False,
        "results": {
            "uniform": {"nu_minus": 1, "lambda_min": -2.0},
            "phi": {"nu_minus": 3, "lambda_min": -1.25},
        },
    }
    fixture = {
        "schema_version": "1.0.0",
        "authority": "T1_NUMERICAL_DIAGNOSTIC",
        "expected": {
            "uniform": {"nu_minus": 1, "lambda_min_interval": [-2.0001, -1.9999]},
            "phi": {"nu_minus": 3, "lambda_min_interval": [-1.2501, -1.2499]},
        },
    }

    verdict = verify_reference_fixture(observed, fixture)
    assert verdict["reproduced"] is True
    assert verdict["authority"] == "T1_NUMERICAL_DIAGNOSTIC"
    assert verdict["global_weil_positivity_proven"] is False
    assert verdict["rh_proven"] is False

    fixture["expected"]["phi"]["nu_minus"] = 2
    mismatch = verify_reference_fixture(observed, fixture)
    assert mismatch["reproduced"] is False
    assert "phi:NU_MINUS_MISMATCH" in mismatch["errors"]


def test_finite_cutoff_weil_symbol_is_levy_exponent_plus_adverse_scalar_shift() -> None:
    probe = WeilSpectralInertiaProbe(
        SpectralProbeConfig(
            tau=2.0,
            p_cutoff=100,
            k_basis_dim=3,
            n_quad=2048,
            t_bound=50.0,
        )
    )

    receipt = run_levy_gap_probe(probe, scale_factor=1.0)

    assert receipt["authority"] == "T1_NUMERICAL_DIAGNOSTIC"
    assert receipt["finite_cutoff_standard_levy_measure"] is True
    assert receipt["full_symbol_is_standard_levy_exponent"] is False
    assert receipt["infinite_prime_measure_standard_levy_limit"] is False
    assert abs(receipt["normalized_exponent_at_zero"]) < 1e-12
    assert receipt["normalized_exponent_grid_min"] >= -1e-10
    assert receipt["spectral_offset"] < 0.0
    assert abs(receipt["adverse_shift_magnitude"] + receipt["spectral_offset"]) < 1e-12
    assert receipt["matrix_decomposition_max_abs_error"] < 1e-9
    assert receipt["lambda_shift_identity_abs_error"] < 1e-9
    assert abs(
        receipt["weil_lambda_min"]
        - (receipt["levy_gap_lambda_min"] + receipt["spectral_offset"])
    ) < 1e-9
    assert receipt["uniform_gap_closed"] is False
    assert receipt["global_weil_positivity_proven"] is False
    assert receipt["rh_proven"] is False
