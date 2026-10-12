#!/usr/bin/env python3
"""Plot the proved critical-Ising calibration formulas; no spectral computation.

Root must inspect this script and admit it through the canonical guard.
Suggested command, run from the textbook directory:
  ~/.local/bin/research-safe-run --limit-mib 1024 --memory-mib 512 \
      --threads 1 -- timeout 90s python3 plot_ising_calibration.py

Unmeasured, conservative peak estimate:
  Python/NumPy/Matplotlib imports and shared mappings: 160 MiB resident;
  font discovery, caches, vector rendering, output and allocator headroom:
  80 MiB; explicit data and a possible Agg canvas: below 4 MiB.
Expected resident peak is therefore below 256 MiB. A 512 MiB whole-job
reservation also covers charged file cache; a 1024 MiB address-space cap
allows library mappings. The canonical guard still checks host/cgroup
availability and enforces both limits. These are estimates, not measurements.

There are 512 smooth samples and 15 even-size samples. No explicitly
constructed numerical array has more than 1024 scalar entries, including
the 512-by-2 plotted coordinate arrays. Matplotlib may allocate its own
font/rendering buffers, included in the estimate above. Data are generated
with scalar math and small Python lists; there is no eigensolver or fit.
One foreground process, one compute thread, no workers or external programs.
The audit hook disables subprocess creation, including optional fontconfig
queries; Matplotlib falls back to its in-process font-directory discovery.
"""

from pathlib import Path
import hashlib
import json
import math
import os
import resource
import sys
import time


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def forbid_children(event, args):
    """Keep optional font discovery and all rendering in this process."""
    if event in {
        "subprocess.Popen",
        "os.fork",
        "os.forkpty",
        "os.posix_spawn",
        "os.system",
        "os.exec",
    }:
        # Fontconfig discovery catches OSError and uses directory scanning.
        raise FileNotFoundError("External processes are disabled in this plot.")


def calibration(t):
    """Return the two dimensions and velocity ratio at t=1/L**2."""
    if t == 0.0:
        return 1.0, 1.0, 1.0
    z = 0.5 * math.pi * math.sqrt(t)
    sinc = math.sin(z) / z
    cos_squared = math.cos(z) ** 2
    return sinc, 1.0 / cos_squared, sinc * cos_squared


def main():
    if not os.environ.get("RESEARCH_SAFE_RUN_ACTIVE"):
        raise SystemExit(
            "Use the canonical research-safe-run; no unguarded computation."
        )
    if hasattr(os, "sched_getaffinity") and len(os.sched_getaffinity(0)) != 1:
        raise SystemExit("Admit this small plot with --threads 1 (one CPU).")

    started = time.monotonic()
    root = Path(__file__).resolve().parent
    if Path.cwd().resolve() != root:
        raise SystemExit("Run from the haagerup_cft_textbook directory.")

    config_dir = root / "build" / "tmp" / "matplotlib_ising"
    config_dir.mkdir(parents=True, exist_ok=True)
    os.environ["MPLCONFIGDIR"] = str(config_dir)
    os.environ["MPLBACKEND"] = "Agg"
    for name in (
        "OMP_NUM_THREADS",
        "OPENBLAS_NUM_THREADS",
        "MKL_NUM_THREADS",
        "NUMEXPR_NUM_THREADS",
        "VECLIB_MAXIMUM_THREADS",
        "BLIS_NUM_THREADS",
    ):
        os.environ[name] = "1"
    sys.addaudithook(forbid_children)

    # All non-stdlib imports occur after the guard and resource checks.
    import matplotlib

    matplotlib.use("Agg", force=True)
    from matplotlib import pyplot as plt

    plt.rcParams.update(
        {
            "text.usetex": False,
            "font.family": "DejaVu Sans",
            "font.size": 9,
            "axes.labelsize": 10,
            "axes.titlesize": 10,
            "legend.fontsize": 8,
            "xtick.labelsize": 8,
            "ytick.labelsize": 8,
            "pdf.fonttype": 42,
            "svg.fonttype": "path",
            "svg.hashsalt": "haagerup-textbook-ising-calibration",
            "savefig.dpi": 150,
        }
    )

    sample_count = 512
    t_max = 1.0 / 16.0
    smooth_t = [t_max * i / (sample_count - 1) for i in range(sample_count)]
    smooth = [calibration(t) for t in smooth_t]
    sizes = list(range(4, 33, 2))
    discrete_t = [1.0 / (length * length) for length in sizes]
    discrete = [calibration(t) for t in discrete_t]

    blue = "#0072B2"
    vermilion = "#D55E00"
    green = "#009E73"
    reference = "#666666"
    fig, axes = plt.subplots(
        1, 2, figsize=(7.2, 3.0), constrained_layout=True
    )
    for ax in axes:
        ax.set_xlim(-0.001, 0.064)
        ax.set_xticks([0.0, 0.02, 0.04, 0.06])
        ax.set_xlabel(r"$1/L^2$")
        ax.axhline(1.0, color=reference, linewidth=1.0, linestyle="--")
        ax.grid(axis="y", color="#DEDEDE", linewidth=0.6)
        ax.set_axisbelow(True)
        ax.spines["top"].set_visible(False)
        ax.spines["right"].set_visible(False)
        ax.tick_params(direction="out")

    left, right = axes
    left.plot(
        smooth_t, [row[0] for row in smooth], color=blue, linewidth=1.7
    )
    left.plot(
        discrete_t,
        [row[0] for row in discrete],
        linestyle="none",
        marker="o",
        markersize=3.6,
        color=blue,
        label="Known velocity",
    )
    left.plot(
        smooth_t, [row[1] for row in smooth], color=vermilion, linewidth=1.7
    )
    left.plot(
        discrete_t,
        [row[1] for row in discrete],
        linestyle="none",
        marker="s",
        markersize=4.0,
        markerfacecolor="white",
        markeredgewidth=1.0,
        color=vermilion,
        label="Stress calibration",
    )
    left.set_ylim(0.96, 1.19)
    left.set_yticks([1.0, 1.05, 1.10, 1.15])
    left.set_ylabel(r"Estimated $\Delta_\epsilon$")
    left.set_title("(a) The same energy-field gap", loc="left")
    left.legend(loc="upper left", frameon=False, handlelength=1.0)

    right.plot(
        smooth_t, [row[2] for row in smooth], color=green, linewidth=1.7
    )
    right.plot(
        discrete_t,
        [row[2] for row in discrete],
        linestyle="none",
        marker="D",
        markersize=3.6,
        color=green,
    )
    right.set_ylim(0.82, 1.02)
    right.set_yticks([0.84, 0.88, 0.92, 0.96, 1.0])
    right.set_ylabel(r"Stress velocity $\widehat{v}_T/(2J)$")
    right.set_title("(b) The calibration has its own bias", loc="left")
    right.text(
        0.058, 1.004, "Continuum limit", fontsize=8,
        color=reference, ha="right", va="bottom"
    )

    figure_dir = root / "figures"
    figure_dir.mkdir(exist_ok=True)
    pdf_path = figure_dir / "ising_calibration.pdf"
    svg_path = figure_dir / "ising_calibration.svg"
    title = "Exact finite-size calibrations in the critical periodic Ising chain"
    fig.savefig(
        pdf_path,
        format="pdf",
        metadata={
            "Title": title,
            "Creator": "Haagerup CFT textbook: plot_ising_calibration.py",
            "CreationDate": None,
            "ModDate": None,
        },
    )
    fig.savefig(
        svg_path,
        format="svg",
        metadata={
            "Title": title,
            "Description": (
                "Exact scalar formulas; even L=4,...,32; smooth formula "
                "continuations; no eigensolver, extrapolation, or Haagerup data."
            ),
            "Date": None,
        },
    )
    plt.close(fig)

    guard = Path.home() / ".local" / "bin" / "research-safe-run"
    chapter = root / "chapters" / "l02_scaling.tex"
    provenance = {
        "scope": "Canonical critical Ising comparison; no Haagerup-chain data.",
        "hamiltonian": "H=-J sum_j(sigma_x[j] sigma_x[j+1]+sigma_z[j]); J>0",
        "conventions": "Periodic spin chain; even L>=4; spacing=1; v=2J.",
        "source": {
            "file": "chapters/l02_scaling.tex",
            "example": "ex:scaling-Ising-calibration",
            "equation_labels": [
                "eq:scaling-Ising-epsilon-v",
                "eq:scaling-Ising-stress-gap",
                "eq:scaling-Ising-epsilon-stress",
            ],
            "sha256": sha256(chapter),
        },
        "formulas": {
            "t": "1/L^2",
            "z": "(pi/2)*sqrt(t)",
            "delta_known_v": "sin(z)/z",
            "delta_stress_calibrated": "1/cos(z)^2",
            "stress_velocity_over_2J": "(sin(z)/z)*cos(z)^2",
            "t_zero": "All three quantities have continuous value 1.",
        },
        "smooth_grid": {
            "samples": sample_count,
            "t_min": 0.0,
            "t_max": t_max,
            "meaning": "Smooth continuation of exact formulas; not a fit.",
        },
        "data_columns": [
            "L", "1/L^2", "delta_known_v",
            "delta_stress_calibrated", "stress_velocity_over_2J",
        ],
        "data": [
            [length, t, *row]
            for length, t, row in zip(sizes, discrete_t, discrete)
        ],
        "execution": {
            "script_sha256": sha256(Path(__file__)),
            "guard_sha256": sha256(guard),
            "guard_unit": os.environ["RESEARCH_SAFE_RUN_ACTIVE"],
            "matplotlib_version": matplotlib.__version__,
            "config_directory": "build/tmp/matplotlib_ising",
            "smooth_samples": sample_count,
            "cpu_affinity": sorted(os.sched_getaffinity(0)),
            "max_rss_kib_linux": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            "elapsed_seconds": time.monotonic() - started,
            "estimated_peak_resident_mib": 256,
            "suggested_guard_address_space_mib": 1024,
            "suggested_guard_memory_reservation_mib": 512,
        },
        "outputs": [
            {"path": str(path.relative_to(root)), "sha256": sha256(path)}
            for path in (pdf_path, svg_path)
        ],
    }
    provenance_path = root / "editorial" / "ising_calibration_plot_provenance.json"
    provenance_path.write_text(
        json.dumps(provenance, indent=2, ensure_ascii=True) + "\n",
        encoding="utf-8",
    )
    print("Wrote figures/ising_calibration.pdf and figures/ising_calibration.svg")
    print("Provenance: editorial/ising_calibration_plot_provenance.json")
    print(
        "Peak RSS: "
        f"{provenance['execution']['max_rss_kib_linux'] / 1024:.1f} MiB; "
        f"elapsed: {provenance['execution']['elapsed_seconds']:.2f} s"
    )


if __name__ == "__main__":
    main()
