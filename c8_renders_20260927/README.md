# Seven views of the c = 8 Haagerup construction

Seven renders for talks and outreach, each with a story tied to the
manuscript `hi_cft_c8_proof.tex`. The stories are in [STORIES.md](STORIES.md)
and in the gallery page `gallery/index.html`. Both are generated from
`scripts/stories.py`, which is the single source for the text.

| # | Image (`out/`) | What it shows | Data source |
|---|---|---|---|
| 1 | `r1_fusion_graph.png` | Fusion graph of ρ in H₃; radii = quantum dimensions | fusion rules, d = (3+√13)/2 |
| 2 | `r2_e8_248.png` | E₈ roots, coloured by the Z₃ cosets of E₆⊕A₂; U's current roots ringed | Gram matrix of Appendix A |
| 3 | `r3_seed_field.png` | The defining field u as three interfering waves; phasors 1, ζ, ζ̄ | eq. (83), positive transport |
| 4 | `r4_five_squared.png` | (ℤ/13)² torus; isotropic lines k = −5j (realized) and k = 5j | Section G.1 |
| 5 | `r5_thirteen_hours.png` | Twists of the 12 sectors on a 13-hour clock; Gauss sum walk to √13 | modular data, Section 5 |
| 6 | `r6_correlator_landscape.png` | log\|G₀(x)\| and arg G₀(x) over the complex cross-ratio plane | eq. (28) |
| 7 | `r7_two_cities.png` | Virasoro-primary counts at (h, h̄) for the diagonal and E₈ theories | `c8_physics_20260927/data` |

`out/` holds 2400×1350 PNGs. `out/web/` holds JPEG copies for the web.

## Regenerate

Run each command from the repository root, one at a time. The shared lock
in `~/.local/bin/research-safe-run` enforces this.

```sh
# 2D renders (NumPy light accumulation)
~/.local/bin/research-safe-run --limit-mib 3072 -- python c8_renders_20260927/scripts/r2_e8.py
~/.local/bin/research-safe-run --limit-mib 3072 -- python c8_renders_20260927/scripts/r3_seed.py
~/.local/bin/research-safe-run --limit-mib 3072 -- python c8_renders_20260927/scripts/r5_clock.py

# Blender scenes: render to work/*.npy, then post-process
~/.local/bin/research-safe-run --limit-mib 6144 -- blender -b -noaudio -t 2 --python c8_renders_20260927/scripts/r1_scene.py
~/.local/bin/research-safe-run --limit-mib 3072 -- python c8_renders_20260927/scripts/r1_post.py
# ... likewise r4, r6, r7

# gallery page and STORIES.md
python c8_renders_20260927/scripts/build_gallery.py
```

For a quick preview, set `R_SCALE=0.33 R_SAMPLES=40` in the environment of
a Blender command.

## Resource notes

Every run used the permanent launcher limits: two CPUs, one job at a time,
and the host-memory reserve. The measured peak group RSS was at most
2.8 GiB for the Blender scenes and at most 1.2 GiB for the NumPy
scripts. OpenImageDenoise needs a 6 GiB address cap at full resolution;
4 GiB failed with an address-space error while RSS was only 0.6 GiB.
Render 6's large height field leaves too little address space for the
denoiser even at 6 GiB, so that scene renders with 320 samples, a tight
adaptive threshold and no denoiser. It shows no visible noise.

Blender 5.2's bundled OCIO config does not load with the system
OpenColorIO 2.4, so Blender's colour management is off. Scenes are
rendered as linear EXR and tone-mapped in `scripts/look.py` (ACES fit),
so the 3D and 2D images share one look.
