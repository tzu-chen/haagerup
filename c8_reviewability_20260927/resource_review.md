# Resource review: human verification and Lean assessment

The permanent shared-desktop policy applies. Root alone runs computations,
serially through `hi_cft_safe_run.py`. The expired September 15 exception is
unused. Each run checks host MemAvailable and cgroup limits, enforces at
most two threads and CPUs, keeps at least 32 GiB host MemAvailable, and
retains the 8 GiB process-group RSS watchdog. No worker pool is used.

| Work | Live-memory estimate | Hard address cap | Time boundary |
|---|---|---|---|
| Independent small lattice/stress checker | <0.12 GiB: three JSON sources <1 MiB each; fewer than 2,000 sparse terms per field; 8x8 Fraction inverse; pairings grouped by momentum; no mode caches | 512 MiB | 120 seconds |
| Finite Gate4/5 witness reader | <192 MiB expected; 384 MiB internal RSS refusal; SQLite caches total <=8 MiB, decoded records <=8 MiB, <=5,000 terms/vector; one target and one source vector, no vector cache | 1 GiB | Internal 360 seconds |
| Potts/PF13 membership witness export | <0.75 GiB: original grade<=3 calculation <0.12 GiB, plus raw sources, tracked expressions and JSON; S2<=120, S3<=58, tracking<=58, persistent sparse terms<=250,000, <=4,096-bit coefficients, bounded mode caches | 2 GiB | Internal 560 seconds; outer600 seconds |
| Independent membership-coordinate verifier | <0.3 GiB for the actual exported43,462-term packet; JSON<=30MiB and totalstatecap250,000; parsed coordinates plus one accumulated residual | 1 GiB | Internal180 seconds |
| Current80 cyclicity export | <0.3 GiB: 86 ambient states, 80 complement/cyclic rows, 30 sparse86x86 matrices; <=100,000 matrixentries and <=250,000 savedentries; only grade<=2 mode engine with bounded caches | 2 GiB | Internal120seconds; outer180seconds |
| Independent current80 matrix check | <0.3 GiB: JSON<=30MiB, 86 coordinates, 30 sparse86x86 matrices, 160 rows, <=250,000 total entries; exact Fraction operations without the mode engine | 1 GiB | Internal120seconds; outer180seconds |
| Minimal-generation witness export/check | <0.25 GiB estimated: <=120 raw/normalized rows and tracked expansions, <=100,000 persistent sparse entries, <=2,048-bit coefficients, JSON<=30MiB; retained tracking<=120, rejected-candidate scratch<=121; no higher-grade engine | Export2GiB; independentcheck1GiB | Internal180seconds; RSS512MiB refusal |
| Portable Gate4 export/check | Export<64MiB; check<192MiB with384MiB refusal; 33 records, eachdecoded<=8MiB/5,000terms; gzipJSONL<=256MiB uncompressed; one residual and one source vector; no original database in checkmode | 1 GiB | Internal360seconds |
| TeX companion build | <0.3 GiB: text/tables and ordinary fonts, no shell escape | 1.5 GiB | 120 seconds per pass |
| Selected page rendering | <0.3 GiB per page at 90 dpi, serial child processes | 1 GiB | 30 seconds per page |
| Static audit and reviewer archive | <0.25 GiB: bounded JSON/TSV inputs, streaming 1MiB hashing and ZIP members; no original large databases, ZIP payload capped at 40MiB | 1 GiB | 120 seconds |
| Fresh-extraction portable replay | <0.3 GiB: preparation streams <=40MiB ZIP and hashes; each checker then launched separately and directly through the permanent launcher using the bounds above | 1 GiB (small check512MiB) | Preparation/validation120seconds; each checker its existing internal bound |

Additional certificate exporters must be reviewed here before execution.
Text reading, source searches, and editing by subagents do not launch
numerical jobs. Source files and frozen certificates remain unchanged.

Observed process peak RSS: readable-input check about 24MiB; finite
Gate4/5 check 39,512KiB; membership export 84,292KiB and independent
coordinate check 52,788KiB; minimal-generation export 44,400KiB and
independent check 35,900KiB; current80 export 36,996KiB and independent
matrix check 25,336KiB; portable Gate4 check 35,380KiB. The largest
sampled process-group RSS was about 0.082GiB. Every run passed with the
permanent launcher and with host MemAvailable above 52GiB at launch.
