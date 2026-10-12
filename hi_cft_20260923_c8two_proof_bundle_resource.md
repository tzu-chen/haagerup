# Final provenance-ledger resource review

This root-only serial job reads and hashes completed certificate graphs and
human-readable proof notes. It performs no lattice mode, matrix calculation,
or native solve. Source files are streamed in 1 MiB chunks; certificate JSON
files are capped at 32 MiB each. The five terminal summaries and eighteen
earlier exact-input records together occupy only a few MiB. The latter use
explicitly handled historical hash encodings and retain their original scopes.
The expected RSS is below 0.1 GiB; the script checks 256 MiB at completion.
Use the normal safe launcher at 1024 MiB address space, internal 180-second
alarm and outer 200-second foreground timeout. The ordinary group watchdog,
32 GiB host reserve, shared numerical lock, two threads and CPU affinity apply.

Run only after the final proof notes are complete and frozen. The ledger
authenticates provenance and terminal statuses; it explicitly does not claim
proof-assistant checking of the analytical and categorical arguments.
