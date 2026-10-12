# Last H4 block: column rescaling within the existing native budget

New adapter `hi_cft_20260923_c8two_h4_normalized.py` imports the closed
`hi_cft_20260923_c8two_targeted_h4_trimmed_v2` directory into a new authenticated
directory. The118 completed identities and all reconstructed exact columns are
retained. Frozen producers, old databases, mode engine, FLINT adapter and integer
residual helper are unchanged. Only root may launch this job, serially through
the guarded launcher under3 GiB AS, the inherited1400 MiB RSS boundary,
32 GiB host reserve and at most two CPUs/threads. Use an external timeout.

The final weight(0,0) block has280 columns. Its previously reconstructed matrix
contains280-bit entries, causing the existing512 MiB native preflight to refuse
the solve. This adapter does not change that preflight or increase any limit.
Instead it tries invertible scalar changes of column basis:

1. Clear the rational coordinate denominators of one matrix column and divide
   the resulting integer coordinates by their common content.
2. Divide the column by a nonzero number-field entry of minimum coefficient
   height in that column.

A trial is used only if it strictly decreases the maximum coefficient height
in that column. Every changed entry is checked against the original entry
times its recorded nonzero scalar. Trials whose common denominator or scalar
height exceeds4096 bits are skipped. There is no guarantee that scaling lowers
the global matrix height enough: the unchanged preflight decides after actual
normalization. If it still refuses, the artifact records the scaling outcome,
and support pruning remains the fallback.

If A'=A diag(s_j), the native solver finds d with A'd=b. The adapter converts
to original normal-word coefficients c_j=s_j d_j before calling the frozen
full sparse integer residual checker. Thus the saved relation format and
actual original normal-word coefficients are unchanged. The conversion retains
the4096-bit relation bound. Existing successful records need no recomputation.

The scaling pass holds only one raw and at most two trial280-entry columns in
addition to the existing matrix. It adds under a few MiB even at the4096-bit
trial bound; it does not duplicate the entire matrix. Expected normalization
time is several seconds, unmeasured before launch. The saved column cache avoids
new lattice-mode work for the final block. The inherited pre-native trimming
still discards the128 MiB raw-vector cache,192 MiB whole-action cache and64 MiB
integer-column cache before FLINT. Matrix/RHS/targets remain live exactly as in
the reviewed trim adapter. Conservative expected peak is0.8–1.3 GiB RSS if the
native preflight passes; the hard3 GiB AS ceiling remains authoritative.

Copying uses1 MiB streaming buffers, source file hashes, a temporary directory
and atomic rename. Each source file is at most512 MiB, aggregate at most4 GiB;
this is disk storage, not simultaneous RAM. The new lineage binds all copied
closed files, the complete prior trim/targeted policy and the new implementation.
Restart requires identical sources and lineage. The inner targeted main resets
its Python alarm after preparation, so the external timeout must bound the
entire copy-plus-computation process, as well as any ctypes native solve.
No live journals or WAL files
are accepted. The original118 certificates remain untouched in their source
directory; the new directory may append policy metadata and final relations.

Suggested root-only payload, with3 GiB AS and external620-second timeout:

```text
python hi_cft_20260923_c8two_h4_normalized.py --seconds 600
```

Only syntax checking has been performed by the implementing agent. No exact
column arithmetic, native solve or numerical control has been run by an agent.
