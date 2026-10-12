# Global resource guard migration

Run current jobs from their project directory with
`~/.local/bin/research-safe-run -- COMMAND ...`. The project-local
`hi_cft_safe_run.py` only forwards old calls and helper imports to that guard.
The installed global guard is required; there is no local fallback policy.

The primary lock is `/tmp/research_numerical.lock`. The old
`/tmp/haagerup_numerical.lock` remains an alias to the same inode. Neither
lock was unlinked or replaced. The 6 GiB address cap, 8 GiB group watchdog,
32 GiB host reserve, and two-CPU/thread maximum are unchanged.

The `.txt` files here preserve the exact pre-migration launcher-related
sources. They are provenance artifacts, not runnable fallback launchers.
`migration.json` records their hashes, the global guard and shim hashes,
and the validation performed for this change. Existing research records,
checkpoint hashes and released bundles were not rewritten.

Strict old checkpoint/source-graph validation can now report a legitimate
hash mismatch for the guard or another modified launcher-related source.
A future continuation must explicitly verify historical bytes against
these archives, validate current scientific sources, and separately record
the current global guard and launcher hashes. Do not silently rehash old
records or skip source checks. New bundles containing the shim require the
global guard installation.

Regression checks run without research workloads:

```sh
python -m unittest discover -s tests -p test_resource_guard_migration.py -v
```

Eight tests passed, covering forwarding, arguments and working directory,
global helper delegation, parent-process acceptance/refusal, historical
source preservation, external guard hashing, and expired-window refusal.
Python and shell syntax checks passed. The guarded runtime probe correctly
refused because another job held the shared lock; no child ran. Julia's
parent check received static review without launching Julia.
