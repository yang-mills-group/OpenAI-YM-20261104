# Verifying the Wilson Yang–Mills comparators

Each comparator checks one theorem. Existence uses [its own construction](lean/Comparators/Existence/Solution.lean). Matching proves the correlation and ordinary OPE estimates on the same selected Wilson hierarchy. Its public statement also requires the specified Wilson lattice family, ordering of the raw coordinates and construction data. An alternative proof must supply these data. [Matching statement](lean/YangMills/PerturbativeMatching.lean) · [Lattice requirements](lean/YangMills/PerturbativeMatching/NativeLattice.lean)

## Tools and inputs

Use Linux with working Landlock support. The release uses the following tool versions. The comparator checkout pins the compatible exporter in its Lake manifest.

| Tool | Version or revision |
|---|---|
| Lean and Lake | [Lean 4.32.0](https://github.com/leanprover/lean4/releases/tag/v4.32.0) |
| Mathlib | [`81a5d257c8e410db227a6665ed08f64fea08e997`](https://github.com/leanprover-community/mathlib4/tree/81a5d257c8e410db227a6665ed08f64fea08e997) |
| Comparator | [`07bc4ea40f2266dcb861820a2ec1fa3244ed307f`](https://github.com/leanprover/comparator/tree/07bc4ea40f2266dcb861820a2ec1fa3244ed307f) |
| lean4export | [`4e7915201d3f9f04470d9eae002fa695f7cdc589`](https://github.com/leanprover/lean4export/tree/4e7915201d3f9f04470d9eae002fa695f7cdc589) |
| Landrun | [`5ed4a3db3a4ad930d577215c6b9abaa19df7f99f`](https://github.com/Zouuup/landrun/tree/5ed4a3db3a4ad930d577215c6b9abaa19df7f99f) |

The following SHA-256 values identify the Linux x86-64 executables used for the release checks.

```text
e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550  lean
60330ab6f07dce20f3fa9ebb08e8b984ea9549eac172afeb15d9d2227060e2b3  lake
4ffd95f2708428ad712c24d8afcb9804d91b8cc4d49edbd5d61c3d0ecb93be42  comparator
e57369980b0b81228580ce08066fb9bd738e717e002673a143f4956d217266b0  lean4export
66e1d7cc2fb769faded1763c2d44472361eeabefb26a6d5867a6b1d18dd5383c  landrun
```

Install the tools outside the submitted project and put the trusted `lake`, `lean`, `comparator`, `lean4export`, `landrun` and `git` executables on `PATH`. Use [lean-toolchain](lean/lean-toolchain) and the existing [dependency lock](lean/lake-manifest.json). Prepare the pinned external packages before restricting network access. The Mathlib cache can be installed with `lake exe cache get` from a trusted checkout.

Check the archive SHA-256 against the separately published release record. From the extracted distribution, `sha256sum -c SOURCES.sha256` checks the individual files. The challenge, its transitive imports, the Lake configuration and the verifier tools must come from sources the verifier trusts independently of a submitted proof. In particular, protect the reference build from writes by the submitted solution.

## Linux memory maps

Lean memory-maps compiled modules as it loads them. A single Matching compiler process can exhaust the Linux default of 65,530 mappings even when RAM is available. Check the limit on the Linux host before starting. [Linux kernel documentation](https://docs.kernel.org/admin-guide/sysctl/vm.html#max-map-count)

```sh
sysctl -n vm.max_map_count
```

The standalone verifier uses 262,144 mappings per process. On a host with a lower limit, an administrator can raise it to this value for the current boot. For a container, configure the underlying Linux host.

```sh
sudo sysctl -w vm.max_map_count=262144
```

If the host limit is fixed, build Lean with the CMake option `-DMMAP=OFF`. On glibc systems it may also be necessary to set `GLIBC_TUNABLES=glibc.malloc.mmap_max=0:glibc.malloc.arena_max=1` when running Lean or Lake. A custom Lean build has its own executable hashes. To reproduce the release check with the pinned binaries above, use a host with the higher map limit. [Lean 4.32.0 CMake option](https://github.com/leanprover/lean4/blob/8c9756b28d64dab099da31a4c09229a9e6a2ef35/src/CMakeLists.txt#L107)

## Run a stock comparator

Use a fresh verification environment under an unprivileged account for each submission. Compile the trusted reference first. The stock command builds and exports the challenge before building and exporting the solution. Keep the tools, reference inputs and trusted dependency cache outside the solution's write permissions. A previous run of untrusted project code in that verification environment can invalidate the reference. Upstream also describes how to use a fully prebuilt project obtained in a separate environment. [Comparator trust assumptions](https://github.com/leanprover/comparator/blob/07bc4ea40f2266dcb861820a2ec1fa3244ed307f/README.md#comparator)

With a systemd user manager, run the following from a fresh extraction. Choose `Existence` for the first verifier and `Matching` for the second. The socket restriction is important on Linux kernels older than 7.1. A platform with a different sandbox launcher must enforce the same restrictions around the entire command.

```sh
cd lean
selector=Existence
test "$(id -u)" -ne 0 || exit 1
systemd-run --user --wait --pipe --collect \
  --property=NoNewPrivileges=yes \
  --property='RestrictAddressFamilies=~AF_UNIX AF_INET AF_INET6' \
  --working-directory="$PWD" --setenv="PATH=$PATH" \
  /usr/bin/env -i "HOME=$HOME" "PATH=$PATH" LC_ALL=C.UTF-8 \
    "$(command -v lake)" env "$(command -v comparator)" "ComparatorChallenges/$selector.json"
```

Check that the verifier runs with a nonzero effective user ID, no effective capabilities, and denied creation of Unix sockets. With the real Landrun binary and the comparator's filesystem policy, use disposable files to check that an ordinary write and a read-only open with `O_TRUNC` are both denied outside the build directory, while a permitted write succeeds inside it. Both checks matter on older Linux kernels. Preserve the executable hashes, the challenge and solution identifiers, the full log and the exit status for each run.

The selectors permit exactly `propext`, `Quot.sound` and `Classical.choice`. They compare the exported theorem with the challenge and replay the proof in Lean's default kernel. For each selector the success log ends with `Lean default kernel accepts the solution` and `Your solution is okay!`, with exit status zero. A default `lake build` compiles the two challenges and the two solutions. The two stock comparator commands perform the proof comparisons. [Existence selector](lean/ComparatorChallenges/Existence.json) · [Matching selector](lean/ComparatorChallenges/Matching.json)

## Sources and receipts

The companion verification record identifies the archive by SHA-256 and gives the per-selector verdict, elapsed time and available resource measurements. Cache use and parallelism affect those measurements. The root [NOTICE](NOTICE) identifies adapted sources and their original authors. See [third-party dependencies](THIRD_PARTY.md), the [project license](LICENSE) and the [bundled license texts](third_party_licenses).
