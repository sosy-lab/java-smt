# README — Patch: build Z3 4.5.0 with `legacy` in package names

This README explains how to apply a patchfile to the Z3 `d57a2a6` (4.5.0) tree and build it so that package names include the string `legacy`.

```bash
# 1) clone and checkout the exact commit
git clone https://github.com/Z3Prover/z3.git
cd z3
git checkout d57a2a6dce9291acf9c71a561252f3e133f0c894

# 2) copy your patchfile into the repo (example: 4.5.0-legacy.patch)
# then check it applies cleanly
git apply --check 4.5.0-legacy.patch

# 3) apply the patch
git apply 4.5.0-legacy.patch

# 4) build (the classic 4.5.0 build workflow using mk_make.py)
mkdir release
python2.7 scripts/mk_make.py --prefix="$PWD/release" --java
cd build && make -j "$(nproc)" && make install
```