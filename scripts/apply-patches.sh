#!/bin/sh
# Apply the two compatibility patches that the vendored project `quasi-riemann-improved`
# requires for its dependencies `rellich-kondrachov` and `PrimeNumberTheoremAnd`
# (see vendor/quasi-riemann-improved/README.md and lean/upstream-config/applied-physical-patches.json).
# Run once after Lake has fetched the packages; running it again changes nothing.
set -eu
cd "$(dirname "$0")/.."
PATCHES="$PWD/vendor/quasi-riemann-improved/lean/upstream-config/patches"
apply_once() {
  pkg=".lake/packages/$1"
  patch="$PATCHES/$2"
  if [ ! -d "$pkg/.git" ]; then
    echo "$pkg is missing: let Lake fetch the packages first (lake env lean --version)" >&2
    exit 1
  fi
  if git -C "$pkg" apply --reverse --check "$patch" 2>/dev/null; then
    echo "$1: patch already applied"
  else
    git -C "$pkg" apply --whitespace=nowarn "$patch"
    echo "$1: patch applied"
  fi
}
apply_once rellich-kondrachov rellich-kondrachov-lean4341.patch
apply_once PrimeNumberTheoremAnd PrimeNumberTheoremAnd-lean4341.patch
