#!/usr/bin/env bash
# safe-lean — resource-bounded wrapper around `lake env lean` / `lake build`.
#
# WHY: heavy proof files (deep `interval_cases`, large `maxHeartbeats`, generated
# case-split families) can spike memory and run for minutes; this Lake version has
# no `-j`/`--jobs` flag, so `lake build <target>` schedules as many files
# concurrently as it likes (observed: up to nproc). Unbounded, a spike trips the
# kernel OOM-killer, which kills *arbitrary* processes on the box, not just this
# one. This wrapper runs the invocation inside a transient systemd scope with a
# hard MemoryMax and a wall-clock timeout, so a runaway is killed *as its own
# scope*. The box, your session, and sibling builds survive.
#
# Ported from ai-math/lean4/scripts/safe-lean.sh (2026-07-23) for this repo's
# different layout (Propositio/<Area>/... instead of a flat lean4/ directory) —
# the only change is how a `.lean` path is mapped to a module name; the resource
# safety logic is unchanged.
#
# USAGE:
#   scripts/safe-lean.sh Propositio/NumberTheory/Collatz/File.lean   # typecheck, bounded
#   scripts/safe-lean.sh --build TargetName                          # == lake build TargetName, bounded
#   scripts/safe-lean.sh --print-axioms Thm [File.lean ...]          # axiom names, CSV
#   MEM=4G TIMEOUT=1800 scripts/safe-lean.sh BigFile.lean             # override caps
#
# --print-axioms <ThmName> [<file_or_module> ...]
#   Evaluates `#print axioms <ThmName>` in a temp .lean file that imports the
#   modules implied by the given files (a `Propositio/Foo/Bar.lean` path is
#   imported as module `Propositio.Foo.Bar`), and prints the resulting axiom
#   names comma-separated to stdout. Exit 0 on a successful extraction (a
#   theorem that depends on NO axioms prints an empty line — callers that need
#   fail-closed behaviour must treat an empty list as "could not determine").
#   Exit nonzero on ANY Lean/IO error. REQUIRES THE BUILD BOX: it invokes
#   `lake env lean`, so it needs the mathlib olean cache present
#   (`.lake/packages` symlinked from an ai-math checkout, or `lake exe cache get`).
#
# EXIT CODES: 124 = timeout, 137 = killed (OOM/scope MemoryMax), else lean's own.
#
# Requires: elan on PATH, systemd --user (falls back to ulimit if absent).
set -euo pipefail

export PATH="$HOME/.elan/bin:$PATH"

MEM="${MEM:-6G}"          # hard memory ceiling for this invocation
SWAP="${SWAP:-2G}"        # swap allowance on top of MEM
TIMEOUT="${TIMEOUT:-900}" # wall-clock seconds before SIGTERM

# --- --print-axioms: live #print axioms extractor (build box only) ---------
if [[ "${1:-}" == "--print-axioms" ]]; then
  shift
  thm="${1:?--print-axioms requires <ThmName>}"; shift || true
  # Remaining args name the modules to import so the theorem is in scope.
  # A `.lean` path is mapped to a module name by just dropping the extension
  # and turning `/` into `.` (paths here are already repo-root-relative,
  # e.g. `Propositio/NumberTheory/Collatz/File.lean` -> `Propositio.NumberTheory.Collatz.File`).
  imports=(); modnames=()
  for a in "$@"; do
    if [[ "$a" == *.lean ]]; then
      m="${a%.lean}"; m="${m//\//.}"
    else
      m="$a"
    fi
    [ -n "$m" ] && { imports+=("import $m"); modnames+=("$m"); }
  done
  if [ ${#modnames[@]} -gt 0 ]; then
    if command -v systemd-run >/dev/null 2>&1 && systemctl --user >/dev/null 2>&1; then
      systemd-run --user --scope --quiet \
        -p MemoryMax="$MEM" -p MemorySwapMax="$SWAP" \
        timeout --signal=TERM "$TIMEOUT" lake build "${modnames[@]}" >/dev/null 2>&1 || true
    else
      kib=$(( ${MEM%G} * 1024 * 1024 ))
      ( ulimit -v "$kib"; timeout --signal=TERM "$TIMEOUT" lake build "${modnames[@]}" ) >/dev/null 2>&1 || true
    fi
  fi
  tmp="$(mktemp --suffix=.lean)" || { echo "safe-lean: mktemp failed" >&2; exit 1; }
  trap 'rm -f "$tmp"' EXIT
  {
    for i in "${imports[@]:-}"; do [ -n "$i" ] && echo "$i"; done
    echo "#print axioms $thm"
  } > "$tmp"

  axcmd=(lake env lean "$tmp")
  if command -v systemd-run >/dev/null 2>&1 && systemctl --user >/dev/null 2>&1; then
    out="$(systemd-run --user --scope --quiet \
            -p MemoryMax="$MEM" -p MemorySwapMax="$SWAP" \
            timeout --signal=TERM "$TIMEOUT" "${axcmd[@]}" 2>&1)" \
      || { echo "safe-lean --print-axioms: lean invocation failed for '$thm'" >&2; exit 1; }
  else
    kib=$(( ${MEM%G} * 1024 * 1024 ))
    out="$( ulimit -v "$kib"; timeout --signal=TERM "$TIMEOUT" "${axcmd[@]}" 2>&1 )" \
      || { echo "safe-lean --print-axioms: lean invocation failed for '$thm'" >&2; exit 1; }
  fi

  inner="$(printf '%s' "$out" | tr '\n' ' ' | grep -oE '\[[^]]*\]' | head -1 | tr -d '[]' | tr -s ' ' || true)"
  printf '%s\n' "$inner"
  exit 0
fi

mode="env"
if [[ "${1:-}" == "--build" ]]; then mode="build"; shift; fi

if [[ "$mode" == "build" ]]; then
  cmd=(lake build "$@")
else
  cmd=(lake env lean "$@")
fi

run_bounded() {
  if command -v systemd-run >/dev/null 2>&1 && systemctl --user >/dev/null 2>&1; then
    exec systemd-run --user --scope --quiet \
      -p MemoryMax="$MEM" -p MemorySwapMax="$SWAP" \
      timeout --signal=TERM "$TIMEOUT" "${cmd[@]}"
  else
    local kib
    kib=$(( ${MEM%G} * 1024 * 1024 ))
    ( ulimit -v "$kib"; exec timeout --signal=TERM "$TIMEOUT" "${cmd[@]}" )
  fi
}

echo "safe-lean: MEM=$MEM SWAP=$SWAP TIMEOUT=${TIMEOUT}s :: ${cmd[*]}" >&2
run_bounded
