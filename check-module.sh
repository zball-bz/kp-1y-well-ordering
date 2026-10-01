#!/usr/bin/env bash
# Check one module (or the root KP1Y.lean) with autoImplicit=false; --emit writes its .olean.
# Lean binary: $KP_LEAN, else ../.tools/lean-4.33.1-linux/bin/lean if present, else `lean` on PATH (elan reads lean-toolchain).
set -eu
kp_task_root="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
if [ -n "${KP_LEAN:-}" ]; then
  kp_lean_bin="$KP_LEAN"
elif [ -x "$kp_task_root/../.tools/lean-4.33.1-linux/bin/lean" ]; then
  kp_lean_bin="$kp_task_root/../.tools/lean-4.33.1-linux/bin/lean"
else
  kp_lean_bin="$(command -v lean)"
fi
export LEAN_PATH="$kp_task_root/third_party/YesMetaZFC/.lake/build/lib/lean:$kp_task_root/.lake/build/lib/lean"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
cd "$kp_task_root"
kp_module_path="$1"
case "$kp_module_path" in KP1Y.lean|KP1Y/*.lean) ;; *) exit 2;; esac
if [ "${2-}" = '--emit' ]; then
  kp_olean_path="$kp_task_root/.lake/build/lib/lean/${kp_module_path%.lean}.olean"
  mkdir -p "$(dirname "$kp_olean_path")"
  exec "$kp_lean_bin" -DautoImplicit=false "$kp_module_path" -o "$kp_olean_path"
else
  exec "$kp_lean_bin" -DautoImplicit=false "$kp_module_path"
fi
