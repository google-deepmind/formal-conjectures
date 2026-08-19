#!/usr/bin/env bash
set -euo pipefail

# Landrun's current CLI needs an explicit outer `--` before the sandboxed
# command. Comparator constructs Landrun's options itself but does not add that
# delimiter. Without it, Landrun consumes lean4export's own `--` separator.
landrun_binary=${PALOMAR_LANDRUN_BIN:?PALOMAR_LANDRUN_BIN must name the pinned Landrun binary}
landrun_options=()

# Landrun's --unrestricted-* flags each switch off a whole class of Landlock
# restriction. The pinned Comparator never asks for one, and passing them
# through would let a later Comparator disable the sandbox without anyone
# noticing, so refuse them and say which one arrived. Widening the sandbox is
# a decision for this repository, not one a dependency bump makes on its own.
# Landrun accepts one or two leading dashes for every flag, so reject both.
while [ "$#" -gt 0 ]; do
  case "$1" in
    -unrestricted-*|--unrestricted-*)
      echo "error: Landrun option $1 switches off part of the sandbox" >&2
      echo "Comparator must not request it; refusing to run $landrun_binary" >&2
      exit 2
      ;;
    --best-effort|-ldd|--ldd|-add-exec|--add-exec|--ignore-missing|--log-disable-originating|--log-enable-subprocesses|--log-disable-subdomains)
      landrun_options+=("$1")
      shift
      ;;
    --log-level|--ro|--rox|--rw|--rwx|--unix|--bind-tcp|--connect-tcp|--env)
      if [ "$#" -lt 2 ]; then
        echo "error: Landrun option $1 is missing its value" >&2
        exit 2
      fi
      landrun_options+=("$1" "$2")
      shift 2
      ;;
    -*)
      echo "error: unrecognized Landrun option $1; update scripts/landrun-wrapper.sh" >&2
      exit 2
      ;;
    *)
      break
      ;;
  esac
done

if [ "$#" -eq 0 ]; then
  echo "error: Comparator supplied no sandboxed command" >&2
  exit 2
fi

exec "$landrun_binary" "${landrun_options[@]}" -- "$@"
