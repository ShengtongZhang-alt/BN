#!/usr/bin/env bash
# Validates formalization.yaml against the upstream mathlib-initiative JSON schema
# (the format Palomar adopts, https://github.com/mathlib-initiative/formalization.yaml),
# pinned to a fixed commit so the check is reproducible.  Uses the validator the
# upstream README recommends, `check-jsonschema`.
#
# Usage: scripts/check-metadata-schema.sh
# Install the validator with `pip install check-jsonschema` (or `pipx install check-jsonschema`).
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)

# mathlib-initiative/formalization.yaml @ 2026-08-25 (schema dispatcher; selects v0.4 from `version`).
schema_commit=99c678e569c7c4c0772db297c5ddd5e4c9b6322e
schema_url="https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/$schema_commit/schema/formalization.schema.json"

if ! command -v check-jsonschema >/dev/null 2>&1; then
  echo "error: check-jsonschema is required (pip install check-jsonschema)" >&2
  exit 1
fi

check-jsonschema --schemafile "$schema_url" "$repository_root/formalization.yaml"
