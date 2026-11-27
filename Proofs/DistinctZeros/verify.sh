#!/usr/bin/env bash
# Run with the published compact-runtime-build-435-03 and compact-zeta-build-435-01 installed.
set -euo pipefail
runtime=$(realpath "${1:?Pass the compact verification runtime directory}")
src=$(cd "$(dirname "$0")" && pwd)
[[ $(lean --githash) == eb6cafb7290e8bd5f2937522d8d804f58f02bafc ]]
build=$(mktemp -d)
trap 'rm -rf -- "$build"' EXIT
cd "$build"
mkdir -p ChallengeDeps Solution
ln -s "$runtime/deps/zeta/ChallengeDeps.olean" ChallengeDeps.olean
export LEAN_NUM_THREADS=2 LEAN_ABORT_ON_PANIC=1
deps=$(find "$runtime/deps" -mindepth 1 -maxdepth 1 -type d | sort | paste -sd:)
base="$build:$runtime/compat:$deps:$(lean --print-prefix)/lib/lean"
export LEAN_PATH="$runtime/interface:$base"
printf '%s\n' 'import LegacyFinsetSyntax' 'import ChallengeDeps' 'import Main' \
  'noncomputable def currentRecordKappa : ℝ := 85390845089 / 100000000000' \
  'noncomputable def candidateKappa : ℝ := 854225 / 1000000' > ChallengeDeps/CandidateSpec.lean
lean -j2 -o ChallengeDeps/CandidateSpec.olean ChallengeDeps/CandidateSpec.lean
curl -fsSL --retry 3 \
  https://raw.githubusercontent.com/josusanmartin/riemann/d4d280813d0b4f2a8fbb89229755b24f1dfee63e/submissions/knausgard-rh-reflected-kernel-8542/proof/Solution.lean \
  -o Solution/Candidate.lean
echo '57ee6e4def6c05145ce8196f49ce6302b211a24fa4feb091afbd732db93a12f3  Solution/Candidate.lean' | sha256sum -c -
lean -j2 --tstack=400000 -o Solution/Candidate.olean Solution/Candidate.lean
# Link the compiled proof on the real Riemann hypothesis implementation.
export LEAN_PATH="$runtime/foundation:$base"
cp "$src"/{Bridge,Result}.lean .
lean -j2 -o Bridge.olean Bridge.lean
lean -j2 -o Result.olean Result.lean | tee axioms.log
grep -Fx "'riemannZeta.distinct_prop_lt' depends on axioms: [propext, Classical.choice, Quot.sound]" axioms.log
roots=(Quot Quot.mk Quot.lift Quot.ind propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam)
leanexport Result -- "${roots[@]}" riemannZeta.distinct_prop_lt > result.ndjson
leanchecker --from-export result.ndjson
