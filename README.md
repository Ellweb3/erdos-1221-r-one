# Erdős Problem 1221, the case r = 1

A Lean 4 proof of `Erdos1221.erdos_1221.variants.r_one` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures):
for points `a 0, a 1, …` on the circle, de Bruijn and Erdős (1949) proved

- `Λ₁ = 1/log 2`: the infimum over sequences of `limsup n · M_n`;
- `λ₁ = 1/log 4`: the supremum over sequences of `liminf n · m_n`;
- `μ₁ = 2`: the infimum over sequences of `limsup M_n / m_n`.

Here `M_n` and `m_n` are the longest and shortest arcs between consecutive points among the
first `n` points. See [Erdős Problem 1221](https://www.erdosproblems.com/1221).

## Files

- `Challenge.lean`: the statement. It imports only Mathlib. The definitions and the statement
  are copied verbatim from `FormalConjectures/ErdosProblems/1221.lean` at commit
  `ea8e3e198ded6fc73efb7f5653b74b28ac4ae1a8`.
- `Erdos1221/Defs.lean`: the same definitions, for the proof.
- `Erdos1221/ROne.lean`: the proof.
- `Solution.lean`: the proved statement, checked against `Challenge.lean` by `lake comparator`.

## The proof

- Upper bounds: the sequence `a k = log₂ (2k + 1)`. Its first `n` points correspond to the
  integers `n, …, 2n - 1`, so every arc lies between `log₂ (1 + 1/(2n-1))` and `log₂ (1 + 1/n)`.
- `μ₁ ≥ 2`: a new point splits some arc, so `2 m_{k+1} ≤ M_k`. If `M_k / m_k ≤ c < 2` for all
  large `k`, then `M_k` decays geometrically, which contradicts `M_k ≥ 1/k`.
- `Λ₁ ≥ 1/log 2`: the `t` new points `a n, …, a (n+t-1)` enter at most `t` arcs of time `n`.
  So the `t`-th largest arc at time `n` is at most `M_{n+t}`, and `1 ≤ ∑_{t<n} M_{n+t}`.
- `λ₁ ≤ 1/log 4`: at time `2n`, at most `2t` arcs have an endpoint added after time `2n - t`.
  Every other arc was already an arc at time `2n - t`, so `2 ∑_{t<n} m_{2n-t} ≤ 1`.

## Checks

```text
lake exe cache get
lake build
ruby scripts/validate-formalization.rb
./scripts/verify-comparator.sh   # Linux with bubblewrap
```

This repository follows the [Palomar template](https://github.com/PalomarRegistry/PalomarTemplate).
Submissions go through the [Palomar submission form](https://submit.palomar-registry.org/).
