# FormalPowerSeries

[![Nix CI for bundle coq8.17-mc2.2.0](https://github.com/hivert/FormalPowerSeries/actions/workflows/nix-action-coq8.17-mc2.2.0.yml/badge.svg)](https://github.com/hivert/FormalPowerSeries/actions/workflows/nix-action-coq8.17-mc2.2.0.yml) [![Nix CI for bundle coq8.18-mc2.2.0](https://github.com/hivert/FormalPowerSeries/actions/workflows/nix-action-coq8.18-mc2.2.0.yml/badge.svg)](https://github.com/hivert/FormalPowerSeries/actions/workflows/nix-action-coq8.18-mc2.2.0.yml) [![Nix CI for bundle coq8.17-mc2.2.0](https://github.com/hivert/FormalPowerSeries/actions/workflows/nix-action-coq8.19-mc2.2.0.yml/badge.svg)](https://github.com/hivert/FormalPowerSeries/actions/workflows/nix-action-coq8.19-mc2.2.0.yml)

## Formal power series in Mathematical Components.

The goal of this project is to formalize the notion of Formal Power
Series. I've mainly in view application to enumerative and algebraic
combinatorics. They are two different formalization:

1 - an axiom free formalization of Truncated Formal Power Series. It is
largely based on the work of Cyril Cohen et al. on Newton Sums.

   https://github.com/math-comp/newtonsums

The main difference is that they assumed the base ring to be a field whereas I
tried to use the more general base ring setting to formalize the different
properties.

2 - Formal Power Series using classical axioms. These are defined as the
inverse limit of the truncated power series allowing to transfer easily result
between the two setting.

The main results are
- formula for the multiplicative inverse of a series both in a commutative and
  non-commutative setting;
- geometric series;
- formal derivative and primitive (commutative and non-commutative);
- composition of power series (assuming the inner one has zero constant
  coefficient);
- Lagrange inversion formulas (Lagrange-Bürmann theorem);
- exponential and logarithm series.

All those results are proved both for truncated and non-trucated series.


## Application to combinatorics

To test the framework I provide 6 proofs of the formula for Catalan
numbers. I'm using the following 3 different strategies together with
truncated and non-trucated series:

1 - prove the algebraic equation `F = 1 + X F^2` and extract the
coefficients using square root and Newton's formula;

2 - Start again from the algebraic equation, extract the coefficients
using Lagrange inversion formula;

3 - Transform the algebraic equation into the holonomic differential equation
 `(1 - 2X) F + (1 - 4X) X F' = 1` which give the recursion
 `(n+2) C(n+1) = (4n + 2) C(n)` and solve it.


All these files are still largely experimental

To compile it I'm using the following opam packages:
```
coq-hierarchy-builder     1.8.0
coq-mathcomp-ssreflect    2.3.0
coq-mathcomp-algebra      2.3.0
coq-mathcomp-multinomials 2.3.0
coq-mathcomp-classical    1.8.0
```

