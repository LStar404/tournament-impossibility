# Quantitative rational source exponent interface

Define Lambda=a/(1+a/n)-k^2*(psi/n^2)/(1+a/n). For n>0, |a|<=r,
r/n<=1/2, |k|<=R and |psi|/n^2<=B/n with B>=0, this module proves:

* |1+a/n|>=1/2, a genuinely nonzero denominator and inverse norm<=2;
* |Lambda-a|<=2*(r^2+R^2*B)/n;
* if this last bound is<=1, then
  |exp(Lambda)-exp(a)|<=4*exp(r)*(r^2+R^2*B)/n.

The exponential step is a separately exported general complex perturbation
lemma. Constants are explicit. Focused Lean compilation passed and the three
printed endpoints depend only on propext, Classical.choice and Quot.sound.
Aggregate integration is separate.

This module retains the normalized-source bound and parameter bounds as inputs;
it does not alone instantiate an actual graph, prove the branch parameter
substitution, combine the Gaussian prefactor, or establish Condition R.
