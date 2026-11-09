# Concrete spectral factors

Focused Lean verification passed. For actual factors constructed from AᴴA, proves XYᴴ=A and XᴴX=YᴴY=diag(s). Handles zero eigenvalues by the proved column annihilation identity, without assuming invertibility or an external support identity. All checked endpoints use only propext, Classical.choice and Quot.sound.

This is finite matrix factor algebra. No Fock positivity extension, positive integral, permanent inequality, spectral perturbation bound or circle envelope is supplied. The independent circle-tail transfer still requires its genuine circle bound.
