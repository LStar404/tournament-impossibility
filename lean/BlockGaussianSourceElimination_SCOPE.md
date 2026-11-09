# Independent next-stage block-source elimination

`BlockGaussianSourceElimination.lean` focused Lean compilation completed with exit 0 and generated its library olean. Endpoint `eliminate_block` depends only on propext, Classical.choice, Quot.sound. Log: `block_gaussian_source_elimination.log`.

Input is the actual fromBlocks matrix `[[I, alpha(S+vI)], [alpha(-S+vI), I]]` applied to the concatenated vector `(x,y)`, equal to `(e,e)`. Under explicit `v^2=1`, `beta=1-alpha^2 != 0`, `beta*t=alpha^2`, and `R(I+tS^2)=I`, it proves `x+y=(2/(1+v alpha)) R e`.

The two sum/difference equations are proved from the block system, not assumed in the endpoint. The denominator `1+v alpha` is proved nonzero from beta. Only the left inverse is needed for this implication; it is not silently claiming that arbitrary block matrices possess inverses. No skew, spectral, positivity, or energy assumption is used beyond the explicit plus/minus S block structure.

The frozen 140 source/configuration files were not changed. This new candidate has only focused verification and is not covered by the 140-module full verification/build certificate. It remains to instantiate actual blocks, prove the raw W/Lambda relation, and combine with the bilinear score-source identity. No Gaussian integral or permanent recovery is established here.
