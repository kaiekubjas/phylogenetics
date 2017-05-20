# phylogenetics
This repository contains the code for the phylogenetics project

The file "algorithm.m" contains Macaulay2 code for the modification of Algorithm 1 in the paper. It constructs ideals of Lagrange likelihood constraints for the interior and all the boundary components.

The folder "PHCpack" contains in the files "ideal_0", ..., "ideal_43" these ideals in Macaulay2 format. Files "ideal_0_phc", ..., "ideal_43_phc" in the same folder contain the generators of these files in the PHCpack format. Files "ideal_0_phc.phc", ..., "ideal_43_phc.phc" are outputs of PHCpack after we have run the command "phc -b" on all of the PHCpack input files. In particular, they contain all the complex solutions of the corresponding ideal.
