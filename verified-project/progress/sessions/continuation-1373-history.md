# Current checkpoint:1373

Both projects independently PASS1373 declarations;286 public modules and root imports byte-match. Independent audit reports preserved;MAIN checked at 2026-10-24T12:14:29.525340+00:00. All19 OAI hashes match.286 public modules;694 additional supporting declarations from679;0 additional whole named statements this run. Named5 unconditional/3 conditional/43 incomplete outof51. Whole Lemma3.1 partial,GFF unproved. Usage31%,stop50%. Goal active,no blocker;this turn made concrete proof progress.

Whole Lemma3.1 remains partial. The canonical actual Hamiltonian-ground/transfer-Perron data remain proved. The actual free-point consecutive-root plane-wave determinant now has proved energy,sum dispersion,circle sign,nonvanishing,and a single configuration-independent phase making every ordered amplitude strictly positive. Still identify the coordinate hopping operator with the actual physical spin-sector Hamiltonian,including periodic boundary signs;identify the actual Bethe state with the free ground line;justify continuation in lambda. U09 retains occupied compact-test scope. No Bethe Perron conclusion is claimed.

# New verified blocks

Exact physical free-point momentum and dispersion: The physical shift phase equals -F_i_lambda(y-i*lambda/2),with real branch p=-2*pi*S_lambda(y). At the free point p=-2*arctan(tanh y),cos(p)=1/cosh(2y),and the actual kernel energy -2*pi*(1/2)*s(y) equals -cos(p). The actual homogeneous consecutive-root equations give p_j=pi*(n-1-2j)/L,the fermionic circle sign (-1)^(n-1),exact centering,and strict central-half-circle bounds when 2n<=L. The sign reverses rapidity order.

Finite Slater determinant eigenvalue theorem: An exact determinant identity sums weighted single-row updates to the sum of orbital weights times the determinant. A Slater determinant vanishes whenever two coordinates collide. If supplied one-particle orbitals obey explicit finite matrix eigenvalue equations,the coordinate Hamiltonian acts on their determinant by the sum of those eigenvalues. These are proved algebraic consequences;they do not assume the actual spin Hamiltonian identification.

Physical free plane-wave and Slater energy: The actual complex exponential plane wave on integer coordinates obeys nearest-neighbor hopping energy -cos(p). The actual consecutive-root momenta obey the correct periodic circle sign at every integer position. The exact free coordinate hopping operator acts on the finite plane-wave determinant with total energy equal to the sum of -cos(p_j). The coordinate operator is not yet identified with the actual spin-sector restriction.

Actual consecutive Slater Vandermonde and nonvanishing: The site Fourier phases are injective in one period. The actual consecutive-root Slater determinant equals an explicitly row-scaled Vandermonde determinant. Therefore every distinct-site configuration within one period has nonzero amplitude. All casts,phase factors,and the empty-particle case are retained;no Bethe-state correspondence is assumed.

Configuration-independent phase and strictly positive free Slater amplitudes: The site-phase difference has an exact sine factorization. The ordered-pair phase sum counts each coordinate n-1 times,so all configuration-dependent phases cancel. The actual consecutive-root Slater determinant equals one nonzero constant depending only on n times the real sine Vandermonde. Dividing by this single constant makes every ordered configuration within one period real and strictly positive. This constructs the positive candidate used in the free-point argument;the actual spin-operator and Bethe identifications remain open.

# Next proof obligations

Construct ordered occupied-site coordinates for each binary spin configuration and identify the exact free coordinate hopping with the actual spin-sector Hamiltonian,including collision zeros and periodic boundary signs.
Use the constructed positive free Slater vector to identify the free Hamiltonian ground line,then connect the actual nonzero Bethe state by a proved coordinate formula or differentiated actual transfer eigenvalue. Carry A01 explicitly if used for nonzero norms.
Justify continuation in lambda of the actual root/eigenvector branch and preserve its ground-state identity.
Retain U09:occupied compact test windows are proved;nonzero endpoint tests need separate boundary terms if intended.

# New APIs and scope

FreeFermionMomentum, SlaterEigen, FreeSlaterHamiltonian, FreeSlaterVandermonde, FreeSlaterPositive contain24 new public theorem declarations. All5 drafts integrated once. freeSlaterWave_fixed_phase_positive uses freeSlaterPhase n=product over i<j of(-2I),a fixed nonzero constant independent of sites. Momentum is NEGATIVE counting phase;do not reverse this sign. freeSlaterWave_energy is on integer labeled coordinates;it is not yet an actual physical-spin eigenvalue theorem. freeSlaterWave_consecutive_ne_zero holds for any injective integer site map in[0,L),while positivity requires StrictMono. All actual-consecutive-root formulas use zero site inhomogeneities. No assumed free-point ground-state result.

# Next implementation pointers

RowSpins is recursive nested Fin2 products with Unit at0. No conversion to FinL->Fin2 exists yet. SpinSwapConnectivity proves open adjacent swaps connect sectors; PhysicalChainHamiltonian proves actual H equals periodic cyclic local-link sum. Use Finset.orderEmbOfFin for ordered occupied positions after constructing the occupied-site set;its range is exactly that set. The pinned Mathlib LinearAlgebra.Vandermonde dependency was built in the shared cache with approval,source unchanged. General SlaterEigen proves the finite coordinate eigenfunction theorem abstractly,but actual spin identification is still needed.

# Prior context and rules

progress/sessions/continuation-1349-history.md preserves previous details. Both canonical actual ground-state and actual transfer Perron construction remain proved. OnlyA01Slavnov authorized as explicit Prop,never global axiom. MAIN=/Users/trishengunaratnam/Documents/Formalization Math/SixVertex requiresrequire_escalatedforsaving/building,already authorized. Nevercopyverificationreportsbetweenprojects;runindependentauditsandbytecompare286modulesplusroot. Lake root=staging/lean;PATH=/Users/trishengunaratnam/.elan/bin:$PATH. No subagentsauthorized. Reload the full visualize skill before creating or updating a visualization. Visualpath:/Users/trishengunaratnam/.codex/visualizations/2026/10/23/01a168f7-7ede-78a2-b429-e054eef2c3a9/six-vertex-progress.html. Expected18phases/177rootsteps/122auditrecords/9open/0errors/usage31%/0of15additionalnamed. Codeopenrequestsreturnqueued,notconfirmedvisible. Sourcepin1581d4cbdd69a0faf34b2089614fe2a814316a6a,19hashes,93pages.


# Prepared next step outside1373

drafts/SpinCoordinates.lean separately compiles successfully with9 theorem declarations,not included in1373. It constructs rowSpinAt/rowSpinsOfSites and their equivalence,minusCount as sum of site bits,occupiedSites cardinality,and the strictly increasing integer occupiedCoordinates with0<=x<L. It defines spinFreeSlaterVector on the ACTUAL particle-sector basis,using the proved ordered-coordinate positive Slater amplitude and the fixed phase,and proves it is real,strictly positive and nonzero. This is a constructed positive sector vector only;the actual Hamiltonian eigenvalue equation remains open. Next:integrate this checked draft once,then prove nearest-neighbor and periodic seam actions in these coordinates. A harmless final simpa linter warning remains;no sorry/admit/unsafe/global mathematical axiom. All proof and audit sessions are terminal at this checkpoint.
