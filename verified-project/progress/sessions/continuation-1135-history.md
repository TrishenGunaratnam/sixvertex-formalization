# Current checkpoint:1135

Both projects independently pass1135 declarations;227 public modules and root imports byte-match. Both independent audit reports are preserved. Saved audit completed at 2026-10-24T08:52:14.849419+00:00. All19 OAI source hashes match.227 public proof modules;456 additional supporting declarations from baseline679;0 additional whole named statements this run. Named5unconditional/3conditional/43incomplete out of51. Whole Lemma3.1 partial,GFF unproved. Latest weekly usage23%,stop50%. Goal active,no blocker. This turn made concrete mathematical progress.

# New full physical filling block

The actual positive-K finite-window density decreases pointwise with increasing cutoff, as follows from the actual positive exterior operator and fixed-point comparison. Its ordinary exterior integral equals 2*(1-lambda/pi)*(1/2-M_Q). Comparing those integrals across cutoffs, with a strictly positive lost band, proves strict filling-mass monotonicity on Q>=0. No endpoint-derivative formula is assumed.

Combining the two signs of K and the free point, the actual M_Q is strictly increasing on Q>=0, M_0=0, 0<M_Q<1/2 for every finite Q>0, and M_Q tends to1/2. Every prescribed filling rho in(0,1/2) has exactly one actual nonnegative cutoff; every family of masses converging strictly below one half has eventually bounded cutoffs. All statements hold for every 0<lambda<pi.

The actual full-line exterior mass is between exp(-Q/(lambda/pi))/pi and twice that expression for Q>=0, by the identified density, evenness and actual exponential integration. The ordinary finite-window deficit is comparable to that exterior mass in both parameter regimes. Consequently the exact manuscript rate c*exp(-Q/(lambda/pi))<=1/2-M_Q<=C*exp(-Q/(lambda/pi)) is proved for every 0<lambda<pi, with positive constants chosen before every cutoff, including the free point.

The actual identified full-line density satisfies a two-sided spatial exponential comparison with exact inverse length pi/lambda, throughout the physical range. The proof compares the two exponentials defining cosh and then uses the proved actual density identification.

17 new supporting theorems in7modules:PositiveWindowMass,PositiveWindowMonotone,StrictPositiveFillingMass,UniformFillingMass,PhysicalDensityExteriorRate,PhysicalFillingRate,FullLineDensitySpatial. The former5 mass/antitonicity draft results are integrated,not counted twice. No new assumptions. Crosswalk clause3(comparison,mass,deficit)isnowchecked_in_lean;whole named Lemma3.1remainsincomplete.

# Next required work

Whole Lemma3.1 remains partial. Its uniform finite-window comparison, filling-mass monotonicity/limit, unique cutoff selection and exact exponential deficit are now proved for every physical lambda. Open: positive-K derivative estimates, actual reference/root construction and limiting quadrature; nominal sparse-edge positions; sector Perron identification; and remaining all-regime nonsingularity/analytic twist-branch clauses.

Prove positive-K finite-window relative derivative/log variation bounds using the actual positive resolvent and exact full-line spatial comparison.
Extend actual reference quantiles, scaled-density thresholds and exact-root construction/quadrature to every physical lambda.
Resolve nominal edges,Perron identification and the remaining analytic-branch clauses before counting whole Lemma3.1.

# Paths and boundaries

Writable staging:/Users/trishengunaratnam/Documents/ChatGPT/Formalization 6V/sixvertex-bootstrap
Lake root:staging/lean. PATH=/Users/trishengunaratnam/.elan/bin:$PATH
Saved MAIN:/Users/trishengunaratnam/Documents/Formalization Math/SixVertex
Saved writes/builds require require_escalated,already user-authorized. All reviews approved. Do not ask separately. Never copy staging verification.json over MAIN;independently audit each then compare every public module and root imports.
Lean/Mathlibv4.35.0,revision56a005855ea17e0b0958f73ec801ae140b0a1679. Staging packages symlink saved cache. Gamma.Beta,Fourier.Convolution,Fourier.Inversion,CauchyIntegral and dependencies are compiled. Old dependency71230 finished;do not restart.
Pinned OAI source1581d4cbdd69a0faf34b2089614fe2a814316a6a.19 original hashes match. One93-page manuscript. Source prefix:sources/openai-math/preprints/The-Gaussian-free-field-limit-of-the-balanced-six-vertex-model-with-variance-multiplier-1-over-arcsin-c-over-2-September-23-2026/build/sections/.
02-finite-rows.tex275-295 actual kernel/source Fourier and density formulas.03-thermodynamic-kernels.tex78-133 Lemma3.1,proof135-476;Lemma3.2at479,3.3at622,3.4at918,3.5at1083.
Only external mathematical assumption allowed:A01Slavnov,explicit Prop parameter,never a global axiom. No sorry/admit/unsafe/global mathematical axioms. Allowed kernel axioms onlypropext,Classical.choice,Quot.sound. Eight analytic flags remain open;0confirmed paper errors.
No subagents authorized. No new chats,automations,PRs,commits/worktrees. No model setting changed. Model advice answered:Sol6.1High main proof reasoning,Luna6High focused helpers;not benchmarked on this project.

# Previously verified scope

Complete first item Lemma3.1 negativeK:global unique finite roots for everyrealarray,2n<=L;positive whole-line counting density;uniform density and ordinary cumulative discrepancy half-filling. The comparison density now has its proved explicit formula.
Actual finite-window inverse,both identities and norm for everyphysicalλ;actualr_Q,H_Q equations/uniqueness and endpoint/source/mass continuity.
NegativeK:r_Q>=s>0,1<=H_Q<=(1-h)^-1,(1-h)r<=r_Q<=r inside;monotoneQ;M0=0,strictincreasingM to1/2,unique cutoff everyrho∈(0,1/2),eventually bounded cutoffs subhalf.
Actual CDF/midquantiles,meanfield phase/residual,weighted rows/Gaudin inverse,scaled Newton correction andwhole-line rho=Lr_Q+O1.
Actual Neumann convolution preserves radial decrease;exterior kernel comparison gives minr_Q>=(1-h)r(Q).
Actual corrected root construction whenLr(Q) crosses fixed threshold,eventually whenLr(Q)->infinity,including regular filling anddiverging missing-half-filled-root count.
Actual counting primitive and occupied windows,unitBL quadratureC/L;compact Lipschitz approximation/rescaling extends it to everycompact continuous test.
Actual bare arraygrid b_j=(j-(L-1)/2)*d/2,uniformbulk density c/d,translatedtesterrorC*d,and width-first spacing-second compactcontinuousdoublelimit. WidthB=Ld/2;bulk centers|a|<=(1-gamma)B/2. StrictnegativeK required bymassbound.
Actual density righttail~r(Q),finite-windowdeficit~r(Q);now r(Q)~exp(-Q/eta) exactlyidentified.
Previous1054 saved continuation is preserved inprogress/sessions/continuation-1054-history.md for detailed earlier proof APIs. Its open-status statements are historical,not current.

# Actual new API details

paperFourier f p=integral exp(-I*p*u)*f u. paperFourier_eq_fourier converts it to Mathlib Fourier atp/(2*pi). L1integrability,linearity andconvolution areproved inPaperFourier.
PhysicalKernelFourier proves actualK andS transforms. Frequencyzero usesifp=0 thenkernelmass;nonzero sinhquotient. Do not assert literal sinh0/sinh0 equals the continuation value.
FullLineDensityFourier proves actual(1+Khat)*rhat=shat andrhat=1/(2*cosh(lam*p/2)) forallrealp. The multiplier is proved nonzero forp!=0.
ExplicitDensityIdentification proves candidatecontinuous,candidateFTL1,andactualr=candidatepointwise. Two private normalizedFTlemmas handlep=2*pi*xi;transitivelyaudited.
DensityExponentialRate proves exp(-Q/eta)/(2lam)<=r(Q)<=exp(-Q/eta)/lam for0<lam<pi,Q>=0;and cexp<=1/2-M_Q<=Cexp forpi/2<lam<pi.
Complex.ofReal cast integrability is hf.ofReal. integral_complex_ofReal needsnointegrabilitypremise. Fourierinversion is Continuous.fourierInv_fourier_eq withactualfunctionandFT integrability.
Real.sinh_add/sub sumidentity needs explicit argument normalization afterfield_simp,which may reorderp*(pi-lam). Avoidbroadpush_cast aroundrealcosh/sinh casts.
A Fourier integrability majorant usesexplicit change before rw[norm_mul,he,one_mul];broad simp normalizesnegativeexponent in a waythat loseshe.
Real.exp_neg t yieldsinverse;simpa only[one_div] whenrequired1/exp t.

# Checks and display

scripts/check.py scans everypublic SixVertex module evenunimported. Keepunfinishedproofs/private/tmp or drafts. IndividuallyLean-checkthenpubliccopy/rootimport/fullaudit. Checkall reports and sourcebytecomparison. CheckerregressionsalreadyPASS960;do not rerununmodifiedtests.
Display1135:18phases,102rootsteps,79auditrecords,V65-V68,8openflags,5/3/43named,run0of15,usage23of50. Reload the full visualize skill before creating or updating a visualization. Visualpath:/Users/trishengunaratnam/.codex/visualizations/2026/10/23/01a168f7-7ede-78a2-b429-e054eef2c3a9/six-vertex-progress.html
Render scripts/render_audit.py andscripts/render_progress.py[visualpath]. FreshVMQA phases18/steps102/counts;finitewordsselection revealsA01,savesonce;restoredoesnotsave. open_in_codex returnsqueued;do notclaimvisiblecodeunlessconfirmed.
Batchindependentreads withPromise.allSettled,inspectall. Dependencies/mutationssequential. write_stdin forshellsessions;functions.wait only yieldedfunctions cellIDs. Do not restartliveprocessesonobservationtimeout. No ps(sandboxdenied).
Do not modify a proof file while its livecheck isrunning. Useuniquelogsperrevision. No unnecessary tests beyond Lean andfull audits.




# Current mathematical API and next derivative route

UniformFillingMass.lean assemblesallphysicalstrictmassmonotonicity,bounds,tendsto_half,strictboundsatQ>0,uniqueactualcutoffs,eventualboundedcutoffs. PhysicalFillingRate.lean provesexactallphysicalexponentialdeficitincludingfreepoint. PhysicalDensityExteriorRate.lean proves exp(-Q/eta)/pi<=ordinaryexteriormass<=2exp(-Q/eta)/pi byactualexpintegrationandevenness. Do not redo these.
StrictPositiveFillingMass.lean provesactualdeficit/exterioridentityforalllambda,andpositive-KstrictmassmonotonicitywithoutdifferentiatingQ. ForQ<T,thepositive-Kr_Qdecreasespointwise;ordinaryintegralsoutside[-T,T]strictlydecreasebecausethefixedpositivef_Qlosesapositiveband. Theirdeficitidentitygivesstrictmassincrease. Unique cutoffsusealreadyprovedmasscontinuityandIVT.
FullLineDensitySpatial.lean provesactualr spatialexponentialcomparisonwithC=pi/lambda forallphysicalλ. Aprivatecosh_spatial_upper bounds each definingexpseparately. Avoid '|*'lexicaltoken:putspaceafterclosingabsbar.

Next route forpositive-Kfirstderivativeregularity:actualR0=J*r,withJ>=0,sointegratingtheactualrcomparisonagainstJgivesactualR0spatialcomparisonwithsameC=pi/lambda. Theactualfinite-windowexteriorequationr_Q=r+R0*(indicator_out*r_Q),withr_Q>=0,thenpreservesthatcomparisononthewholeline. TakinglogsprovesLipschitzWithC forlogr_Q. TheactualfiniteIntervalDensity_hasDerivAt isalreadyprovedforallphysicalλ inFiniteIntervalRegularity.lean. Apply HasDerivAt.le_of_lipschitz toitslogderivative,then multiplybypositive r_Q toget|r_Q_prime|<=C*r_Q. This avoidsaddinganassumedresolventderivativebound. Itremainsunproveduntilnewdraftsarechecked.
PhysicalResolventFactorization.lean hasactualR0positivefactorizationandL1mass<half. PositiveWindowEquation.lean hasactualexteriorequations. PositiveWindowComparison.lean hasglobalpositive-Kr_Q>=r,globaladditiveupper,interiorrelativeupper,Hbounds,andnormexterior<1. BoundedconvolutionintegrandintegrabilityworksforJandactualr. Foroutput-variableintegralsR0(u-v)*r_Qv,usebounded_measurable_convolution_integrable orhk.comp_sub_left.mul_bdd.

Afterpositive-Krelativevariation,extendactualreferencequantilesandReferenceQuantileDatatoallλ usingnewactualdensitypositivityanduniquecutooff;existingReferenceQuantiles/ReferenceQuantileGeometryareunnecessarilyrestrictedbyhhalf,buttheirproofsonlyusecdfpositivity. Do notrenameorbreakoldAPIs;addgeneralizedtheoremsorreusegenericcores. Exact-rootconstructionandGaudininversesstillneedtheirfullall-physicalestimates;donotcountreferencequantilesasBetheroots.

Lean integral_div isthenamedBochnertheorem,notintegral_div_const. Do notsimp_rw[div_eq_mul_inv]beforeusinganexpintegralidentity:itrewritesdivisioninsideexponentialargumentsandlosesthematch. Toidentify2*(exp/(2*pi))=exp/pi,field_simp[pi_ne_zero]isneededbeforerationallinarith;ringalonecanleaveinverse(2*pi)opaque. integral_exp_mul_Ioi ha Q=-exp(a*Q)/a. Actualratescanusea=-(1/eta).
TheoremHasDerivAt.le_of_lipschitz {C:NNReal}(hlip:LipschitzWith C f)givesnormofactualderivative<=C directly. Also norm_deriv_le_of_lipschitz exists;firstavoidsrewritingderiv. LipschitzWith.of_dist_le_mul worksasexistingfiles.
Both5/3namedcountsand0newnamedthisrunareunchanged. No externalassumptionsbeyondA01Slavnov,explicitPropinput. No globalsorry/admit/unsafe/mathaxioms;allowedonlypropext,Classical.choice,Quot.sound. No subagents/chats/automations/PRs/commits/worktrees. Reload the full visualize skill before creating or updating a visualization.


# Prepared positive regularity/reference drafts outside1135

drafts/PositiveDensitySpatial.lean PASSES Lean individually(4 public theorems,closed session59281):actualpositiveR0spatialcomparisonviaitsprovedJ*rconvolution;actualpositive-Kr_Qglobalspatialcomparisonviatheactualexteriorfixedpointequation;globalcutoff-independentlogLipschitzbound;andactualfiniteIntervalDensityPrimeFunctionrelativebound|r_Q_prime|<=(pi/lambda)*r_Q. Scope0<lambda<pi/2,allrealQ,u. ThisisactualderivativeverifiedfromexistingfiniteIntervalDensity_hasDerivAt;notanassumedderivativeorabstractsurrogate. The firstthreeproofscomposeactualpointwisecomparisonsandintegrablepositiveconvolutions. The fourthusesHasDerivAt.le_of_lipschitzonlogr_Qandpositive r_Q.

Thefirstdraftcheck51282failedonlyon a deterministic heartbeat limit in broad simp[abs_sub_comm] whenprovingLipschitzWith. Fixedbychangingtotheexactabsolute-differencegoal andcallingthelogvariationtheoremwithargumentsy,x. Thecompletecheck59281thenPASSedwithoutincreasingheartbeats. Noactualmathgapidentified. Keepthisdirectorientation;avoidexpensivecommutativitysimplificationoflargeproofterms.

drafts/PhysicalReferenceQuantiles.lean PASSES Lean individually(5 public theorems,closed session53236):globalactualfinite-windowpositivityallλ;actualcumulativeintegralstrictlyincreasingallλ;uniqueinterioractualreferencequantile;exactorderedactualmid-quantiles;andmass-selectedReferenceQuantileDataforallphysicalλ,L>0,n>0,2n<L. The proofusesalreadycheckeduniqueactualmasscutoffsandordinarycumulativeintegrals. Thesearecontinuumreferencepoints,noton-shellBetheroots. Theformernegative-KAPIsarepreserved.

These9publicdraftstatementsareOUTSIDE1135 andnotcountedinthecheckpoint. Immediate next:integrate/root-import/full-audit them. Thenassembleall-physicalrelativeconstants,saykernelLogConstant(lambda)+pi/lambda,usingtheoldnegative-Kboundandnewpositive-Kbound. Extendactualreferencequadrature/weightedrows/Gaudininversesandlocalrootconstructiontothepositive-Krange. ExistingReferenceQuantileGeometry.sawtoothproofonlyneedsCDFstrictmonotonicity,socanuseitsnewall-physicalversion. Do notassumethereferencepointsalreadyobeythediscreteBetheequations.

Bothindependent1135reportsarepreserved;227publicmodules/rootimportsbyte-match. SavedauditUTC2026-10-24T08:52:14.849419+00:00. Alltemporaryproof/build/auditsessionsareclosed. FreshVMQA PASS18phases/102rootsteps/1135/usage23of50;A01selectionandrestorePASS. MainPhysicalFillingRate.lean:10openrequestqueued;donotclaimvisiblecode. No blockers,papererrors,newassumptionsorsubagents. Goalactive,latestusage23%,stop50%. Thisturnmadeconcretemathematicalprogress.
