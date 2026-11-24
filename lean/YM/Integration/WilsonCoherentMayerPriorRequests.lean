import YM.Integration.WilsonCoherentMayerPriorBank

/-! The powers needed for the submoments and their connected logarithm are fixed by the original physical arms before the request chooses its perturbative order. The reader norm can depend on the chosen request. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorRequests
open WilsonCoherentMayerPriorSource WilsonCoherentMayerPriorCapacity WilsonCoherentMayerPriorLog Extra.Trajectories
open private scale from YM.Integration.WilsonCoherentMayerPriorBank
open Filter Finset Function Lattice Wilson RG Precision Source Marker Push.GridApprox
open LocalComparison LocalComparison.Global PhysicalNext.Repeat.Legato IterationFour
open FullQLocal FullQLocal.RenderedStep Comparison.RG02 WilsonLimitConstruction
open RG3.Script.Picnic
open IterationFour.Vacuum MergeProof MergeProof.Accent
open MS MS.Menus MS.Local.Physical Extra.Histories ActualOriginalQReaders
open WilsonReportingPrescribedOldRawForecast (raw)
open private reader from YM.Integration.WilsonReportingPrescribedOldScale
open scoped Classical Topology BigOperators

variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V][Nonempty V]{B:Deck G}
    (R:Run G)(simple:G.Simple)(u:V→MS.Rake.Label B)(Q:MS.Land.Prescription B)(μ:ℝ)

theorem registered (K:ℕ):∃e:ℕ,∀J:Request V,∃C:ℝ,0<C ∧ ∀ᶠt:ℕ in atTop,
    ∀(d:LocalFormal.Datum R.family (Stock.census V)),d.level=t→d.cutoff=d.level+1→
    (∀a:Slot u,R.family.ref a.2.size≤d.level+1)→
    ∀(o:V→Site (R.family.side (d.level+1) d.period))(ks:V→ℕ), (∀i,ks i≤K)→
    ∀(x:IndependentTests (ActualOriginalQPointSetup.request R u J).tests){j:ℕ}(live:j≤d.level+1)
      (U:Config G (R.family.side j d.period)),
      let actual:=physical R simple u J Q μ d o ks x live U
      actual.part (Stock.census V).quiet=1 ∧
      ∀s:(Stock.census V).Mode, ‖actual.part s‖≤C*(R.family.path.levels.clock.hatBeta t)^e:=by
  obtain ⟨C,cp,e,late⟩:=WilsonSeparatedOriginalSlabQArms.original R Q u K μ simple
  refine ⟨e*Fintype.card V,?_⟩
  intro J
  let base:=ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _=>0)
  let M:ℝ:=1+∑i:V,|readerPrice base i|
  let c:=1+M*C
  have m1:1≤M:=le_add_of_nonneg_right (sum_nonneg fun _ _=>abs_nonneg _)
  have c1:1≤c:=le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans m1) cp.le)
  refine ⟨c^Fintype.card V,pow_pos (zero_lt_one.trans_le c1) _,?_⟩
  filter_upwards [late] with t posted d atDate cutoff age o ks orders x j live U actual
  subst t
  let D:=ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
  let b:=R.family.path.levels.clock.hatBeta d.level
  let word:=ActualStartupNormalizedQ.modeObservable Q D u (μ-R.family.S.scale d.cutoff) ks (testInclusion _ x)
  have b1:1≤b:=(R.family.path.levels.fits.delayed _).le
  have h1:1≤c*b^e:=one_le_mul_of_one_le_of_one_le c1 (one_le_pow₀ b1)
  have read (i:V):‖ActualRunQlocalNativeTuple.reader D i (testInclusion _ x i)‖≤M:=by
    have atRoot:=ActualOriginalQReaders.native_reader_bound D i x
    change ‖ActualRunQlocalNativeTuple.reader D i (testInclusion _ x i)‖≤readerPrice (ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o) i at atRoot
    rw [reader R J d.period (d.level+1) o i] at atRoot
    have term:|readerPrice base i|≤∑j:V,|readerPrice base j|:=single_le_sum (fun j _=>abs_nonneg (readerPrice base j)) (mem_univ i)
    exact atRoot.trans ((le_abs_self _).trans (by dsimp only [M];linarith only [term]))
  have identity (s):actual.part s=actualTransport R.family (N:=d.cutoff) (word s) live U:=
    WilsonReportingPrescribedOldMicroscopic.original R Q D u _ ks simple d.below age _ live s U
  constructor
  · rw [identity]
    have one:word (Stock.census V).quiet=fun _=>(1:ℂ):=by funext Z;simp [word,ActualStartupNormalizedQ.modeObservable,Census.quiet]
    rw [one,actualTransport_const R.family R.makes d.below]
  intro s
  rw [identity]
  apply actualTransport_norm_le R.family R.makes d.below _ live U
  intro Z
  change ‖∏i∈s.val,_‖≤_
  rw [norm_prod]
  have each i (_:i∈s.val):‖ActualRunQlocalNativeTuple.reader D i (testInclusion _ x i)*
        ActualOriginalCalibratedColumns.weightedObservable R B Q (u i) (μ-R.family.S.scale d.cutoff) _ (ActualRunQlocalNativeTuple.root D i) Z (ks i)‖≤c*b^e:=by
    rw [norm_mul]
    have arm:=posted (m:=d.level) (t:=d.level) le_rfl (WilsonReportHarvestUpperRange.latest R.family.S le_rfl)
      i (ks i) (orders i) _ (ActualRunQlocalNativeTuple.root D i) Z
    rw [cutoff]
    exact (mul_le_mul (read i) arm (norm_nonneg _) (zero_le_one.trans m1)).trans
      (by change M*(C*b^e)≤(1+M*C)*b^e;have pos:0≤b^e:=pow_nonneg (zero_le_one.trans b1) _;nlinarith only [pos])
  calc
    _≤∏_i∈s.val,c*b^e:=prod_le_prod (fun _ _=>norm_nonneg _) each
    _=(c*b^e)^s.val.card:=by simp
    _≤(c*b^e)^Fintype.card V:=pow_le_pow_right₀ h1 (card_le_univ s.val)
    _=c^Fintype.card V*b^(e*Fintype.card V):=by rw [mul_pow,pow_mul]

theorem priced (K:ℕ):∃e:ℕ,∀J:Request V,∃C:ℝ,0<C ∧ ∀ᶠt:ℕ in atTop,
    ∀(d:LocalFormal.Datum R.family (Stock.census V)),d.level=t→d.cutoff=d.level+1→
    (∀a:Slot u,R.family.ref a.2.size≤d.level+1)→
    ∀(o:V→Lattice.Site (R.family.side (d.level+1) d.period))(ks:V→ℕ), (∀i,ks i≤K)→
    ∀(x:IndependentTests (ActualOriginalQPointSetup.request R u J).tests){j:ℕ}(live:j≤d.level+1)
      (U:Config G (R.family.side j d.period)) (q old:Poly (Stock.census V)),q.part (Stock.census V).quiet=0→
    let actual:=physical R simple u J Q μ d o ks x live U
    ∀{δ:ℝ},0≤δ→δ≤1/2→(∀s,‖actual.part s-(Poly.pass q*old).part s‖≤δ)→
      old.part (Stock.census V).quiet≠0 ∧ ∀s,
        ‖(connected actual-(q+connected (normalized old))).part s‖≤C*(R.family.path.levels.clock.hatBeta t)^e*δ:=by
  let Γ:=Stock.census V
  obtain ⟨e,prior⟩:=registered R simple u Q μ K
  refine ⟨e+e*degree Γ,?_⟩
  intro J
  obtain ⟨c,cp,prev⟩:=prior J
  have cn:0≤count Γ:=by unfold count;exact Finset.sum_nonneg fun _ _=>by positivity
  have fund:0≤bill Γ c:=mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (add_nonneg zero_le_one cp.le)) cn)
    (pow_nonneg (add_nonneg zero_le_one (mul_nonneg (by norm_num) cp.le)) _)
  refine ⟨1+bill Γ c,add_pos_of_pos_of_nonneg zero_lt_one fund,?_⟩
  filter_upwards [prev] with t bounds
  intro d date top age o ks law x j live U q old quiet actual δ dp half fit
  let b:=R.family.path.levels.clock.hatBeta t
  have one:1≤b:=(R.family.path.levels.fits.delayed t).le
  have capital:=bounds d date top age o ks law x live U
  have full:=paid actual (Poly.pass q*old) capital.1 dp half (mul_nonneg cp.le (pow_nonneg (zero_le_one.trans one) _)) capital.2 fit
  have detached:old.part Γ.quiet≠0:=by
    simpa only [Poly.quiet_mul,Poly.pass_part _ quiet,one_mul] using full.1
  refine ⟨detached,fun s=>?_⟩
  rw [←filed q old quiet detached]
  calc _≤δ*bill Γ (c*b^e):=full.2 s
       _≤δ*(bill Γ c*b^(e+e*degree Γ)):=mul_le_mul_of_nonneg_left (scale Γ cp one e) dp
       _≤(1+bill Γ c)*b^(e+e*degree Γ)*δ:=by
         rw [mul_comm δ]
         exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
           (pow_nonneg (zero_le_one.trans one) _)) dp

end YM.Integration.WilsonCoherentMayerPriorRequests
