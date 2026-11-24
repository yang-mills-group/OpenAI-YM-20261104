import YM.Integration.WilsonReportingPrescribedOldFirstCourse
import YM.Integration.WilsonReportingPrescribedOldMicroscopic
import YM.Integration.WilsonSeparatedOriginalSlabQArms

/-! The complete submoments that multiply errors in the connected logarithm are genuinely bounded on the original older Wilson law. The reference readers are fixed before any positions, cutoff or period. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonCoherentMayerPriorSource
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
    (R:Run G)(simple:G.Simple)(u:V→MS.Rake.Label B)(J:Request V)(Q:MS.Land.Prescription B)(μ:ℝ)

def physical (d:LocalFormal.Datum R.family (Stock.census V)) (o:V→Site (R.family.side (d.level+1) d.period))
    (ks:V→ℕ)(x:IndependentTests (ActualOriginalQPointSetup.request R u J).tests)
    {j:ℕ}(live:j≤d.level+1)(U:Config G (R.family.side j d.period)):Poly (Stock.census V):=
  ((R.family.path.rep d.cutoff d.period j).eval U)⁻¹ • gust R.family.path d.cutoff d.period (d.level+1)
    (raw R simple u J d Q o μ ks x) j live U

theorem original (K:ℕ):∃C:ℝ,0<C ∧ ∃e:ℕ,∀ᶠt:ℕ in atTop,
    ∀(d:LocalFormal.Datum R.family (Stock.census V)),d.level=t→d.cutoff=d.level+1→
    (∀a:Slot u,R.family.ref a.2.size≤d.level+1)→
    ∀(o:V→Site (R.family.side (d.level+1) d.period))(ks:V→ℕ), (∀i,ks i≤K)→
    ∀(x:IndependentTests (ActualOriginalQPointSetup.request R u J).tests){j:ℕ}(live:j≤d.level+1)
      (U:Config G (R.family.side j d.period)),
      let actual:=physical R simple u J Q μ d o ks x live U
      actual.part (Stock.census V).quiet=1 ∧
      ∀s:(Stock.census V).Mode, ‖actual.part s‖≤C*(R.family.path.levels.clock.hatBeta t)^e:=by
  obtain ⟨C,cp,e,late⟩:=WilsonSeparatedOriginalSlabQArms.original R Q u K μ simple
  let base:=ActualOriginalQPointSetup.pointDatum R J 0 0 (fun _=>0)
  let M:ℝ:=1+∑i:V,|readerPrice base i|
  let c:=1+M*C
  have m1:1≤M:=le_add_of_nonneg_right (sum_nonneg fun _ _=>abs_nonneg _)
  have c1:1≤c:=le_add_of_nonneg_right (mul_nonneg (zero_le_one.trans m1) cp.le)
  refine ⟨c^Fintype.card V,pow_pos (zero_lt_one.trans_le c1) _, e*Fintype.card V,?_⟩
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

end YM.Integration.WilsonCoherentMayerPriorSource
