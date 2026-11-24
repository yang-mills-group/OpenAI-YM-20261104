import YM.Integration.WilsonMacroscopicRichGridDefects
/-! The price of evaluating the original independent prescription with unit
amplitude on every normalized marked test at every genuine fine site. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichGridUnit
open Function Filter Set MeasureTheory Lattice RG Wilson Source Labels Analysis Next.Foundations Push.Local
open PhysicalNext PhysicalNext.Repeat.Legato RG05Readout Address Native Pulse Flatten RGComparison.Core16
open OPE PhysMS Spec RG17 Extraction MergeProof.Accent Marker Precision Next.UVStress
open LocalComparison LocalComparison.Global IterationFour IterationFour.Vacuum FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric WilsonLimitConstruction QLocalOriginalQHistory
open WilsonSeparatedOriginalSlabWatchScalarMesh
open scoped Classical BigOperators Topology
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V]{B:MS.Local.Physical.Deck G}
    (R:Run G)(hG:G.Simple)(v:V → MS.Rake.Label B)(J:Request V)(A:NumericSchedule R.family J)
    (d:LocalFormal.Datum R.family (Stock.census V))(Q:MS.Land.Prescription B)(μ:ℝ)(ord:V → ℕ)
local notation "N₀" => d.level+1
local notation "UV" => Config G (R.family.side (N₀) d.period)
local notation "Sites" => V → Site (R.family.side (N₀) d.period)
local notation "J₀" => ActualOriginalQPointSetup.request R v J
private theorem constantBill (T:ComparisonDensity.Address.Orbit)(c:ℝ)(hp:0≤c):
    T.Bill (fun _=>(c:ℂ)) c:=by
  refine ⟨hp,contDiff_const,?_⟩
  intro j _ x _
  by_cases hz:j=0
  · subst j
    rw [norm_iteratedFDeriv_zero,Complex.norm_real,Real.norm_of_nonneg hp]
    have hh:1≤T.height x:=one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg x))
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh hp
  · rw [iteratedFDeriv_const_of_ne hz];simp only [Pi.zero_apply,norm_zero]
    exact mul_nonneg (T.sky x).le hp

def fee (x:Sites):ℝ:=ActualOriginalQInitialInput.normalizer R hG v J A d Q x μ ord
local notation "cost" => fee R hG v J A d Q μ ord
def restored (x:Sites):TestSpace (J₀).tests:=fun _=>
  ⟨fun _=>(cost x:ℂ),cost x,constantBill _ _ (le_trans zero_le_one (le_max_left _ _))⟩
local notation "buyer" => restored R hG v J A d Q μ ord

theorem tariff (x:Sites)(i:V):((J₀).tests i).Bill ((buyer x i).val) (cost x):=
  constantBill _ _ (le_trans zero_le_one (le_max_left _ _))

theorem calibrated (x:Sites)(i:V):
    ((VariableScaling.tests (ActualOriginalQInitialInput.scales R hG v J A d Q x μ ord) (buyer x)) i).val 0=1:=by
  have hc:1≤cost x:=le_max_left _ _
  change ((cost x:ℂ)⁻¹)*(cost x:ℂ)=1
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le zero_lt_one hc).ne')

theorem original (x:Sites)(s:(Stock.census V).Mode)(U:UV):
    WilsonMacroscopicRichQSiteInput.observation R hG v J A d Q x μ ord (buyer x) s U=
      ∏i∈s.val,WilsonMacroscopicRichOriginalPortfolio.observation R Q (d.level+1) d.period (v i)
        (μ-R.family.S.scale d.cutoff) (ord i) (x i) U:=by
  rw [WilsonMacroscopicRichQSiteInput.sites]
  apply Finset.prod_congr rfl;intro i _
  rw [calibrated,one_mul]

end YM.Integration.WilsonMacroscopicRichGridUnit
