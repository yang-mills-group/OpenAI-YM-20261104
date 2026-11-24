import YM.Integration.QLocalReceivedWilsonState
import YM.Integration.QLocalPhysicalRetunedRate

/-! Absolute all-field order restriction on the received physical Q
trajectory. Both the marked test comparison and the cutoff/period
identification refer to the original normalized Q input. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalOriginalQForecast

open Filter Lattice Wilson RG Marker Precision LocalComparison LocalComparison.Global
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction MergeProof.Accent QLocalReceivedWilsonState
open AnalyticBridge.VerifiedReset.Averaging WilsonLimitConstruction Pert.Asymptotics
open ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open scoped Topology Classical

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {B:MS.Local.Physical.Deck G}

omit [Fintype V] in
private theorem transport {C:Family G} {N N' b b' j k:ℕ} {Γ:Census V}
    {Y:Config G (C.side j b)→Poly Γ} {Y':Config G (C.side j b')→Poly Γ} (hn:N=N') (hb:b=b')
    (hy:HEq Y Y') (hk:k≤j) {w:V→ℝ} {a:ℝ}
    (paid:∀U,Poly.price w (actualSignedTransport C (N:=N') Y' hk U)≤a) :
    ∀U,Poly.price w (actualSignedTransport C (N:=N) Y hk U)≤a := by
  subst N' b'
  have eq:Y=Y':=eq_of_heq hy
  simpa only [eq] using paid

variable [Nonempty V] {J:Request V} (R:Run G) (hG:G.Simple) (u:V→MS.Rake.Label B)
    (J₀:Request V) (A₀:NumericSchedule R.family J₀) (hT:ActualRunNativeComponentRecipe.Attached R)
    (readout:RG05Preconstruction.ReadoutPurchase R.b) (caps:Handoff.OutputCapacities)
    (A:NumericSchedule R.family J) (K:NumericPrices A)

include hT readout

theorem selected {p:ℕ} (hp:2≤p) (hq:p≤J.order) (r:ℕ) {ε:ℝ} (hε:0<ε) :
    ∀ᶠ m:ℕ in atTop,∀ (d:LocalFormal.Datum R.family (Stock.census V)),d.level=m →
      ∀ (Y:Bulk.Chain R.family.path) (F:AnalyticInput J A d) (η:ℝ) (I:FullPreparedInputAt F η)
        (M:FundedPhysicalCatalogue.Purchase caps K F),
      FundedCoverKineticMeasurement.Tested R Y F M hG (fun v=>(0:(J.tests v).Mood)) →
      ∀ S:FundedRenderedBank.Chosen K I M.toCatalogue,
      η≤(Currency.g R.family d.cutoff d.period (d.level+1))^2 →
      I.carrier.rep.eval=(R.family.path.rep d.cutoff d.period (d.level+1)).eval →
      let O:=S.bank.output
      let Q:=onRun R d.cutoff d.period d.level O.model r
      let x:=(plan M.plan p).predict d.level+delta (S.vacuum.listing.read S.vacuum.source)
      let w:=fun v=>F.outputRadii v/F.kernelCosts v
      let f:=regulatorRun R.family d.cutoff d.period (d.level+1)
      ∀ (d₀:LocalFormal.Datum R.family (Stock.census V)),d.cutoff=d₀.cutoff → d.period=d₀.period →
      ActualOriginalQLayout.referenceLevel R u≤d₀.level+1 →
      ∀ (P:MS.Land.Prescription B) (o:V→Site (R.family.side (d₀.level+1) d₀.period))
        (μ:ℝ) (orders:V→ℕ)
        (source:TestSpace J.tests → Config G (R.family.side (d₀.level+1) d.period)→Poly (Stock.census V)),
      State I (d₀.level+1) source →
      ∀ (t:IndependentTests J.tests)
        (t₀:IndependentTests (ActualOriginalQPointSetup.request R u J₀).tests),
      let v:=testInclusion J.tests t
      let v₀:=testInclusion _ t₀
      HEq (source v) ((ActualOriginalQInitialPreparation.input R hG u J₀ A₀ d₀ P o μ orders).leaf v₀).density →
      ∀ U,let ρ:=((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹
      Poly.price w (ρ • (Poly.pass (Q.read v (Currency.gain x) U)*(O.residual.leaf v).density U-
        (O.output.leaf v).density U))≤ε*f^((p:ℝ)+1-J.eta) := by
  let bound:=MarkedPackets.uniformModelCost (ActualOriginalQLayout.rankCap R u) (Fintype.card V) 1
  let c:=max 1 bound
  have cp:0<c:=zero_lt_one.trans_le (le_max_left _ _)
  filter_upwards [QLocalPhysicalRetunedRate.physical (Γ:=Stock.census V) R hG A K hT readout caps hp hq r
    (div_pos hε cp)] with m price d hm Y F η I M contact S hη fine
  dsimp only
  intro d₀ hn hb ref P o μ orders source L t t₀ chosen U
  let v:=testInclusion J.tests t
  let w:=fun v=>F.outputRadii v/F.kernelCosts v
  let ρ:=((R.family.path.rep d.cutoff d.period d.level).eval U)⁻¹
  let f:=regulatorRun R.family d.cutoff d.period (d.level+1)
  let a:=((p:ℝ)+1-J.eta)
  have hf:0<f:=Currency.g_pos R.makes _ _ _ d.below
  have prev:(d₀.level+1)≤d.cutoff:=by
    rw [hn]
    exact Nat.succ_le_of_lt d₀.below
  have hk:d.level≤d₀.level+1:=(Nat.le_succ _).trans L.before
  have actual:=QLocalReceivedWilsonState.output L M.toCatalogue S.bank v
  have received:actualSignedTransport R.family (N:=d.cutoff) (source v) hk U=
      ρ • (S.bank.output.output.leaf v).density U:=by
    rw [actualSignedTransport_eq R.family R.makes prev,←actual]
  have weightpos:∀v,0<w v:=fun _=>div_pos (F.output_radius_positive _) (F.kernel_positive _)
  have counted:Poly.price w (ρ • (S.bank.output.output.leaf v).density U)≤c:=by
    rw [←received]
    exact (transport hn hb chosen hk (QLocalNormalizedQBirth.transported R hG u J₀ A₀ d₀ P o μ orders
      ref w weightpos (QLocalReceivedWilsonState.weight L) t₀ hk) U).trans (le_max_right _ _)
  have physical:=price d hm Y F η I M contact S hη fine t U (ρ:ℂ)
  simp only [Complex.coe_smul] at physical
  calc
    _≤(ε/c*f^a)*Poly.price w (ρ • (S.bank.output.output.leaf v).density U):=physical
    _≤(ε/c*f^a)*c:=mul_le_mul_of_nonneg_left counted (mul_nonneg (div_pos hε cp).le (Real.rpow_nonneg hf.le _))
    _=ε*f^a:=by field_simp [cp.ne']

end YM.Integration.QLocalOriginalQForecast
