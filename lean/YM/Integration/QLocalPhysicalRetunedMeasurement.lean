import YM.Integration.QLocalFiniteContactWindow
import YM.Integration.QLocalMarkedCouplingDifference
import YM.Integration.QLocalMarkedSpectator
import YM.Integration.ActualRunInterpolatedPackets

/-! Lower-order measurements on the actual density of the elected physical
bank. The old fine payment is transported onto the same coarse coupling as
the physical output, retaining the entire residual leaf in the comparison. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalPhysicalRetunedMeasurement

open Filter Lattice Wilson RG Marker Precision LocalComparison
open PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 QLocalVacuumOrderRestriction
open AnalyticBridge.VerifiedReset.Averaging WilsonLimitConstruction Pert.Asymptotics Push.AbsoluteSums
open ActualRunInterpolatedPackets QLocalMarkedCouplingDifference
open scoped Classical Topology

variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Census V} {J:Request V}
    (R:Run G) (hG:G.Simple) (hT:ActualRunNativeComponentRecipe.Attached R)
    (readout:RG05Preconstruction.ReadoutPurchase R.b)
    (caps:Handoff.OutputCapacities) (A:NumericSchedule R.family J) (K:NumericPrices A)

include hT readout

theorem selected {p:ℕ} (hp:2≤p) (hq:p≤J.order) (r:ℕ) :
    ∃ D:ℝ,0<D ∧ ∃ s:ℕ,∀ᶠ m:ℕ in atTop,
      ∀ (z:LocalFormal.Datum R.family Γ),z.level=m →
      ∀ (Y:Bulk.Chain R.family.path) (F:AnalyticInput J A z) (η:ℝ) (I:FullPreparedInputAt F η)
        (M:FundedPhysicalCatalogue.Purchase caps K F),
      FundedCoverKineticMeasurement.Tested R Y F M hG (fun v=>(0:(J.tests v).Mood)) →
      ∀ S:FundedRenderedBank.Chosen K I M.toCatalogue,
      η≤(Currency.g R.family z.cutoff z.period (z.level+1))^2 →
      I.carrier.rep.eval=(R.family.path.rep z.cutoff z.period (z.level+1)).eval →
      let f:=regulatorRun R.family z.cutoff z.period (z.level+1)
      let c:=regulatorRun R.family z.cutoff z.period z.level
      let O:=S.bank.output
      let Q:=onRun R z.cutoff z.period z.level O.model r
      let x:=(plan M.plan p).predict z.level+delta (S.vacuum.listing.read S.vacuum.source)
      let Z:=residual Q (Currency.gain x/c) 1
      let w:=fun v=>F.outputRadii v/F.kernelCosts v
      let bill:=K.geometry m*(1+1)*(rate (max caps.packetPower (r+2))*(6*(D*A.admittedCost m^s*f^(p+1))))
      Z.Paid (A.outputNorm z.level) F.outputAddresses M.region w c (A.outputWidth z.level)
          bill M.coverOffset M.coverSlope ∧
      (∀ (t:TestSpace J.tests) (U:Config G (R.family.side z.level z.period)),
        Z.read t c U=Q.read t (Currency.gain x) U-O.model.read t f U ∧
        Poly.pass (Q.read t (Currency.gain x) U)*(O.residual.leaf t).density U=
          Poly.pass (Z.read t c U)*(O.output.leaf t).density U) ∧
      (∀ (t:IndependentTests J.tests) (U:Config G (R.family.side z.level z.period)),
        let v:=testInclusion J.tests t
        let cost:=MarkedPackets.uniformReadCost caps.packetRank (Fintype.card V) bill
        cost≤1 →
        Poly.price w (Poly.pass (Q.read v (Currency.gain x) U)*(O.residual.leaf v).density U-
          (O.output.leaf v).density U)≤2*cost*Poly.price w ((O.output.leaf v).density U)) := by
  obtain ⟨D,hD,s,pay⟩:=QLocalFiniteContactWindow.selected (Γ:=Γ) R hG hT readout caps A K hp hq
  refine ⟨D,hD,s,?_⟩
  filter_upwards [pay,onRun_paid_eventually caps.packetPower R hG (by norm_num : (0:ℝ)<1)]
    with m paid copy z hz Y F η I M contact S hη hI
  subst m
  obtain ⟨hb,hx,amount⟩:=paid z rfl Y F η I M contact S hη hI
  let f:=regulatorRun R.family z.cutoff z.period (z.level+1)
  let c:=regulatorRun R.family z.cutoff z.period z.level
  let b:=R.family.path.β z.cutoff z.period z.level
  let x:=(plan M.plan p).predict z.level+delta (S.vacuum.listing.read S.vacuum.source)
  let O:=S.bank.output
  let Q:=onRun R z.cutoff z.period z.level O.model r
  let Z:=residual Q (Currency.gain x/c) 1
  let bill:=K.geometry z.level*(1+1)*(rate (max caps.packetPower (r+2))*
    (6*(D*A.admittedCost z.level^s*f^(p+1))))
  have live:0<c:=Currency.g_pos R.makes _ _ _ z.below.le
  have cap:O.model.powerCap≤caps.packetPower:=by
    dsimp [O]; rw [S.bank.same_model]; exact M.power_bounded
  have base:O.model.Paid (A.outputNorm z.level) F.outputAddresses M.region
      (fun v=>F.outputRadii v/F.kernelCosts v) f (A.outputWidth z.level) (K.geometry z.level)
      M.coverOffset M.coverSlope:=by
    dsimp [O]; rw [S.bank.same_model]; exact M.paid
  have booked:=copy z.cutoff z.period z.below O.model cap r base
  have self:b∈Currency.stripe b:=by constructor <;> linarith
  have issued:=QLocalMarkedCouplingDifference.paid Q hb hx self live.ne' booked
  change (residual Q (Currency.gain x/c) (c/c)).Paid _ _ _ _ c _ (_*(rate Q.powerCap*b⁻¹*|x-b|)) _ _ at issued
  rw [div_self live.ne'] at issued
  have qcap:Q.powerCap ≤ max caps.packetPower (r+2):=max_le_max_right _ cap
  have nonneg:0≤b⁻¹*|x-b|:=mul_nonneg (inv_nonneg.mpr hb.le) (abs_nonneg _)
  have cost:rate Q.powerCap*b⁻¹*|x-b|≤rate (max caps.packetPower (r+2))*
      (6*(D*A.admittedCost z.level^s*f^(p+1))):=by
    rw [mul_assoc]
    exact mul_le_mul (rate_mono qcap) amount nonneg (rate_nonnegative _)
  have stored:Z.Paid (A.outputNorm z.level) F.outputAddresses M.region
      (fun v=>F.outputRadii v/F.kernelCosts v) c (A.outputWidth z.level) bill
      M.coverOffset M.coverSlope := by
    refine { issued with roots := fun v => budget_loosen (issued.roots v) ?_ }
    exact mul_le_mul_of_nonneg_left cost (mul_nonneg (K.geometry_nonnegative _) (by norm_num))
  have rank:Z.rankCap≤caps.packetRank:=by
    change O.model.rankCap≤caps.packetRank
    dsimp [O]; rw [S.bank.same_model]; exact M.rank_bounded
  have difference (t:TestSpace J.tests) (U:Config G (R.family.side z.level z.period)) :
      Z.read t c U=Q.read t (Currency.gain x) U-O.model.read t f U:=by
    have left:=onRun_read R z.cutoff z.period z.level z.below O.model r base t U
    have eq:=QLocalMarkedCouplingDifference.read Q (Currency.gain x/c) 1 c live.ne' t U
      (NativePaidPacketColors.read_summable booked live.ne' t _ U)
      (NativePaidPacketColors.read_summable booked live.ne' t _ U)
    have tuned : Q.read t c U = O.model.read t f U := left
    simpa only [Z,div_mul_cancel₀ _ live.ne',one_mul,tuned] using eq
  refine ⟨stored,fun t U=>⟨difference t U,?_⟩,fun t U small=>?_⟩
  · rw [O.full t U]
    exact QLocalMarkedSpectator.multiply _ _ _ _ (difference t U) (O.model.quiet_read ..) (Z.quiet_read ..)
  · let v:=testInclusion J.tests t
    have debit:=(stored.uniform_read caps.packetRank rank t U).2
    rw [O.full v U]
    exact QLocalMarkedSpectator.charge stored.positive _ _ _ _ (difference v U)
      (O.model.quiet_read ..) (Z.quiet_read ..) debit small

end YM.Integration.QLocalPhysicalRetunedMeasurement
