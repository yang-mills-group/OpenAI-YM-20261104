import YM.Integration.WilsonOriginalPublicReflectedKColumn
import YM.Integration.WilsonReflectedPublicSignedFare
import YM.Integration.WilsonReflectedPublicCommonSup

/-! Uniform price of the actual K-site residual relative to the norm of the commissioned input. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonOriginalPublicReflectedKWallet
open Push Push.Local Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph RG05Readout RG05Readout.Address RG05Readout.Records
open MergeProof MergeProof.Accent PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato WilsonOriginalNullCorridor
open RG05Readout.UV RG05Readout.Copper RG05Readout.Native
open WilsonReflectedFundedHearing WilsonOriginalMicroscopicGuardedPage WilsonOriginalPublicReflectedKColumn
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family
local notation "β" => (C₀).path.levels.clock.hatBeta

def invoice (d:ℕ):ℝ:=
  (2+orbitCost ((C₀).labels.level d))*
    ((16+|GermGraph.price (C:=C₀) d| * Real.exp 200)*9*orbitCost ((C₀).labels.level d))

theorem stages (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(d:ℕ):
    ∀ᶠ K:ℕ in atTop,∀N p:ℕ,K≤N→((C₀).path.levels.budget K).supportExponent≤100 →
      let P:=(C₀).path.rep N p K
      turnCost P.p.order P.p.power*gross R d K≤ invoice R d*(β K)^3 ∧
      orbitCost ((C₀).labels.level d)*gross R d K≤ invoice R d*(β K)^3:=by
  filter_upwards [WilsonReflectedPublicRotationFare.original R simple shop d,
    WilsonThermometerOffsetLedger.original R simple shop d] with K rot entered N p live width
  let H:=β K
  let F:=(C₀).labels.level d
  let Ω:=orbitCost F
  let P:=(C₀).path.rep N p K
  let τ:=turnCost P.p.order P.p.power
  let D:=|GermGraph.price (C:=C₀) d| * Real.exp 200
  have one:1≤H:=((C₀).path.levels.fits.delayed K).le
  have hp:0<H:=zero_lt_one.trans_le one
  have op:0≤Ω:=zero_le_one.trans (orbitCost_one_le F)
  have dp:0≤D:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have tp:0≤τ:=by dsimp only [τ,turnCost];positivity
  have inner:0<2+Real.log H:=by linarith [Real.log_nonneg one]
  have gap:1+Real.log (2+Real.log H)≤2*H:=by
    linarith only [Real.log_le_sub_one_of_pos inner,Real.log_le_sub_one_of_pos hp,one]
  have turn:τ≤2*H:=(le_mul_of_one_le_right tp entered.2.1).trans ((rot N p live).trans gap)
  have census:GermGraph.stock (C₀) K≤WilsonThermometerOffsetLedger.cash R d K:=by
    change (R.alloy.B.a.params K).columns≤_
    rw [Push.PriceCompiler.params_eq R.alloy.B.valid K]
    exact (cash_fill G d (R.alloy.B.a.clock.J K) R.metals.p.profile R.y).choose_spec.2.1
  have st:GermGraph.stock (C₀) K≤2*H:=census.trans (entered.2.2.trans gap)
  have s0:0≤GermGraph.stock (C₀) K:=zero_le_one.trans ((C₀).path.levels.params K).columns_ge
  have project:WilsonReflectedAffordableArm.projectionBill R d K≤D:=by
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [width])) (abs_nonneg _)
  have keep:0≤WilsonReflectedAffordableArm.projectionBill R d K:=mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have first:WilsonReflectedAffordableArm.charge R d K≤(16+D)*H:=by
    unfold WilsonReflectedAffordableArm.charge
    nlinarith only [st,project,one,mul_le_mul_of_nonneg_left one dp]
  have second:1+4*GermGraph.stock (C₀) K≤9*H:=by linarith only [st,one]
  let fee:=(16+D)*9*Ω
  have budget:gross R d K≤fee*H^2:=calc
    _≤((16+D)*H)*(9*H)*Ω:=mul_le_mul_of_nonneg_right
      (mul_le_mul first second (by positivity) (mul_nonneg (by positivity) hp.le)) op
    _=_:=by dsimp only [fee];ring
  have feePos:0≤fee:=mul_nonneg (mul_nonneg (by positivity) (by norm_num)) op
  have tv:τ≤(2+Ω)*H:=turn.trans (mul_le_mul_of_nonneg_right (by linarith only [op]) hp.le)
  have ov:Ω≤(2+Ω)*H:=by nlinarith only [one,hp.le,mul_le_mul_of_nonneg_left one op]
  have refund (x:ℝ)(bound:x≤(2+Ω)*H):x*gross R d K≤ invoice R d*H^3:=calc
    _≤((2+Ω)*H)*(fee*H^2):=mul_le_mul bound budget (by
      unfold gross WilsonReflectedAffordableArm.charge
      exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) op) (mul_nonneg (by positivity) hp.le)
    _=_:=by dsimp only [invoice,fee,D,Ω,F];ring
  exact ⟨refund _ tv,refund _ ov⟩

theorem original (simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)(d:ℕ):
    ∀ᶠ K:ℕ in atTop,∀N p f (A:Arm R d N p f K)(front:f≤K)(high:K≤N),
    (C₀).ref d≤K→((C₀).path.levels.budget K).supportExponent≤100→
    ∀j q (start:j≤K){η bank:ℝ}{M:(C₀).label d ≃ₗ[ℂ] (C₀).label d},
      WilsonReflectedFullPanel.receipt R d j K N p q start high η M A.Y bank →
      A.w=M.symm (full R d N p j A.Y)→∀c:ℂ,
      ∃B:Arm R d N p K K,∃Q:Coefficient ((C₀).labels.level d) ((C₀).side K p),
        let cash:=invoice R d*(β K)^3*sourceFee R A c
        Filed R A front high c B Q cash cash:=by
  filter_upwards [stages R simple shop d] with K wage N p f A front high ref width j q start η bank M paid same c
  obtain ⟨B,Q,situated,source,form,old,head,exactField⟩:=
    WilsonOriginalPublicReflectedKColumn.original R A front high ref j q start paid same c
  have fee:=wage N p high width
  have sp:0≤ sourceFee R A c:=Work.G08.size_nonneg ..
  exact ⟨B,Q,situated,source,form,rem_mono old (mul_le_mul_of_nonneg_right fee.1 sp),
    head.trans (mul_le_mul_of_nonneg_right fee.2 sp),exactField⟩

end YM.Integration.WilsonOriginalPublicReflectedKWallet
