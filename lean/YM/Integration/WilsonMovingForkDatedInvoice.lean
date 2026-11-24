import YM.Integration.WilsonMovingForkCapturedPrint
import YM.Integration.WilsonMovingForkTerminalFile
import YM.Integration.WilsonMovingForkExistingSale
import YM.Integration.WilsonMovingForkDatedContrast

/-! Source-specific price of the complete dated invoice. Every consecutive
charge is on the actual posted density and the two named original flats. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonMovingForkDatedInvoice
open Tree QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit AnalyticBridge
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker Multi QuadraticLocal QuadraticLocal.Earn
open Push Push.AbsoluteSums QuadraticLocal.Sunrise QuadraticLocal.Poetry QuadraticLocal.Affinity
open PhysicalNext PhysicalNext.Repeat.Legato RG16 RG16.Literal Trace.Physical.GermGraph
open WilsonRootedKioskOccupiedSlip WilsonOlderFreshGraphSlate WilsonRegisteredPairUnaryWallet
open WilsonOriginalMixedBlockRows Pert.Asymptotics Trace.Pilot OPE
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkFiniteCell (Later)
open WilsonMovingForkPrintedFile (Program registered allSlots parent)
open WilsonMovingForkMixedSeed (doses)
open WilsonThermometerUnitFilingFourSquare (Arm)
open WilsonThermometerUnitFilingCoarse WilsonThermometerUnitFilingFlatTelescope
open WilsonOriginalTwoFlatTelescope
open WilsonOriginalTwoFlatIRHalo (roof power)
open WilsonPositionProgramReporterBand (Band)
open scoped Classical BigOperators Topology
variable {G:Gauge}{R:Run G}{S:Table R.family.book}{l:Ultrafilter (ℕ×ℕ)}
  {n K:ℕ}{d:Fin n → ℕ}{x:∀i,S.Field (d i)}
  (old:Filed R d K)(arms:∀a,Arm R.family S (l:Filter _) (d a) (x a))
  (X:XSpace.Run){stage u depth:ℕ}(band:Band R X stage)(stop:WilsonIndependentCapturedPages.Stop R X band u depth)
  {j:ℕ}(cut:j ≤ K)(goal h:ℕ)(issued:WilsonMovingForkMountedStage.Paid R X band stop goal h)
local notation "c" => band.reporter+h
local notation "C" => R.family

open WilsonMovingForkTerminalFile (Source programme)
open WilsonMovingForkChronologicalTable (density)
open WilsonMovingForkChronologicalSale (Mounted)
open WilsonMovingForkDepositedPrint (polynomial)
open WilsonMovingForkShiftedSite (Reached)
open WilsonMovingForkFiniteCell (Upper)
open WilsonOriginalTwoFlatGridCapture (word)

variable (sheets:Source R d (stop.date h) K)(simple:G.Simple){m k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin){φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)
  (ahead:Mentor.Forecast D R.rolls Q φ books)

theorem original (N per:ℕ)(top:K<N)(ck:c<K)(positive:0<stop.date h)
    (moved:Fin n → Cover)(Ψ:∀i,Rep G ((C).side i per))(P size:ℕ)(η entry:ℝ):
    let prog:=programme sheets
    let rep:=(C).path.rep N per c
    let g:=regulatorRun (C) N per c
    let w:=doses R d old.station (N:=N) (per:=per) (old.A N per) (fun a=>(arms a).source (N,per))
    let ξ:=WilsonMovingForkSeededPoint.seats (R:=R) cut per moved
    let b:=prog N per w ξ c ck
    let v:=stop.date h
    let I:=(polynomial (sheets N per top.le w ξ v le_rfl ((stop.upper h).trans_lt ck)) (regulatorRun (C) N per v)).part (allSlots n)
    let day:=(WilsonOriginalOrdinaryFaceOrder.constant (allSlots n) (allSlots n).val.card+
      η*(2:ℝ)^P*WilsonOriginalCensusFiledHousing.fare (allSlots n) size)*(regulatorRun (C) N per v)^P
    ∀{ord seats shelf ext:ℕ}{stripU slack gross:ℝ},
      0 ≤ b.strip → b.order ≤ ord → 1 ≤ seats → n ≤ seats → (∑a,b.load a) ≤ shelf → 
      Invoice.Supports rep.p stripU (rep.p.supportExponent+2) g b.strip slack → 
      Invoice.price rep.p stripU (ord+shelf+1) seats (rep.p.supportExponent+2) slack G ≤ 
        (2:ℝ)^(ord+shelf+1)*(3*g⁻¹)^2 → 
      (∑a:b.index,Real.exp (b.strip*(b.binder a).length)*WilsonIndependentCollarSlateIntensity.amount
        (b.copies a) (b.binder a).center) ≤ gross*(3*g⁻¹)^ext → 
      (∀a,parent R ck.le per ξ a=0) → Opened (C) 0 u per → Opened (C) 0 (stop.date h) per → 
      4*(goal+(power (allSlots n).val.card ((∑a,b.load a)+1+2+ext)+0+2)) ≤ depth → 
      let unitGross:=((2:ℝ)^(ord+shelf+1))^2*max 1 gross
      let e:=power (allSlots n).val.card ((∑a,b.load a)+1+2+ext)+0+2
      let bill₀:=WilsonOriginalTwoFlatIRFiled.reserve (roof (Stock.census (Fin n)) (allSlots n)
        ((C).localSection 0) (C).params rep.p.supportExponent unitGross) 1*3^e
      (∀i,v ≤ i → i ≤ K → Mounted prog N per w ξ i) →
      (∀a:ℕ,v ≤ a+1 → a+1<K →
        WilsonReceivedChronologicalDualInterval.Owned (N:=N) R simple hk D Q π Γ Ψ books ahead
          (density prog N per w ξ) a u v (allSlots n) P size η) →
      Upper old arms cut issued.1 (stop.upper h) ck.le moved (N,per) top entry →
      let paid:WilsonMovingForkHeterogeneousCut.Invoice:=⟨entry,fun _=>day,bill₀*g^goal,fun _=>day,0⟩
      WilsonMovingForkDatedExterior.At (registered old prog) issued.1 (stop.upper h) ck.le cut moved (N,per)
        top (fun a=>(arms a).source (N,per)) I paid:=by
  intro prog rep g w ξ b v I day ord seats shelf ext stripU slack gross hs dep oc slots fit fund fare wage
    atZero ou ov deep unitGross e bill₀ mounts grants entryFee bill
  let M:=WilsonMovingForkPrintedFile.row prog N per w ξ
  have hired:∀i,v ≤ i → i ≤ K → Integrable (numerator R N per i (M i)) (prior G _):=by
    intro i iv it
    exact WilsonMovingForkChronologicalTable.full prog N per w ξ i ▸
      (Poly.get (allSlots n)).integrable_comp (WilsonMovingForkChronologicalSale.integrable prog N per w ξ it top.le (mounts i iv it))
  have edge:∀a,v ≤ a → a<K → ∀b',u ≤ b' → b' ≤ v → ‖feeAt R N per b' M a‖≤day:=by
    intro a lo hi ear reached earlier
    obtain ⟨s,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (show a≠0 by dsimp [v] at lo; omega)
    exact WilsonMovingForkChronologicalSale.original prog N per w ξ simple hk D Q π Γ Ψ books ahead
      reached earlier (earlier.trans lo) hi top.le (mounts _ lo hi.le) (mounts _ (Nat.le_succ_of_le lo) hi)
      (grants s lo hi)
  have bottom:=WilsonMovingForkTerminalFile.original (per:=per) old sheets arms top.le ((stop.upper h).trans_lt ck) cut moved
  have retired:‖reading R (N:=N) (numerator R N per v (M v)) v le_rfl-I‖≤bill.terminal:=by
    change ‖_-I‖≤0
    change reading R (N:=N) (numerator R N per v (M v)) v le_rfl=I at bottom
    rw [bottom,sub_self,norm_zero]
  obtain ⟨uv,later⟩:=WilsonMovingForkCapturedPrint.original old prog arms X band stop cut goal h issued
    N per (ck.trans top) ck moved hs dep oc slots fit fund fare wage atZero ou ov deep I bill hired
      (fun i hi=>edge i ((stop.upper h).trans (mem_Ico.mp hi).1) (mem_Ico.mp hi).2 u le_rfl issued.1)
      (fun i hi=>edge i (mem_Ico.mp hi).1 ((mem_Ico.mp hi).2.trans ck) v issued.1 le_rfl)
      retired (le_refl _)
  obtain ⟨integral,fine,across,coarse,terminal⟩:=later
  exact ⟨integral,entryFee,fine,across,coarse,terminal⟩

end YM.Integration.WilsonMovingForkDatedInvoice
