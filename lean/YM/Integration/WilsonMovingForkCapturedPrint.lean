import YM.Integration.WilsonMovingForkMountedStage
import YM.Integration.WilsonMovingForkPrintedFile

/-! At a common capture with all actual parents zero, the two-stop
purchase applies directly to the prescribed ordinary copies. The same
previously fitted matrix still pays for the original upper. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.Integration.WilsonMovingForkCapturedPrint
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
  (old:Filed R d K)(programme:Program R d K)(arms:∀a,Arm R.family S (l:Filter _) (d a) (x a))
  (X:XSpace.Run){stage u depth:ℕ}(band:Band R X stage)(stop:WilsonIndependentCapturedPages.Stop R X band u depth)
  {j:ℕ}(cut:j ≤ K)(goal h:ℕ)(issued:WilsonMovingForkMountedStage.Paid R X band stop goal h)
local notation "c" => band.reporter+h
local notation "C" => R.family

include issued in
theorem original (N per:ℕ)(live:c<N)(ck:c<K)(o:Fin n → Cover):
    let rep:=(C).path.rep N per c
    let g:=regulatorRun (C) N per c
    let w:=doses R d old.station (N:=N) (per:=per) (old.A N per) (fun a=>(arms a).source (N,per))
    let ξ:=WilsonMovingForkSeededPoint.seats (R:=R) cut per o
    let b:=programme N per w ξ c ck
    let M:=WilsonMovingForkCapturedFee.word (registered old programme) arms cut o (N,per)
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
      ∀(I:ℂ)(bill:WilsonMovingForkHeterogeneousCut.Invoice),
        (∀i,stop.date h ≤ i → i ≤ K → Integrable (numerator R N per i (M i)) (prior G _)) → 
        (∀i∈Finset.Ico c K,‖feeAt R N per u M i‖ ≤ bill.fine i) → 
        (∀i∈Finset.Ico (stop.date h) c,‖feeAt R N per (stop.date h) M i‖ ≤ bill.coarse i) → 
        ‖reading R (N:=N) (numerator R N per (stop.date h) (M (stop.date h))) (stop.date h) le_rfl-I‖ ≤ bill.terminal → 
        bill₀*g^goal ≤ bill.across → ∃uv:u ≤ stop.date h,Later (registered old programme) arms cut uv
          (stop.upper h) o (N,per) I bill:=by
  intro rep g w ξ b M ord seats shelf ext stripU slack gross hs dep oc slots fit fund fare wage atZero ou ov deep
    unitGross e bill₀ I bill hired fine coarse bottom estate
  obtain ⟨uv,paid⟩:=issued
  let Z:Support ((C).side c per):={0}
  have root:0∈Z:=Finset.mem_singleton_self _
  have housed:∀a∈(allSlots n).val,parent R ck.le per ξ a∈Z:=by
    intro a _
    rw [atZero a]
    exact root
  have near:∀a∈(allSlots n).val,separation (parent R ck.le per ξ a) 0 ≤ 0:=by
    intro a _
    rw [atZero a]
    simp
  refine ⟨uv,?_⟩
  exact paid N per live b.binder b.load b.copies hs dep oc (by simpa using slots) fit fund fare wage
    (allSlots n) Z root housed 0 near (Nat.zero_le _) (halo_subset _ _) (le_refl _) ou ov deep
    b.wallet (registered old programme) arms cut o I bill
    (WilsonMovingForkPrintedFile.original old programme arms cut ck o (N,per)) hired fine coarse bottom estate

end YM.Integration.WilsonMovingForkCapturedPrint
