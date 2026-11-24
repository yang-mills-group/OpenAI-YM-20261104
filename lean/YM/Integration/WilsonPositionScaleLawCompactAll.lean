import YM.Integration.WilsonPositionScaleLawCompactQinter

/-! One pre-elected directed physical measurement before all ratio windows and
positive orders. On each window the Jacobian and its inverse are quantitative,
and only the measured same-home signed purse remains in the error. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawCompactAll
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPositionScaleLawCompactNative (exactOp)
open WilsonPositionScaleLawCompactJacobian (derivative)
open WilsonPositionScaleLawCompactQinter (prediction measured)
open WilsonPositionScaleLawKinetic (kinetic)
open scoped Topology Classical Asymptotics
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)

def window (W:RangeSpec)(d q:ℕ):Prop:=
  letI : RangeSpec:=W
  (Tendsto (derivative F J Z.store d) sweep (𝓝 1) ∧
    (∀ᶠz in sweep,(derivative F J Z.store d z).IsInvertible) ∧
    Tendsto (fun z=>(derivative F J Z.store d z).inverse) sweep (𝓝 1)) ∧
  (∃L A:ℝ,0≤L ∧ 0≤A ∧ ∀ᶠz in sweep,
    ‖exactOp F J Z.store d z-prediction Z M ν F J d q z‖≤L*‖measured Z M ν F J d q z‖+A*|kinetic Z F J z.1|^(q+1)) ∧
  ((measured Z M ν F J d q)=o[sweep] (fun z=>kinetic Z F J z.1^q)→
    (fun z=>exactOp F J Z.store d z-prediction Z M ν F J d q z)=o[sweep] (fun z=>kinetic Z F J z.1^q))

include H in
theorem original (lead:Leading F J){Y:(Bel R.family.book).Hierarchy}
    (paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(d:ℕ):
    ∃v:(Bel R.family.book).Field d,WilsonPhysicalPositionAdmissible.real R.family d v=v ∧ ∃a:ℝ,0<a ∧
      ((∀ᶠr in trail,∀t∈Icc (1/2:ℝ) 1,WilsonPhysicalPositionDirectedTest.baseline v-a≤
        WilsonPhysicalPositionDirectedReturn.cross F J v r t)→
        ∀c:ℝ,∀hc:0<c,∀q:ℕ,window Z M ν F J ⟨c,hc⟩ d q):=by
  obtain ⟨v,hv,a,ha,choice⟩:=WilsonPositionScaleLawCompactBranch.selected F J Z.store lead d
  refine ⟨v,hv,a,ha,?_⟩
  intro tested c hc q
  letI W:RangeSpec:=⟨c,hc⟩
  have raw:=choice tested W
  exact ⟨WilsonPositionScaleLawCompactJacobian.original F J Z.store lead d raw,
    WilsonPositionScaleLawCompactQinter.original Z M H ν F J lead paid d q raw,
    WilsonPositionScaleLawCompactQinter.qinter Z M H ν F J lead paid d q raw⟩

end YM.Integration.WilsonPositionScaleLawCompactAll
end
