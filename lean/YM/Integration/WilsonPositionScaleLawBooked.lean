import YM.Integration.WilsonPhysicalPositionBookedBranch
import YM.Integration.WilsonPositionScaleLawCompactAll

/-! One filed original-cutoff signed scalar, at the pre-elected two books and
on their common actual reporter, selects the branch for every compact-window
same-home estimate at all perturbative orders. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawBooked
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPhysicalPositionBookedBranch (home Admitted station)
open WilsonPhysicalPositionDirectedPins (cutoff)
open WilsonPhysicalPositionDirectedTest (baseline)
open scoped Topology Classical Asymptotics
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)

theorem raw [W:RangeSpec](d:ℕ)(h:WilsonPhysicalPositionHalfRange.uniform J d W.left):
    WilsonPositionScaleLawCompactBranch.Raw J d:=by
  let X:=(Bel R.family.book).Field d
  letI : NormedAddCommGroup (X→L[ℂ]X):=ContinuousLinearMap.toNormedAddCommGroup
  unfold WilsonPositionScaleLawCompactBranch.Raw
  apply Metric.tendsto_nhds.mpr
  intro ε he
  filter_upwards [(tendsto_fst (f:=trail) (g:=(⊤:Filter Ratio))).eventually (h ε he)] with z hz
  rw [dist_eq_norm]
  exact hz z.2.val z.2.property (WilsonPositionScaleLawCompactNative.positive z.2)

variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {ℓ:Ultrafilter (ℕ×ℕ)}{Y:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}{δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→WilsonOriginalTwoFlatPublicBooks.Book F (l:=ℓ) Y arch D T s.val)

def filed (k:Fin (D+1))(avoid:Finset E4)(v:(Bel R.family.book).Field k.val)(a:ℝ):Prop:=
  ∀ᶠr in trail,∀t,∀h:Admitted δ r t,∀ᶠz in (ℓ:Filter (ℕ×ℕ)),baseline v-a≤
    cutoff F J k r t (fun i=>books (home h i)) v avoid (station (δ:=δ) F books r t) z

include H in
theorem original (bliss:Bliss F ℓ arch Y)(slow:WilsonWindowReportingPace.Slow R.kit)
    (δp:0<δ)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)
    (paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(k:Fin (D+1))(avoid:Finset E4):
    ∃v:(Bel R.family.book).Field k.val,WilsonPhysicalPositionAdmissible.real R.family k.val v=v ∧ ∃a:ℝ,0<a ∧
      (filed F J books k avoid v a→∀c:ℝ,∀hc:0<c,∀q:ℕ,WilsonPositionScaleLawCompactAll.window Z M ν F J ⟨c,hc⟩ k.val q):=by
  obtain ⟨v,hv,a,ha,choose⟩:=WilsonPhysicalPositionBookedBranch.original F J books hG bliss slow δp below lead Z.store k avoid
  refine ⟨v,hv,a,ha,?_⟩
  intro vote c hc q
  letI :RangeSpec:=⟨c,hc⟩
  have paidRaw:=raw J k.val (choose vote c hc)
  exact ⟨WilsonPositionScaleLawCompactJacobian.original F J Z.store lead k.val paidRaw,
    WilsonPositionScaleLawCompactQinter.original Z M H ν F J lead paid k.val q paidRaw,
    WilsonPositionScaleLawCompactQinter.qinter Z M H ν F J lead paid k.val q paidRaw⟩

end YM.Integration.WilsonPositionScaleLawBooked
end
