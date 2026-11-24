import YM.Integration.QLocalThermalPacketActivity
import YM.Integration.QlocalMarkedPrimaryProposal
import YM.Integration.LocalComparisonFunctionalRetains

/-! Use one ordinary numbering for the measured field, the emitted model
and its signed residual. Every genuine old address survives the reindex. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalMeasuredAlignment

open Function Finset Lattice Wilson RG Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal Comparison.Density.RenderM
open WilsonLimitConstruction WilsonLimitConstruction.FundedMarkedSoftRows WilsonLimitConstruction.FundedMarkedFieldSplit
open scoped Classical BigOperators

variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V}
    {X:Type} {n:Side} {P:Rep G n} {o:V→Site n}

def empty (L:Rows X Γ G n) : Rows X Γ G n:={L with value:=fun _ _ _=>0}

omit [Fintype V] in
theorem empty_sum (L:Rows X Γ G n) (p:BudgetPoint) (x:X) (U:Config G n) :
    HasSum (wave (empty L) p x U) 0 := by
  have z:wave (empty L) p x U=0:=by
    funext i
    by_cases h:Healthy p.threshold (L.site i) U <;> simp [empty,wave,masked,h]
  rw [z]
  exact hasSum_zero

theorem log (T:Taste X o P Γ) (L:Rows X Γ G n) (x:X) (U:Config G n)
    (has:Summable (fun i=>(T.leaf x).contents.ray i U)) :
    ((append (empty L) T).leaf x).log U=(T.leaf x).log U := by
  simpa only [add_zero] using FundedMarkedSoftRows.log (empty L) T x U has (empty_sum L P.p x U)

theorem density (T:Taste X o P Γ) (L:Rows X Γ G n) (x:X) (U:Config G n)
    (has:Summable (fun i=>(T.leaf x).contents.ray i U)) :
    ((append (empty L) T).leaf x).density U=(T.leaf x).density U := by
  simp only [RG3.Forms.Deck.density,log T L x U has,FundedMarkedSoftRows.cluster]

variable {C:Family G} {D:V→ ComparisonDensity.Address.Orbit} {N t m:ℕ}
    {f:V→Site (C.side (m+1) t)} {c:V→Site (C.side m t)} {Q:PhysicalCarrier C N t (m+1)}
    {input:Taste (TestSpace D) f Q.rep Γ} (H:FundedPhysicalMarkedClosure.Measured c input)
    (M:MarkedPackets D G (C.side m t) Γ)
variable (S:Invoice H.output (vacuumRemainder H.output) (fun x U=>M.read x (Pert.Asymptotics.regulatorRun C N t (m+1)) U))
    (gas:∀U,Summable (fun a:Finset ℕ=>‖H.carrier.rep.activities.gasOccurrence H.carrier.rep.p a U‖))

include H M S gas in
def produced : ProducedOutput D Q f c input := by
  let old : ProducedOutput D Q f c input := QLocalThermalMeasuredPackets.produced
    (C:=C) (D:=D) (Γ:=Γ) (N:=N) (t:=t) (m:=m) (o:=f) (c:=c) (Q:=Q) (input:=input) H M gas S
  refine {old with output:=append (empty S.soft) H.output,density:=?_,full:=?_,regular_log:=?_}
  · intro x
    rw [H.density]
    exact funext fun U=>(density H.output S.soft x U (S.formal_sum x U)).symm
  · intro x U
    exact (density H.output S.soft x U (S.formal_sum x U)).trans (old.full x U)
  · intro x U
    exact (log H.output S.soft x U (S.formal_sum x U)).trans (old.regular_log x U)

theorem aligned :
    let O:=produced H M S gas
    QlocalMarkedPrimaryProposal.AlignedRegularRows O.output O.formalAligned O.residual := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · intro x i U
    obtain ⟨j,rfl⟩:=Equiv.natSumNatEquivNat.surjective i
    cases j with
    | inl k=>simp [produced,QLocalThermalMeasuredPackets.produced,realize,append,replace,vacuumRemainder]
    | inr k=>simp [produced,QLocalThermalMeasuredPackets.produced,realize,append,replace,negative,empty]
  · intro x v
    change H.output.menu.global x v=0+H.output.menu.global x v
    rw [zero_add]
  · intro x i
    change H.output.score x i=0+H.output.score x i
    rw [zero_add]

theorem elected (K:Guard.Keeper H.carrier.rep.p H.carrier.rep.activities) {p:BudgetPoint}
    {a:V→Support (C.side m t)} {region:Comparison.Density.Testing.Region (fun v=>(D v).Mood) (C.side m t)}
    {w:V→ℝ} {width amount:ℝ} {off cov:ℕ} (paid:M.Paid p a region w (Pert.Asymptotics.regulatorRun C N t (m+1)) width amount off cov)
    (hg:(Pert.Asymptotics.regulatorRun C N t (m+1))≠0) (point:∀v,c v∈a v) {e k:ℝ} (good:H.carrier.rep.activities.Valid H.carrier.rep.p e k)
    (active:∀x,(H.output.leaf x).Active) (fare:∀x,∃u v b d,(H.output.menu.terms x).Radial w u v b d) :
    ∃O:ProducedOutput D Q f c input, O.carrier=H.carrier ∧ O.model=M ∧
      (∀x U,(O.output.leaf x).density U=(H.output.leaf x).density U) ∧
      QlocalMarkedPrimaryProposal.AlignedRegularRows O.output O.formalAligned O.residual ∧
      (∀x,(O.output.leaf x).Active) ∧ (∀x,(O.formalAligned.leaf x).Active) ∧ (∀x,(O.residual.leaf x).Active) ∧
      FunctionalRetains O.output (fun v=>{c v}) ∧ FunctionalRetains O.formalAligned (fun v=>{c v}) ∧
      FunctionalRetains O.residual (fun v=>{c v}) := by
  obtain ⟨sale,chosen⟩:=QLocalThermalJoinedInvoice.invoice_rows M K paid hg point H.output (vacuumRemainder H.output)
    good active (fun x=>vacuumRemainder_active H.output x (active x) x) fare
    (fun x=>⟨0,0,0,1,QLocalThermalMeasuredPackets.vacuum_radial H.output paid.positive x⟩)
  let order:= (Activities.gasSeries good).absolute
  let O:=produced H M sale order
  have pieces x:=QLocalThermalPacketActivity.realized M paid point H.output (vacuumRemainder H.output) sale chosen x
  have formal (x): (O.formalAligned.leaf x).Active:=(pieces x).2
  have rest (x): (O.residual.leaf x).Active:=(pieces x).1
  have live (x): (O.output.leaf x).Active:=by
    let rows:=QLocalThermalPacketActivity.rows (Q:=H.carrier.rep) M paid (H.output.menu.rays 0) ((active x).articles.proper 0) point
    apply FundedMarkedSoftRows.active (empty sale.soft) H.output x (active x)
    · simpa only [empty,chosen] using rows.1
    · simpa only [empty,chosen,H.output.root] using rows.2.1
    · exact fun i=>(regular0 H.carrier.rep.p (sale.soft.site i) (0:Site (C.side m t))).1
  exact ⟨O,rfl,rfl,(fun x U=>density H.output sale.soft x U (sale.formal_sum x U)),aligned H M sale order,
    live,formal,rest,FunctionalRetains.of_active live,FunctionalRetains.of_active formal,FunctionalRetains.of_active rest⟩

end YM.Integration.QLocalThermalMeasuredAlignment
