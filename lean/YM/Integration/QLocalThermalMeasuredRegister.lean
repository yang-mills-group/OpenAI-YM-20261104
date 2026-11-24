import YM.Integration.QLocalThermalMeasuredAlignment

/-! One measured all-field packet placement carries its independent
source laws, common ordinary addresses and complete compulsory expenses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalThermalMeasuredRegister

open Function Finset Lattice Wilson RG Marker Overlay Extra.Histories Planned.GuardedAtom
open RG3.Held RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal Comparison.Density.RenderM
open WilsonLimitConstruction WilsonLimitConstruction.FundedMarkedSoftRows WilsonLimitConstruction.FundedMarkedFieldSplit
open QLocalThermalJoinedForcedRegister QLocalThermalJoinedRate ActualWilsonDirtyPartners
open scoped Classical BigOperators

variable {G:Gauge} {V:Type} [Fintype V] [DecidableEq V] {Γ:Census V}
    {D:V→ ComparisonDensity.Address.Orbit} {n:Side} {P:Rep G n} {o:V→Site n}
local notation "Moods" => (fun v:V=> ComparisonDensity.Address.Orbit.Mood (D v))

def Typed (L:Rows (TestSpace D) Γ G n):Prop:=∀i U,Letter ℂ Moods (L.mode i).val (fun x=>L.value x i U)

omit [Fintype V] in
theorem original (M:MarkedPackets D G n Γ) {p:BudgetPoint} {a:V→Support n}
    {region:Comparison.Density.Testing.Region Moods n} {w:V→ℝ} {g width b:ℝ} {off cov:ℕ}
    (h:M.Paid p a region w g width b off cov) (fill:Γ.Mode) : Typed (QLocalThermalPacketRebooking.regular M fill g) := by
  intro i U
  cases hi:M.packet i with
  | none=>
    simp only [QLocalThermalPacketRebooking.regular,MarkedPackets.term,hi,Option.isSome_none]
    convert (Letter.still (K:=ℂ) (T:=Moods) (s:=fill.val) (E:=ℂ)) using 1
    all_goals rfl
  | some tok=>simpa [QLocalThermalPacketRebooking.regular,hi] using h.term_letter i U

omit [Fintype V] in
theorem appended (T:Taste (TestSpace D) o P Γ) (L:Rows (TestSpace D) Γ G n)
    (h:Multilinear D T) (line:Typed L) : Multilinear D (append L T) := by
  refine ⟨?_,h.forced,h.unit,h.captions⟩
  intro i U
  obtain ⟨j,rfl⟩:=Equiv.natSumNatEquivNat.surjective i
  cases j with
  | inl k=>simpa [append] using h.regular k U
  | inr k=>simpa [append] using line k U

omit [Fintype V] in
theorem vacuum (T:Taste (TestSpace D) o P Γ) : Multilinear D (vacuumRemainder T) :=
  ⟨fun _ _=>Letter.still,fun _ _ _=>Letter.still,fun _=>Letter.still,fun _=>Letter.still⟩

variable {C:Family G} {N t m:ℕ} {f:V→Site (C.side (m+1) t)} {c:V→Site (C.side m t)}
    {Q:PhysicalCarrier C N t (m+1)} {input:Taste (TestSpace D) f Q.rep Γ}
    (H:FundedPhysicalMarkedClosure.Measured c input) (M:MarkedPackets D G (C.side m t) Γ)
local notation "g₀" => Pert.Asymptotics.regulatorRun C N t (m+1)

structure Receipt (p:BudgetPoint) (w:V→ℝ) (κ b b' b₀:ℝ) where
  output : ProducedOutput D Q f c input
  carrier : output.carrier=H.carrier
  model : output.model=M
  measured x U : (output.output.leaf x).density U=(H.output.leaf x).density U
  active x : (output.output.leaf x).Active ∧ (output.formalAligned.leaf x).Active ∧ (output.residual.leaf x).Active
  linear : Multilinear D output.output ∧ Multilinear D output.formalAligned ∧ Multilinear D output.residual
  rows : QlocalMarkedPrimaryProposal.AlignedRegularRows output.output output.formalAligned output.residual
  retained : FunctionalRetains output.output (fun v=>{c v}) ∧ FunctionalRetains output.formalAligned (fun v=>{c v}) ∧
    FunctionalRetains output.residual (fun v=>{c v})
  actual_forced : ForcedBudget p (pullback (testInclusion D) output.output) w κ b₀
  model_forced : ForcedBudget p (pullback (testInclusion D) output.formalAligned) w κ b'
  residual_forced : ForcedBudget p (pullback (testInclusion D) output.residual) w κ b

theorem issued (K:Guard.Keeper H.carrier.rep.p H.carrier.rep.activities) {p:BudgetPoint} {a:V→Support (C.side m t)}
    {region:Comparison.Density.Testing.Region Moods (C.side m t)} {w:V→ℝ} {width amount:ℝ} {off cov:ℕ}
    (paid:M.Paid p a region w (g₀) width amount off cov) (np:0≤amount) (hg:(g₀)≠0)
    (point:∀v,c v∈a v) {e k k₀ κ b:ℝ} (good:H.carrier.rep.activities.Valid H.carrier.rep.p e k₀)
    (live:∀x,(H.output.leaf x).Active) (fare:∀x,∃u v b d,(H.output.menu.terms x).Radial w u v b d)
    (hκ:0<κ) (bound:H.carrier.rep.activities.KBound p k) (prior:ForcedBudget p (pullback (testInclusion D) H.output) w κ b)
    (thermal:2*(k+(Fintype.card V:ℝ)*(κ*b))*blockSites p.B≤(3*p.supportExponent)/2)
    (empty:2*k*blockSites p.B≤(3*p.supportExponent)/2)
    (room:2*(Fintype.card V:ℝ)*(Fintype.card Γ.Mode:ℝ)*charge M p off amount≤1) (letters:Multilinear D H.output) :
    Nonempty (Receipt H M p w κ (b+increase M p off amount κ k b) (increase M p off amount κ k 0) b) := by
  let B:=vacuumRemainder_fullBudget H.output (fun _=>0) (live (fun _=>0)) (testInclusion D) p w κ paid.positive hκ
  let zero:ForcedBudget p (pullback (testInclusion D) (vacuumRemainder H.output)) w κ 0:=
    ⟨B.black,B.black_nonnegative,B.forced,B.forcedTotal⟩
  obtain ⟨S,rows,lf,le,⟨fa⟩,⟨fb⟩⟩:=QLocalThermalFundedFieldSplit.issued_letters M K paid np hg point H.output
    (vacuumRemainder H.output) good live (fun x=>vacuumRemainder_active H.output x (live x) x) fare
    (fun x=>⟨0,0,0,1,QLocalThermalMeasuredPackets.vacuum_radial H.output paid.positive x⟩)
    hκ bound prior zero thermal (by simpa only [mul_zero,add_zero] using empty) room
  let gas:= (Activities.gasSeries good).absolute
  let O:=QLocalThermalMeasuredAlignment.produced H M S gas
  have forms x:=QLocalThermalPacketActivity.realized M paid point H.output (vacuumRemainder H.output) S rows x
  have f x:(O.formalAligned.leaf x).Active:=(forms x).2
  have r x:(O.residual.leaf x).Active:=(forms x).1
  have o x:(O.output.leaf x).Active:=by
    let data:=QLocalThermalPacketActivity.rows (Q:=H.carrier.rep) M paid (H.output.menu.rays 0) ((live x).articles.proper 0) point
    apply FundedMarkedSoftRows.active (QLocalThermalMeasuredAlignment.empty S.soft) H.output x (live x)
    · simpa only [QLocalThermalMeasuredAlignment.empty,rows] using data.1
    · simpa only [QLocalThermalMeasuredAlignment.empty,rows,H.output.root] using data.2.1
    · exact fun i=>(regular0 H.carrier.rep.p (S.soft.site i) (0:Site (C.side m t))).1
  have L:Typed S.soft:=by rw [rows];exact original M paid _
  have neg:Typed (negative S.soft):=fun i U=>(L i U).neg
  exact ⟨{
    output:=O
    carrier:=rfl
    model:=rfl
    measured:=fun x U=>QLocalThermalMeasuredAlignment.density H.output S.soft x U (S.formal_sum x U)
    active:=fun x=>⟨o x,f x,r x⟩
    rows:=QLocalThermalMeasuredAlignment.aligned H M S gas
    retained:=⟨FunctionalRetains.of_active o,FunctionalRetains.of_active f,FunctionalRetains.of_active r⟩
    linear:=⟨appended _ _ letters (fun _ _=>Letter.still),appended _ _ (le (vacuum H.output)) L,appended _ _ (lf letters) neg⟩
    actual_forced:=QLocalThermalMeasuredPackets.appended p _ _ _ prior
    model_forced:=by
      change ForcedBudget p (pullback (testInclusion D)
        (append S.soft (replace (vacuumRemainder H.output) S.residualForced))) w κ
        (increase M p off amount κ k 0)
      simpa only [zero_add] using QLocalThermalMeasuredPackets.appended p _ S.soft _ fb
    residual_forced:=QLocalThermalMeasuredPackets.appended p _ (negative S.soft) _ fa}⟩

end YM.Integration.QLocalThermalMeasuredRegister
