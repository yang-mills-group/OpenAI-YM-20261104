import YM.Integration.WilsonAllDateHarvestFunding
import YM.Integration.WilsonReportHarvestReplayEntries
import YM.Integration.WilsonReportHarvestUpperRange

/-! The original funded marked course at every retained upper date, with both signed ledgers paid through the preceding dates. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportHarvestReplayPhysical
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar
open RG12
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
universe u
variable {G : Gauge} (R : Run G) (simple : G.Simple) {T : Campaign R} (W : Campaign.Pillars R T)
    {δ : ℝ} (fund : FundedOriginalProperties.{u} simple δ W)
    (book : OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
    (portfolio : Funding R) (slow : WilsonWindowReportingPace.Slow R.kit)

/-- The exact same restricted physical field and signed old arrays used by
the lower marked replay. The division is by the running unmarked density. -/
def Retained (R:Run G) {b m i N per:ℕ} (bm:b ≤ m) (mi:m ≤ i) (iN:i ≤ N)
    (s:Fin 3→ℕ)(S:(v:Fin 3)→Emblems R.family (s v))(P:(v:Fin 3)→Sight R.family (s v) per)
    (x:(v:Fin 3)→Palette R.family (s v))(o:Fin 3→Site (R.family.side b per))
    (E:Fin 3→Motion)(q:ManyStem R.family o b→Body)(roster:Census (Fin 3))(d k:ℕ)(Q δ:ℝ):Prop :=
  let C:=R.family
  let Y:=C.path.rep N per
  let A:=Mine.tree o E
  let J:=Mine.masts o E bm (barren o E roster m) i
  let inc:=WilsonAllDateHarvestBoard.admitted o E roster bm mi
  let f:=WilsonAllDateHarvestPhysical.columns o E s q S x m N i
  let X:=birth (Mine.ward o E roster i) (Y N) f
  let Z:=fun U=>narrow inc (gust C.path N per N X i iN U)
  let rows:=imprint R.makes A (headings o E q) (plants (m:=m) s P S x) i iN
  let α:=(C.path.levels.budget i).supportExponent
  Integrable X (prior G _) ∧
    MenuBoard (Y i) rows Z (A.supportX i) (fun _:ManyStem C o i=>Many.envelope C m (d+1) k Q i) α 1 ∧
    (∀U,(Z U).part J.quiet=(Y i).eval U ∧ ∀v,(Z U).part (J.fire v)=(rows v).1 U) ∧
    (∀U,∀v:J.Mode,((Y i).eval U:ℂ)⁻¹*(Z U).part v=
      actualTransport C (N:=N) (fun V=>∏a∈v.val,f a V) iN U) ∧
    ∃H K,Carton (A.supportX i) H K (Y i).p.threshold ∧
      Z=restore (Y i) (fun v=>(rows v).2.1) (fun v=>profile (Y i).activities (rows v).2.2) H K ∧
      Towed (fun _:ManyStem C o i=>(1:ℝ)) id H (Y i).p.B (α-1) δ ∧
      Towed (fun _:ManyStem C o i=>(1:ℝ)) (fun v:Box (C.side i per)=>v.1) K (Y i).p.B (α-1) δ

def allowance (R:Run G)(m N d h:ℕ):ℝ:=
  (R.family.path.levels.clock.hatBeta m)^h*WilsonReportHarvestUpperRange.factor R.family.S d m N

def amount (R:Run G)(b m i N per p engineering reserve:ℕ)(ε:ℝ):ℝ:=
  ε*((Real.sqrt (R.family.path.rep N per i).beta)⁻¹)^p /
    (R.family.S.a m/R.family.S.a i)^engineering/(R.family.path.levels.clock.hatBeta i)^(reserve*(i-b+1))

local notation "C" => R.family

include W fund book slow in
theorem original (d:ℕ){ε:ℝ}(ep:0<ε):
    ∃k:ℕ,∀p h engineering reserve berth:ℕ,∀ᶠ b:ℕ in atTop,∀m:ℕ,∀bm:b ≤ m,
      ((m-b:ℕ):ℝ) ≤ (berth:ℝ)*(1+Real.log (WilsonMeasuredAdmission.mast (C).path.levels m)) →
      ∀u≥m,∀per:ℕ,∀s:Fin 3→ℕ,(∀v,s v ≤ d) →
      let N:=u+1
      let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
      let Q:=allowance R m N d h
      ∃P:(v:Fin 3)→Sight C (s v) per,
        (∀v,Spine R.doors portfolio.allowance R.makes b per (s v) N (P v) (S v)) ∧
        ∀(x:(v:Fin 3)→Palette C (s v)),(∀v,size (x v) ≤ Q) →
        ∀(o:Fin 3→Site ((C).side b per))(E:Fin 3→Motion)(q:ManyStem C o b→Body)(roster:Census (Fin 3)),
        (∀v:ManyStem C o b,Cap (s v.val.1+2) (q v) 1) →
        ∀i:ℕ,∀mi:m ≤ i,∀iu:i ≤ u,WilsonReportHarvestUpperRange.eligible (C).S m i u →
        Retained R bm mi (Nat.le_succ_of_le iu) s S P x o E q roster d k Q (amount R b m i N per p engineering reserve ε) := by
  obtain ⟨k,fundDates⟩:=WilsonAllDateHarvestFunding.original R simple W fund book portfolio slow d ep
  refine ⟨k,?_⟩
  intro p h engineering reserve berth
  obtain ⟨start,terms⟩:=eventually_atTop.mp (WilsonReportHarvestReplayEntries.original R simple p k h engineering
    (2*(d+2)) (2*(d+2)) reserve berth ep)
  obtain ⟨age,upper⟩:=eventually_atTop.mp (WilsonReportHarvestUpperRange.original R simple d h)
  filter_upwards [fundDates,eventually_ge_atTop start,eventually_ge_atTop age] with b booked sb ab
  intro m bm earlier u mu per s degree N S Q
  have mN:m ≤ N:=Nat.le_succ_of_le mu
  obtain ⟨P,spine,grant⟩:=booked m bm N mN per s degree
  refine ⟨P,spine,?_⟩
  intro x sizes o E q roster cap i mi iu eligible
  have live:i<N:=Nat.lt_succ_of_le iu
  obtain ⟨one,ceiling,_⟩:=upper m (ab.trans bm) u mu i mi iu eligible
  have qp:0<Q:=mul_pos (pow_pos (zero_lt_one.trans ((C).path.levels.fits.delayed m)) h) (zero_lt_one.trans_le one)
  obtain ⟨integral,board,mixed,_⟩:=grant o E q x roster (fun _=>Q) cap sizes (fun _=>qp) i mi live.le
  unfold Retained
  dsimp only
  refine ⟨integral,?_,fun U=>board.check (R.makes.wilson.represents N per i live.le).good.labels U,mixed,?_⟩
  · simpa only [if_neg live.ne] using board
  · exact terms m (sb.trans bm) i mi N live per (d+1) b bm earlier o E roster (fun _=>Q) _ _
      (WilsonReportHarvestUpperRange.factor (C).S d m N) one ceiling (fun _=>qp) (fun _=>le_rfl)
      (by simpa only [if_neg live.ne] using board)

end YM.Integration.WilsonReportHarvestReplayPhysical
