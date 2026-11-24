import YM.Integration.WilsonAllDateHarvestRadii
import YM.Integration.WilsonAllDateHarvestObservables
import YM.Integration.WilsonMarkedUltravioletSourceRatios

/-! The actual common palette stock on the financed three-insertion run pays
the Wilson mixed-source representation and its per-insertion radius ratios
on one eventual tail, before all upper cutoffs, periods, sites and input fees. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonAllDateHarvestFunding
open Function Filter Finset Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof Accent Menu Marker
open RG05Readout RG05Readout.Address RG05Readout.Native RG05Readout.Many RG05Readout.View RG05Readout.Records
open Bid Pressure Copper Ac GridApprox.Nil Extra.Trajectories Extra.Multi
open PhysicalNext PhysicalNext.Repeat Lotus Legato Bandage Next.Rank.Station WilsonLimitConstruction
open WilsonCloseCaptureCalendar
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
universe u
variable {G:Gauge} (R:Run G) (simple:G.Simple) {T:Campaign R} (W:Campaign.Pillars R T)
    {δ:ℝ} (fund:FundedOriginalProperties.{u} simple δ W)
    (book:OPE.Package R.family R.w (mutt R.family.path.levels R.Q) R.doors)
    (portfolio:Funding R) (slow:WilsonWindowReportingPace.Slow R.kit)
local notation "C" => R.family

include W fund book slow in
theorem original (d:ℕ) {ε:ℝ} (ep:0<ε):
    ∃k:ℕ,∀ᶠ n:ℕ in atTop,∀m:ℕ,∀nm:n ≤ m,∀N:ℕ,∀_:m ≤ N,∀per:ℕ,∀s:Fin 3→ℕ,
      (∀v,s v ≤ d)→
      let S:=fun v:Fin 3=>portfolio.basis (s v) (N,per)
      ∃P:(v:Fin 3)→Sight C (s v) per,
      (∀v,Spine R.doors portfolio.allowance R.makes n per (s v) N (P v) (S v)) ∧
      ∀(o:Fin 3→Site ((C).side n per))(E:Fin 3→Motion)(q:ManyStem C o n→Body)
        (x:(v:Fin 3)→Palette C (s v))(roster:Census (Fin 3))(Q:Fin 3→ℝ),
      (∀j:ManyStem C o n,Cap (s j.val.1+2) (q j) 1)→(∀v,size (x v) ≤ Q v)→(∀v,0<Q v)→
      ∀i:ℕ,∀mi:m ≤ i,∀iN:i ≤ N,
        let Y:=(C).path.rep N per
        let A:=Mine.tree o E
        let inc:=WilsonAllDateHarvestBoard.admitted o E roster nm mi
        let f:=WilsonAllDateHarvestPhysical.columns o E s q S x m N i
        let X:=birth (Mine.ward o E roster i) (Y N) f
        let Z:=fun U=>narrow inc (gust (C).path N per N X i iN U)
        let rows:=imprint R.makes A (headings o E q) (plants (m:=m) s P S x) i iN
        let rad:=fun j:ManyStem C o i=>Many.envelope C m (d+1) k (Q j.val.1) i
        Integrable X (prior G _) ∧
        MenuBoard (Y i) rows Z (A.supportX i) rad
          (if i=N then ((C).path.levels.budget i).supportExponent-4 else ((C).path.levels.budget i).supportExponent) 1 ∧
        (∀U,∀v:(Mine.masts o E nm (barren o E roster m) i).Mode,(((Y i).eval U:ℂ)⁻¹)*(Z U).part v=
          actualTransport C (N:=N) (fun V=>∏j∈v.val,f j V) iN U) ∧
        ∀v:Fin 3, |Real.log (Many.envelope C m (d+1) k (Q v) i/Many.envelope C m (d+1) k (Q v) (i+1))|
            ≤ ε*((C).path.levels.budget i).B ∧ (i+1 ≤ N→
             |Real.log (WilsonMarkedUltravioletSourceRatios.radius C (Q v) (2*k) (d+1) m i (Y i).beta/
              WilsonMarkedUltravioletSourceRatios.radius C (Q v) (2*k) (d+1) m (i+1) (Y (i+1)).beta)|
                ≤ ε*((C).path.levels.budget i).B) :=by
  obtain ⟨stock,_⟩:=WilsonCloseCaptureFinances.original R simple W fund
  obtain ⟨k,warm⟩:=(portfolio.dates 0 0 d 0).2
  obtain ⟨cutoff,ratios⟩:=eventually_atTop.mp ((WilsonMarkedUltravioletSourceRatios.filed R simple slow k ep).and
    (WilsonMarkedUltravioletSourceRatios.original R simple slow (2*k) ep))
  let start:=∑e∈Finset.range (d+1),portfolio.start e
  refine ⟨k,?_⟩
  filter_upwards [warm,eventually_ge_atTop cutoff,eventually_ge_atTop start,
    (C).path.levels.fits.deep.eventually_ge_atTop 3] with n school room ready crowded
  intro m nm N mN per s deg S
  have earlier(v:Fin 3):portfolio.start (s v) ≤ n:=by
    apply le_trans _ ready
    exact Finset.single_le_sum (fun e _=>Nat.zero_le (portfolio.start e)) (Finset.mem_range.mpr (Nat.lt_succ_of_le (deg v)))
  let path:=fun v:Fin 3=>portfolio.rows.paid (N,per) (s v) ((earlier v).trans (nm.trans mN))
  let P:=fun v:Fin 3=>(path v).choose
  have basis(v:Fin 3):Spine R.doors portfolio.allowance R.makes n per (s v) N (P v) (S v):=
    Records.Spine.tail R.makes _ _ (path v).choose_spec (earlier v)
  refine ⟨P,basis,?_⟩
  intro o E q x roster Q cap pay qp i mi iN Y A inc f X Z rows rad
  have occ:Occupancy o ((C).path.levels.clock.J n):=by
    intro u
    exact (Finset.card_le_univ _).trans (by simpa using crowded)
  obtain ⟨hi,board⟩:=WilsonAllDateHarvestRadii.original o E s q R.makes book stock P S x roster Q
    basis nm mN occ cap pay qp school deg i mi iN
  have late:=ratios i (room.trans (nm.trans mi))
  exact ⟨hi,board,fun U v=>WilsonAllDateHarvestObservables.normalized iN f inc hi v U,
    fun v=>⟨late.1 m mi (d+1) (Q v) (qp v),fun next=>late.2 m mi (d+1) (Q v) (qp v) N next per⟩⟩

end YM.Integration.WilsonAllDateHarvestFunding
