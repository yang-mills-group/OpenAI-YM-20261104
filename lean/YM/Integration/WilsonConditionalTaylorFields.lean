import YM.Integration.WilsonConditionalTaylorFieldPurchase
import YM.Integration.FVA1Physical.Wilson.FluctuationOn

/-! The actual action-weighted Haar posterior of every pre-indexed finite Wilson
source, at every attained sufficiently late age of the same original trajectory. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorFields
open Function Filter Finset Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open PhysicalNext PhysicalNext.Repeat JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open PhysicalNext.Repeat.Legato Cub Circlet Graces Roost Qlocal.Schedule
open YM.Integration.FVA1Physical.Wilson RGComparison.Core16.Spool MSbar MSbar.Heath MSbar.Heath.Stock
open MSbar.Midpoint
open Tree Pressure Push.Uniform Exterior
open scoped Classical Topology BigOperators

open FVA1Physical.Round2.Curvature WilsonConditionalTaylorFieldPurchase WilsonConditionalTaylorCalendar
variable {G : Gauge} {I : ℕ → Type} [∀ t, Fintype (I t)]

/-- The sourced port only needs its previously purchased roster at later
blocks. Each pinned scene still determines its own forest and branch. -/
theorem ports (J : ∀ t, I t → Lamp G) (t : ℕ) (hG : G.Simple) (R : Run G)
    (u : G.ColorIndex) (V : Voice G) (fields : Due J u V R.kit)
    (invoice : Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    PinnedPorts (J t) R u V := by
  have docket:=(Qlocal.Schedule.docket_of_invoice hG R u V invoice).1
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hi
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hi).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  have merit:=townsR R.b R.Q R.T R.t R.stories R.doors ch
  have estate:=invoice.1 growth
  intro p s m L hs hm hr
  filter_upwards [docket.purse s p m hs hm hr, R.alloy.B.a.fits.deep.eventually_ge_atTop (max L (max s m)), R.alloy.B.a.fits.deep.eventually_ge_atTop t]
    with k uses ready seen N n start
  obtain ⟨someScene,allScenes⟩:=uses N n start
  refine ⟨someScene,?_⟩
  intro S scene j kj jN
  have prices:=allScenes S scene
  have cofinal:=ready.trans (R.alloy.B.a.fits.mono (show k ≤ j+1 by omega))
  have jobs:max s m ≤ R.alloy.B.a.clock.J (j+1):=(le_max_right ..).trans cofinal
  have collar:L ≤ R.alloy.B.a.clock.J (j+1):=(le_max_left ..).trans cofinal
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN hG estate.sees
    (fun k'=>invoice.2.1 _ _ (R.alloy.B.valid.pays k') _ (step_paid R.alloy.B.a k'))
  have touched:=(MSbar.Ballet.validP R.family.path R.T.choice merit.towns N n _ jN).1
  exact physical_field_step R.alloy.B u V N k j n p m s S scene _ _ season
    (floorsP R.T N n _ jN) (floorsP R.T N n _ jN.le)
    (prices.2.2 _ (by omega) jN) hs jobs touched kj jN (J t) L hG
    (fields t j n s p m L (seen.trans (R.alloy.B.a.fits.mono (show k ≤ j+1 by omega))) collar hs ((le_max_left ..).trans jobs) hm ((le_max_right ..).trans jobs) hr)
    estate.levy merit (prices.1 _ (by omega) jN)


/-- The numerical threshold and marked port suffice from a finite height onward;
the conclusion is the original uncut Wilson stencil, not a chart-only field. -/
theorem physical {β : Type} [Fintype β] (J : β → Lamp G) (hG : G.Simple) (R : Run G)
    (u : G.ColorIndex) (V : Voice G) (cle : Clear G V) (frame : R.metals.O=chart G)
    (threshold : ∀ᶠ j : ℕ in atTop, ∀ n, fluctuationMenu J V cle hG
      (R.family.path.levels.params j) (R.family.path.levels.params (j+1))
      (R.family.path.levels.clock.op j n).patch (R.family.path.levels.clock.op j n).kernel ≤
        R.family.path.levels.clock.hatBeta j)
    (allPorts : PinnedPorts J R u V)
    (invoice : Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    FluctuationReadings J R u := by
  obtain ⟨docket,_⟩:=docket_of_invoice hG R u V invoice
  obtain ⟨after,granted⟩ := eventually_atTop.mp threshold
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hj
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hj).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  intro p s L hs D η hD hη
  obtain ⟨d,hd⟩:=exists_nat_ge D
  obtain ⟨h,marg⟩:=margin_eventually hη
  let demand:=d+p+s+L+h
  let n₀:=p+2
  filter_upwards [allPorts n₀ s (n₀+4) L hs (by omega) (by omega),
    docket.purse s n₀ (n₀+4) hs (by omega) (by omega),eventually_ge_atTop (R.t demand),
    actual_clock_small R.family.path (q:=1) zero_lt_one zero_lt_one hG R.T.choice,eventually_ge_atTop after]
    with k loc budget menu unit late N n kN
  obtain ⟨existsScene,ports⟩:=loc N n kN
  refine ⟨existsScene,?_⟩
  intro S scene j kj jN
  let F:=(scene.step j jN kj).choose
  let v:=(scene.step j jN kj).choose_spec.choose
  obtain ⟨reproduces,readings⟩:=ports S scene j kj jN
  refine ⟨reproduces,?_⟩
  let A:=sceneIssue (N:=N) (RunFormalChain.fromRun R) S F v
  let H:=R.family.path.levels.params j;let H':=R.family.path.levels.params (j+1)
  let x:=R.family.path.levels.clock.hatBeta j;let y:=R.family.path.levels.clock.hatBeta (j+1)
  have ord:demand≤H.order:=(Nat.le_succ demand).trans (((R.makes.stages demand).2 j (menu.trans kj)).1)
  dsimp only [demand] at ord
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN hG (invoice.1 growth).sees
    (fun i=>invoice.2.1 _ _ (R.alloy.B.valid.pays i) _ (step_paid R.alloy.B.a i))
  have hb:A.S.patch.Branches A.S.kernel G:=season.bends.1
  have je:=kj.trans (Nat.le_succ j)
  have trend:=(scene.budget (j+1) jN je).1
  have wedge:=((budget N n kN).2 S scene).2.2 (j+1) je jN
  have gp:0<A.fClock:=inv_pos.mpr (Real.sqrt_pos.mpr ((half_pos
    (zero_lt_one.trans (R.family.path.levels.fits.delayed (j+1)))).trans_le (R.T.choice.represents N n (j+1) jN).band.1))
  have small:=unit (j+1) je N n jN
  change A.fClock^(1:ℝ) ≤ 1 at small
  rw [Real.rpow_one] at small
  have grow:=Real.rpow_le_rpow_of_exponent_ge gp small (sub_le_sub_left marg ((p:ℝ)+1))
  have height:tip G A.S.patch.L x=y:=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  change R.metals.O=chart G at frame
  intro b Z hz part
  let row:ReadingInputs H.order:=(⟨p,by omega⟩,⟨s,by omega⟩,⟨L,by omega⟩,⟨h,by omega⟩,part)
  let cost:=fun r:ReadingInputs H.order=>fluctuationGate J V cle hG H H' A.S.patch A.S.kernel
    r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
  have gate:cost row≤x:=(le_abs_self (cost row)).trans
    ((single_le_sum (fun i _=>abs_nonneg (cost i)) (mem_univ row)).trans (granted j (late.trans kj) n))
  change fluctuationGate J V cle hG H H' A.S.patch A.S.kernel p s L h part ≤ x at gate
  rw [fluctuationGate,dif_pos hb] at gate
  have y1 : 1 ≤ y := (R.family.path.levels.fits.delayed (j+1)).le
  have room0 : 0 ≤ Heath.Cottage.room y :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans y1) _) (Real.log_nonneg y1)) (Real.sqrt_nonneg _)
  have glob:‖A.fClock • Z‖ ≤ (H.order:ℝ)*Heath.Cottage.room y:=
    hz.trans (mul_le_mul_of_nonneg_right (hd.trans (Nat.cast_le.mpr (by omega : d≤H.order)))
      room0)
  have yy : 0 < tip G A.S.patch.L x := height.symm ▸ zero_lt_one.trans_le y1
  have band : Mosaic.lensT (tip G A.S.patch.L x) A.fClock := Mosaic.ever yy season.case_.beta season.case_.upper
  have room:=((eventually_atTop.mp (fluctuation_hull G hG A.S.patch.L (Nat.cast_nonneg H.order))).choose_spec x
    ((le_max_left ..).trans gate)) A.fClock band
  rw [height] at room
  have cap:‖Z‖ ≤ Mosaic.hull x:=by
    apply (mul_le_mul_iff_right₀ gp).mp
    simpa only [norm_smul, Real.norm_of_nonneg gp.le] using glob.trans room
  have use:=(eventually_atTop.mp (fluctuation_field_season J V cle (chart G) (chart_ok G) hG
    H H' A.S.patch A.S.kernel hb p s L part (Nat.cast_nonneg H.order)
    (margin_pos h) (sub_pos.mp (margin_fits p h)))).choose_spec x ((le_max_right ..).trans gate) A rfl rfl season
  dsimp only at use
  rw [height] at use
  have active:=readings b Z cap part
  have active':FieldPort A (chart G) V n₀ L J part y (y^Mosaic.pawn n₀) b Z :=
    (congrArg (fun χ=>FieldPort A χ V n₀ L J part y (y^Mosaic.pawn n₀) b Z) frame).mp active
  apply (congrArg (fun χ=>PhysicalFieldComparison J A χ y η p L part b Z) frame).mpr
  have requested:=use trend.bond trend.plane wedge b Z
    glob active'
  exact fun o ho=>(requested o ho).trans grow

end YM.Integration.WilsonConditionalTaylorFields
end

