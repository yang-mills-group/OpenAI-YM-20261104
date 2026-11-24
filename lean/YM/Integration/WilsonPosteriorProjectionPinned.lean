import YM.Integration.FVA1Physical.Sources.Round2.FieldReadingOn
import YM.Integration.FVA1Physical.Round2.PinnedFieldEmissions

/-! The two original physical field and emission readers with their finite law
ports supplied on the realized history. A coded census is charged at every
stage after its own finite booking; its earlier stages need no invoice.
The proofs retain the original comparisons, physical budgets and torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPosteriorProjectionPinned
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
open Function Filter Finset Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open MSbar.Midpoint MSbar.Cacao MSbar.CrossH MSbar.Bakery.Film MSbar.Whisk MSbar.Rolling MSbar.Kelvin MSbar.Lis MSbar.Bulk
open MSbar.Mosaic
open YM.Integration.FVA1Physical.Round2.Curvature
variable {G : Gauge} {ι : Type} [Fintype ι] (J : ι → Lamp G)

abbrev Late (R : PhysicalNext.Repeat.Legato.Run G) (f : StageThreshold) :=
  ∀ᶠ j : ℕ in atTop, ∀ n, f (R.family.path.levels.params j) (R.family.path.levels.params (j+1))
    (R.family.path.levels.clock.op j n).patch (R.family.path.levels.clock.op j n).kernel ≤
      R.family.path.levels.clock.hatBeta j

theorem readings (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G)
    (u:G.ColorIndex) (V:Voice G) (cle:Clear G V) (frame : R.metals.O=chart G)
    (threshold : Late R (readingMenu J V cle hG))
    (allPorts : PinnedPorts J R u V)
    (invoice:Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    PinnedReadings J R u := by
  obtain ⟨docket,_⟩:=docket_of_invoice hG R u V invoice
  obtain ⟨level,funds⟩ := eventually_atTop.mp threshold
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
  have grows:=Multi.Wage.hat_tend hG R.family.path.levels
  obtain ⟨k₀,big⟩:=eventually_atTop.mp ((Alto.broad.comp grows).eventually_ge_atTop (8*D))
  filter_upwards [allPorts n₀ s (n₀+4) L hs (by omega) (by omega),
    docket.purse s n₀ (n₀+4) hs (by omega) (by omega),eventually_ge_atTop (R.t demand),
    eventually_ge_atTop k₀,actual_clock_small R.family.path (q:=1) zero_lt_one zero_lt_one hG R.T.choice,eventually_ge_atTop level]
    with k loc budget menu large unit late N n kN
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
  have bg:=big j (large.trans kj)
  change 8*D≤Mosaic.hatW x at bg
  have room : D≤Mosaic.hull x := by unfold Mosaic.hull Mosaic.vol;linarith only [bg]
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
  let cost:=fun r:ReadingInputs H.order=>readingGate J V cle hG H H' A.S.patch A.S.kernel
    r.1 r.2.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2
  have gate:cost row≤x:=(le_abs_self (cost row)).trans
    ((single_le_sum (fun i _=>abs_nonneg (cost i)) (mem_univ row)).trans (funds j (late.trans kj) n))
  change readingGate J V cle hG H H' A.S.patch A.S.kernel p s L h part ≤ x at gate
  rw [readingGate,dif_pos hb] at gate
  have use:=(eventually_atTop.mp (inherited_field_season J V cle (chart G) (chart_ok G) hG
    H H' A.S.patch A.S.kernel hb p s L part (Nat.cast_nonneg H.order)
    (margin_pos h) (sub_pos.mp (margin_fits p h)))).choose_spec x gate A rfl rfl season
  dsimp only at use
  rw [height] at use
  have active:=readings b Z (hz.trans room) part
  have active':FieldPort A (chart G) V n₀ L J part y (y^Mosaic.pawn n₀) b Z :=
    (congrArg (fun χ=>FieldPort A χ V n₀ L J part y (y^Mosaic.pawn n₀) b Z) frame).mp active
  apply (congrArg (fun χ=>PhysicalFieldComparison J A χ y η p L part b Z) frame).mpr
  have requested:=use trend.bond trend.plane wedge b Z
    (hz.trans (hd.trans (Nat.cast_le.mpr (by omega : d≤H.order)))) active'
  exact fun o ho=>(requested o ho).trans grow


theorem emissions (hG:G.Simple) (R:PhysicalNext.Repeat.Legato.Run G) (u:G.ColorIndex)
    (V:Voice G) (cle:Clear G V) (frame:R.metals.O=chart G)
    (rows : Late R (emissionMenu J V cle hG R.metals.K))
    (invoice:Qlocal.Schedule.vacuumInvoice u V R.metals R.rolls R.alloy R.kit) :
    PinnedEmissions J R u := by
  obtain ⟨docket,_⟩:=docket_of_invoice hG R u V invoice
  have growth:Tendsto (fun j=>(R.alloy.B.a.params j).order) atTop atTop:=by
    apply tendsto_atTop.2;intro i
    filter_upwards [eventually_ge_atTop (R.t i)] with j hj
    exact (Nat.le_succ i).trans (((R.makes.stages i).2 j hj).1)
  have ch:=(R.bought R.T R.tuning.receipts R.t R.accepts R.stories R.doors R.makes R.carries R.books).1
  obtain ⟨level,funds⟩ := eventually_atTop.mp rows
  intro p r s q L pr hs D η hD hη
  obtain ⟨d,hd⟩:=exists_nat_ge D
  obtain ⟨h,marg⟩:=margin_eventually hη
  let demand:=d+p+s+q+L+h
  filter_upwards [docket.purse s r (r+4) hs (by omega) (by omega),eventually_ge_atTop (R.t demand),eventually_ge_atTop level] with k budget menu late N n kN
  obtain ⟨existsScene,paid⟩:=budget N n kN
  refine ⟨existsScene,?_⟩
  intro S scene j kj jN F v A x y
  let Z:=RunFormalChain.fromRun R
  let H:=R.family.path.levels.params j
  have ord:demand ≤ H.order:=(Nat.le_succ demand).trans (((R.makes.stages demand).2 j (menu.trans kj)).1)
  dsimp only [demand] at ord
  have season:=auditorium R.b R.Q R.T R.t R.stories R.doors ch V N n j jN hG (invoice.1 growth).sees
    (fun i=>invoice.2.1 _ _ (R.alloy.B.valid.pays i) _ (step_paid R.alloy.B.a i))
  have je:=kj.trans (Nat.le_succ j)
  have tr:=(scene.budget (j+1) jN je).1
  have wedge:=(paid S scene).2.2 (j+1) je jN
  have height:tip G A.S.patch.L x=y:=(Extra.Iteration.block_beta (a:=R.family.path.levels) j).symm
  have land:=emission_bought J V cle hG R.metals.K H (R.family.path.levels.params (j+1)) (A:=A)
  have branch:=season.bends.1
  have prem:Premier (main A.f A.pre.clip A.pre.path):=by
    change Premier (main _ (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path)
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN];exact tr.quiet
  have crit:Critical A.F A.pre.clip A.pre.path A.ρ:=by
    change Critical F (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path _
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN];exact (Z.planned.critical N j n jN F).1
  have pd:(mold A.pre A.F A.v).PosDef:=by
    change (Push.Uniform.block (priced F v (R.family.path.rep N n (j+1)).clip (R.family.path.rep N n (j+1)).path) 0).PosDef
    rw [Z.clips N n (j+1) jN,Z.selected N n (j+1) jN]
    exact blueprint F v (Z.kin.path N (j+1)) _ branch tr.quiet (Z.post.price _) (Z.planned.gap N j n jN F)
  intro b z hz o near part i hi
  have use:=land p s q L h part (by omega) (by omega) (by omega) (by omega) (by omega) (x:=x) (funds j (late.trans kj) n) season
  dsimp only at use
  rw [height] at use
  have plane:Expanse A.T 1 p:=⟨fun a ha=>tr.plane.profile a (ha.trans pr)⟩
  have pieces:Alto.Wedge A.T Alto.Dean (Mosaic.hatW y) (Alto.cWidth y) s p:=⟨fun a ha=>wedge.shares a (ha.trans pr)⟩
  have result:=use tr.bond plane pieces prem crit pd (fun ha small=>selected_land R jN S F v s ha small)
    b z (hz.trans (hd.trans (Nat.cast_le.mpr (by omega : d ≤ H.order)))) o near i hi
  change R.metals.O=chart G at frame
  rw [frame]
  exact Quote.widen result (Real.rpow_le_rpow_of_exponent_le (R.family.path.levels.fits.delayed j).le marg) le_rfl


end YM.Integration.WilsonPosteriorProjectionPinned

