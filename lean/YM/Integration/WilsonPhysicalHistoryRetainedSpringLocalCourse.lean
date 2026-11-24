import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalBoard
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskCalendar
import YM.Integration.OriginalMarkedLocalPurchase

/-! The actual earlier regulated action and complete independent masked spring
on a common exterior. The spatial expenditure is independent of the period. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Finset Lattice RG Wilson WilsonStartup WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic IterationFour.Vacuum PhysicalNext PhysicalNext.Repeat
open PhysicalNext.Repeat.Legato RG01Estimate Pert.Asymptotics LocalComparison.Global
open Comparison.RG02 OPE.Therm WilsonCoeffUV.Bank.Ticket WilsonLimitConstruction
open AnalyticBridge VerifiedReset Collection Quotes IterationFour WilsonVacuumPreResetModelBoard
open scoped Classical Topology BigOperators
variable {G:Gauge}

def maskedSpringScore (R:Run G) (N per j r:ℕ) (Z:SeriesA G) (σ C:ℝ)
    (U:Config G (R.family.side j per)):ℝ :=
  let P:=R.family.path.rep N per j
  P.activities.additive P.p U-
    ∑x:Site (R.family.side j per),maskedSpringAt R N per j r Z σ C (regulatorRun R.family N per j) x U

def maskedSpringModel (R:Run G) (N per j r:ℕ) (Z:SeriesA G) (σ C:ℝ)
    (A:Listing G (R.family.side j per)) (t:ℕ):Precise.Leads G (R.family.side j per):=
  let P:=R.family.path.rep N per j
  let D:=R.family.path.levels.params j
  let g:=regulatorRun R.family N per j
  let p:=finitePitch R N j r g
  let γ:=g^2*pitchTail R N j r g
  source A P.p P.path D.clip D.width D.paths γ (γ+R.alloy.B.kin.alpha N j) σ C Z
    (fun grd rk=>(Integral.temperature g*p)*(g/Real.sqrt p)^(grd+2-rk)) t P.p.B

theorem cofinal_spring_change (R:Run G) (simple:G.Simple)
    (render:WilsonVacuumPreResetRenderCalendar.Issued R.kit)
    (curves:WilsonVacuumPreResetPrecursorReserve.Issued R.kit):
    let V:=R.family.path.levels
    ∀ᶠm:ℕ in atTop,let j:=m+1
      ∀N,j<N→∀per (A:Listing G (R.family.side j per)),∀σ C:ℝ,0<σ→σ⁻¹≤zz V j→
      ∀Z:SeriesA G,Draw Z σ C→∀r:ℕ,∀ᶠt:ℕ in atTop,
      let P:=R.family.path.rep N per j
      let M:=maskedSpringModel R N per j r Z σ C A t
      M.listing.hard=A.hard ∧ Meadow.Budget P.p M.listing.reg M.trunk M.bill ∧
      ∀S U W,OriginalMarkedLocalDifference.Outside S U W→
        |maskedSpringScore R N per j r Z σ C U-maskedSpringScore R N per j r Z σ C W|≤
          OriginalMarkedLocalPurchase.fee V j S (V.clock.allowance j+M.bill):=by
  intro V
  filter_upwards [(tendsto_add_atTop_nat 1).eventually
    (WilsonVacuumPreResetModelWidths.original R simple render curves),eventually_ge_atTop 20] with m widths late
  intro j N live per A σ C hs fund Z draw r
  let P:=R.family.path.rep N per j
  let D:=V.params j
  let g:=regulatorRun R.family N per j
  let p:=finitePitch R N j r g
  let γ:=g^2*pitchTail R N j r g
  have rep:R.family.path.Conv N per j:=R.makes.wilson.represents N per j live.le
  have same:P.p=V.budget j:=rep.vac
  have room:4≤P.p.B:=by rw [same];exact widths.1
  have hw:preExponent P.p/P.p.B≤D.width/4:=by rw [same];exact widths.2.1
  have hz:preExponent P.p/P.p.B≤σ/4:=by
    rw [same];exact widths.2.2 σ hs (fund.trans (WilsonVacuumPreResetPrecursorIncome.width V simple j))
  have base:j≤(R.family.S.denominator j).val:=R.family.S.den_strict.id_le j
  have large:(R.family.S.denominator j).val≤(R.family.S.period per).val*(R.family.S.denominator j).val:=
    Nat.le_mul_of_pos_left _ (R.family.S.period per).property
  have hn:20<(R.family.side j per).val:=by
    exact (show 20<j from Nat.lt_succ_of_le late).trans_le (base.trans large)
  have k:P.path.Bounds D.clip D.width D.paths (V.clock.loopCap j):=by
    change P.path.Bounds (R.family.path.levels.params j).clip _ _ _;rw [←rep.clip];exact rep.good.paths
  have clip:Decent D.clip P.p:=by rw [same];exact CensusStep.decent R.kit (N:=N) live
  have billed:=WilsonVacuumPreResetModelBoard.original simple hn A P.p P.path D.clip k clip hw hs hz
    (le_trans (by norm_num:2≤4) room) γ (γ+R.alloy.B.kin.alpha N j) Z draw
    (fun grd rk=>(Integral.temperature g*p)*(g/Real.sqrt p)^(grd+2-rk)) P.p.B room (η:=1) zero_lt_one
  filter_upwards [billed] with t bought
  intro Y M
  refine ⟨bought.1,bought.2.2.1.live,?_⟩
  intro S U W outside
  have radial:1≤P.p.supportExponent*OriginalMarkedLocalPurchase.width V:=by
    rw [same];exact OriginalMarkedLocalPurchase.width_pays V j
  have change:=numbered_change P rep.good.labels M bought.2.2.1.live _
    (spring_mask_source R simple N per j r live.le hn A Z draw hs hz
      (le_trans (by norm_num:2≤4) room) g t P.p.B) _ radial S U W outside
  simpa only [maskedSpringScore,OriginalMarkedLocalPurchase.fee,←same] using change.2.2

end YM.Integration.OriginalMarkedRunAction
