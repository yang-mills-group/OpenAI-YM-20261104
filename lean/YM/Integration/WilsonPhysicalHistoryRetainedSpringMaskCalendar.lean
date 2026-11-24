import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskBoard
import YM.Integration.WilsonVacuumPreResetModelWidths
import YM.Integration.WilsonVacuumPreResetPrecursorIncome

/-! Uniformly before the cutoff and period, the original physical scale
and the same pre-elected positive width qualify the whole masked display. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Filter Finset Lattice RG Wilson Comparison.RG02 OPE.Therm
open Pert.Asymptotics WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonLimitConstruction
open AnalyticBridge VerifiedReset Collection Quotes IterationFour IterationFour.Vacuum
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato RG01Estimate
open WilsonVacuumPreResetModelBoard
open scoped Classical Topology BigOperators
variable {G:Gauge}

theorem cofinal_mask_source (R:Run G) (simple:G.Simple)
    (render:WilsonVacuumPreResetRenderCalendar.Issued R.kit)
    (curves:WilsonVacuumPreResetPrecursorReserve.Issued R.kit) :
    let V:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,let j:=m+1
      ∀N,j≤N→∀per (A:Listing G (R.family.side j per)),∀σ C:ℝ,0<σ→σ⁻¹≤zz V j→
      ∀Z:SeriesA G,Draw Z σ C→∀r t q:ℕ,∀U:Config G (R.family.side j per),
      let g:=regulatorRun R.family N per j
      let P:=R.family.path.rep N per j
      let D:=V.params j
      let p:=finitePitch R N j r g
      let γ:=g^2*pitchTail R N j r g
      let M:=source A P.p P.path D.clip D.width D.paths γ (γ+R.alloy.B.kin.alpha N j) σ C Z
        (fun grd rk=>(Integral.temperature g*p)*(g/Real.sqrt p)^(grd+2-rk)) t q
      HasSum (fun i=>masked P.p.threshold (M.listing.reg i).support (M.trunk i) U)
        (∑x:Site (R.family.side j per),maskedSpringAt R N per j r Z σ C g x U) := by
  intro V
  filter_upwards [(tendsto_add_atTop_nat 1).eventually (WilsonVacuumPreResetModelWidths.original
    R simple render curves),eventually_ge_atTop 20] with m widths beyond
  intro j N live per A σ C hs fund Z draw r t q U g P D p γ M
  have same:P.p=V.budget j:=(R.makes.wilson.represents N per j live).vac
  have decay:preExponent P.p/P.p.B≤σ/4:=by
    rw [same]
    exact widths.2.2 σ hs (fund.trans (WilsonVacuumPreResetPrecursorIncome.width V simple j))
  have blocks:2≤P.p.B:=by rw [same];exact le_trans (by norm_num:2≤4) widths.1
  have base:j≤(R.family.S.denominator j).val:=R.family.S.den_strict.id_le j
  have large:(R.family.S.denominator j).val≤(R.family.S.period per).val*(R.family.S.denominator j).val:=
    Nat.le_mul_of_pos_left _ (R.family.S.period per).property
  have fits:20<(R.family.side j per).val:=by
    change 20<(R.family.S.period per).val*(R.family.S.denominator j).val
    exact (show 20<j from Nat.lt_succ_of_le beyond).trans_le (base.trans large)
  exact spring_mask_source R simple N per j r live fits A Z draw hs decay blocks g t q U

end YM.Integration.OriginalMarkedRunAction
