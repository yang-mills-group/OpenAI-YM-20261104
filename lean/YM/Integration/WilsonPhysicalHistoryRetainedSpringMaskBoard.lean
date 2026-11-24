import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskEntries
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskComplete
import YM.Integration.WilsonVacuumPreResetModelBoard

/-! On each configuration the masked physical site sum is the numerical sum
of the original two-path kinetic and full previously filed source display. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Comparison.RG02 OPE.Therm IterationFour PhysicalNext.Repeat.Legato
open Function Finset Lattice RG Wilson PhysicalNext PhysicalNext.Repeat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonLimitConstruction
open AnalyticBridge VerifiedReset Collection Quotes IterationFour.Vacuum RG01Estimate
open WilsonVacuumPreResetPeriodEntries WilsonVacuumPreResetModelBoard
open scoped Classical Topology BigOperators
variable {G:Gauge} {n:Side}

theorem spring_mask_board (simple:G.Simple) (hn:20<n.val) (A:Listing G n) (B:BudgetPoint)
    (K:PathData G) (c:Clip) {u D Λ σ C:ℝ} (sale:K.Bounds c u D Λ)
    (hs:0<σ) (reach:preExponent B/B.B≤σ/4) (blocks:2≤B.B)
    (γ η ρ z:ℝ) (Z:SeriesA G) (draw:Draw Z σ C) (t q:ℕ) (U:Config G n) :
    let M:=source A B K c u D γ η σ C Z (fun grd rk=>ρ*z^(grd+2-rk)) t q
    HasSum (fun i=>masked B.threshold (M.listing.reg i).support (M.trunk i) U)
      (∑x:Site n,(γ*maskedSecondAt K c B x U+
       η*(maskedSitePacket K.cubic B x U+maskedSitePacket K.quartic B x U)+
       ρ*maskedPacketsAt Z B σ C B.threshold z x U)) := by
  intro M
  rw [sum_add_distrib,sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,sum_add_distrib,
    spring_mask_second K c sale B U,spring_mask_interaction,spring_mask_interaction,
    spring_mask_entries simple hn B hs reach blocks Z draw ρ z U]
  exact WilsonVacuumPreResetModelBoard.measured simple hn A B K c sale hs reach blocks γ η Z draw _ t q U

theorem spring_mask_source (R:Run G) (simple:G.Simple) (N per j r:ℕ) (live:j≤N)
    (hn:20<(R.family.side j per).val) (A:Listing G (R.family.side j per))
    (Z:SeriesA G) {σ C:ℝ} (draw:Draw Z σ C) (hs:0<σ)
    (reach:preExponent (R.family.path.rep N per j).p/(R.family.path.rep N per j).p.B≤σ/4)
    (blocks:2≤(R.family.path.rep N per j).p.B) (g:ℝ) (t q:ℕ) (U:Config G (R.family.side j per)) :
    let P:=R.family.path.rep N per j
    let D:=R.family.path.levels.params j
    let p:=finitePitch R N j r g
    let γ:=g^2*pitchTail R N j r g
    let η:=γ+R.alloy.B.kin.alpha N j
    let M:=source A P.p P.path D.clip D.width D.paths γ η σ C Z
      (fun grd rk=>(Integral.temperature g*p)*(g/Real.sqrt p)^(grd+2-rk)) t q
    HasSum (fun i=>masked P.p.threshold (M.listing.reg i).support (M.trunk i) U)
      (∑x:Site (R.family.side j per),maskedSpringAt R N per j r Z σ C g x U) := by
  intro P D p γ η M
  have rep : R.family.path.Conv N per j:=R.makes.wilson.represents N per j live
  have sale:P.path.Bounds D.clip D.width D.paths (R.family.path.levels.clock.loopCap j):=by
    dsimp only [P,D];rw [←rep.clip];exact rep.good.paths
  exact spring_mask_board simple hn A P.p P.path D.clip sale hs reach blocks
    γ η (Integral.temperature g*p) (g/Real.sqrt p) Z draw t q U

end YM.Integration.OriginalMarkedRunAction
