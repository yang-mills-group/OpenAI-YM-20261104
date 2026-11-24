import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskPayload
import YM.Integration.WilsonPhysicalHistoryRetainedSpringMaskRoster

/-! The complete previously filed finite list of signed original period
packets on the torus, with every mask applied before the spatial sum. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Function Finset Lattice RG Wilson PhysicalNext PhysicalNext.Repeat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonLimitConstruction
open AnalyticBridge VerifiedReset Collection Quotes IterationFour.Vacuum
open WilsonVacuumPreResetPeriodEntries
open scoped Classical Topology BigOperators
variable {G:Gauge} {n:Side}

theorem spring_mask_list (B:BudgetPoint) (σ C ρ c:ℝ) (U:Config G n) (Z:SeriesA G)
    (paid:Render.permits (Z.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)) (Song.headline B)) :
    ∑x:Site n,ρ*maskedPacketsAt Z B σ C B.threshold c x U=
      Render.renders (fun a=>ρ*c^(a.power+2-a.rank)) B U
        (Z.map (FundedCorrectedPeriod.piece n (Song.headline B) σ C)) := by
  let Q:PrismA G→Piece G n:=FundedCorrectedPeriod.piece n (Song.headline B) σ C
  induction Z with
  | nil=>simp [maskedPacketsAt,Render.renders]
  | cons a Z ih=>
    have head:(Q a).packet.Invoice (Song.headline B) (Q a).credit:=paid (Q a) (List.mem_cons_self ..)
    have tail:=ih (fun s h=>paid s (List.mem_cons_of_mem _ h))
    have one:=mask_packet_sites B σ C a head U
    change (∑x:Site n,ρ*(c^(a.grade-a.rise)*maskedPrismAt a B σ C B.threshold x U+
      maskedPacketsAt Z B σ C B.threshold c x U))=
      ρ*c^(a.grade+2-(a.rise+2))*(Q a).packet.amount B U+
        Render.renders (fun a=>ρ*c^(a.power+2-a.rank)) B U (Z.map Q)
    simp_rw [mul_add,←mul_assoc]
    rw [sum_add_distrib,←Finset.mul_sum,one,tail,Nat.add_sub_add_right]

theorem spring_mask_entries (simple:G.Simple) (hn:20<n.val) (B:BudgetPoint) {σ C:ℝ}
    (hs:0<σ) (reach:preExponent B/B.B≤σ/4) (blocks:2≤B.B)
    (Z:SeriesA G) (draw:Draw Z σ C) (ρ c:ℝ) (U:Config G n) :
    ∑x:Site n,ρ*maskedPacketsAt Z B σ C B.threshold c x U=
      (entries n B σ C Z (fun grd rk=>ρ*c^(grd+2-rk))).additive B U := by
  have paid:=FundedCorrectedPeriod.permits Z draw simple hn (Song.headline B) hs reach blocks
    (Pane.pale n G) (fun s b=>((Pane.whey n G (Song.headline B)).moves s b).some)
  exact (spring_mask_list B σ C ρ c U Z paid).trans
    (WilsonVacuumPreResetPeriodField.maskedRows simple hn B hs reach blocks Z draw (fun d h=>ρ*c^(d+2-h)) U).symm

end YM.Integration.OriginalMarkedRunAction
